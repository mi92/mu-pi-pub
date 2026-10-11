#!/usr/bin/env python3
"""
Recompute the numbers printed in paper/K2H_paper_v3.tex (mu(pi) <= 6.0446, triple (5,3,4)).

Written for the audit of version 2 of the paper (2026-10-03; see paper/AUDIT_K2H_paper_v2.md), independently of
the programs that produced the numbers in the text.  Version 3 is version 2 with the corrections of that audit; the
two numbers of version 2 that were wrong (3.70615, "level 14n attained for n <= 6") are checked here in corrected form.  Every check prints PASS/FAIL; the exit status is non-zero if a check fails.

    python scripts/paper_v3_numbers.py            # everything (about 15 seconds)
    python scripts/paper_v3_numbers.py --fast     # skips n <= 300 and the sieve up to 4*10^7

Exact arithmetic: rationals (gmpy2.mpq if available), Q(sqrt 2) and Q(sqrt 2, i) as pairs.
Numerics: mpmath.  Polynomial powers: python-flint if available, pure Python otherwise.

Methods for the linear forms J_n = u_n + v_n*pi:
  M0  the recursion of Section 4.2, literally: G = sum_j p_j [ xi_j * (primitive of the Laurent polynomial W^j/z)
                 - sum_{m'} mu_{j,2n,m'} W^{j+1} Y^{-(2m'+1)} ],  u_n = -i (G(1+i) - G(1-i))        (Prop. 4.6)
  M1  moments:   J_n = sum_j a_j M_j,  A_n(W) = sum_j a_j W^j = sum_j p_j xi_{j,2n} W^j,
                 M_j = int_{-pi/4}^{pi/4} (2 sqrt2 cos phi)^j dphi = U_j + V_j pi   (Remark 4.9, App. A.1)
  M2  partial fractions of h_n over Q(sqrt 2), integrated term by term           (Section 5.2)
  M3  the coordinate w, atoms and their data over Q(sqrt 2)                      (Section 5.4)
  M4  numerical quadrature of the integral itself
  M5  c_n as a power-series coefficient                                          (Lemma 6.1)
"""
import os
import re
import sys
import time
from math import comb, factorial, gcd

import mpmath as mp

try:
    from gmpy2 import mpq as Fr
    HAVE_GMPY = True
except Exception:  # pragma: no cover
    from fractions import Fraction as Fr
    HAVE_GMPY = False

try:
    from flint import fmpz_poly
    HAVE_FLINT = True
except Exception:  # pragma: no cover
    HAVE_FLINT = False

FAST = "--fast" in sys.argv
RESULTS = []
T0 = time.time()


def check(name, cond, detail=""):
    RESULTS.append((name, bool(cond)))
    print(("PASS  " if cond else "FAIL  ") + name + (("   [" + str(detail) + "]") if detail else ""), flush=True)


def section(title):
    print("\n== " + title + "  (t=%.1fs) ==" % (time.time() - T0), flush=True)


def trunc_eq(x, s):
    """True if the decimal expansion of x starts with the digits of the string s: the convention of the paper for
    numbers printed with dots, as in '0.2939598992...' (strict truncation, no rounding)."""
    s = s.strip()
    neg = s.startswith("-")
    body = s.lstrip("-")
    nd = len(body.split(".")[1]) if "." in body else 0
    val = mp.mpf(body)
    ax = -mp.mpf(x) if neg else mp.mpf(x)
    return val <= ax < val + mp.mpf(10) ** (-nd)


def round_eq(x, s):
    """True if x rounded to the number of decimals of s equals s."""
    s = s.strip()
    nd = len(s.split(".")[1]) if "." in s else 0
    return abs(mp.mpf(x) - mp.mpf(s)) <= mp.mpf(10) ** (-nd) * mp.mpf("0.5000001")


def numer(q):
    return int(q.numerator)


def denom(q):
    return int(q.denominator)


def v2int(m):
    m = abs(int(m))
    return (m & -m).bit_length() - 1 if m else 10 ** 9


def v2q(q):
    return v2int(numer(q)) - v2int(denom(q))


# ------------------------------------------------------------------ Q(sqrt 2) and Q(sqrt 2, i)
class Q2:
    __slots__ = ("a", "b")

    def __init__(self, a=0, b=0):
        self.a = Fr(a)
        self.b = Fr(b)

    @staticmethod
    def c(o):
        return o if isinstance(o, Q2) else Q2(o, 0)

    def __add__(self, o):
        o = Q2.c(o)
        return Q2(self.a + o.a, self.b + o.b)

    __radd__ = __add__

    def __neg__(self):
        return Q2(-self.a, -self.b)

    def __sub__(self, o):
        o = Q2.c(o)
        return Q2(self.a - o.a, self.b - o.b)

    def __rsub__(self, o):
        return Q2.c(o) - self

    def __mul__(self, o):
        o = Q2.c(o)
        return Q2(self.a * o.a + 2 * self.b * o.b, self.a * o.b + self.b * o.a)

    __rmul__ = __mul__

    def norm(self):
        return self.a * self.a - 2 * self.b * self.b

    def inv(self):
        n = self.norm()
        return Q2(self.a / n, -self.b / n)

    def __truediv__(self, o):
        return self * Q2.c(o).inv()

    def __rtruediv__(self, o):
        return Q2.c(o) * self.inv()

    def __pow__(self, k):
        if k < 0:
            return self.inv() ** (-k)
        r, base = Q2(1), self
        while k:
            if k & 1:
                r = r * base
            base = base * base
            k >>= 1
        return r

    def __eq__(self, o):
        o = Q2.c(o)
        return self.a == o.a and self.b == o.b

    def is_zero(self):
        return self.a == 0 and self.b == 0

    def conj(self):
        return Q2(self.a, -self.b)

    def level(self):
        """exponent of sqrt2 in the element (v_2 of the norm); +inf for 0"""
        return 10 ** 9 if self.is_zero() else v2q(self.norm())

    def mp(self):
        return mp.mpf(numer(self.a)) / denom(self.a) + (mp.mpf(numer(self.b)) / denom(self.b)) * mp.sqrt(2)

    def __repr__(self):
        return "(%s + %s*sqrt2)" % (self.a, self.b)


SQ = Q2(0, 1)
EPS = Q2(-1, 1)          # sqrt2 - 1
KAP = Q2(1) + EPS * EPS  # 1 + eps^2


class Q2i:
    """x + i y with x, y in Q(sqrt 2)"""
    __slots__ = ("re", "im")

    def __init__(self, re=0, im=0):
        self.re = Q2.c(re)
        self.im = Q2.c(im)

    @staticmethod
    def c(o):
        return o if isinstance(o, Q2i) else Q2i(o, 0)

    def __add__(self, o):
        o = Q2i.c(o)
        return Q2i(self.re + o.re, self.im + o.im)

    __radd__ = __add__

    def __sub__(self, o):
        o = Q2i.c(o)
        return Q2i(self.re - o.re, self.im - o.im)

    def __neg__(self):
        return Q2i(-self.re, -self.im)

    def __mul__(self, o):
        o = Q2i.c(o)
        return Q2i(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    __rmul__ = __mul__

    def inv(self):
        n = self.re * self.re + self.im * self.im
        return Q2i(self.re / n, -self.im / n)

    def __pow__(self, k):
        if k < 0:
            return self.inv() ** (-k)
        r, base = Q2i(1), self
        while k:
            if k & 1:
                r = r * base
            base = base * base
            k >>= 1
        return r


# ------------------------------------------------------------------ polynomials (lists, low degree first)
def pmul(p, q, zero=0):
    if not p or not q:
        return []
    r = [zero] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a == 0:
            continue
        for j, b in enumerate(q):
            r[i + j] = r[i + j] + a * b
    return r


def ppow(p, k, one=1):
    r = [one]
    for _ in range(k):
        r = pmul(r, p)
    return r


def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def psub(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) - (q[i] if i < len(q) else 0) for i in range(n)]


def pscale(p, c):
    return [c * a for a in p]


def pderiv(p):
    return [i * p[i] for i in range(1, len(p))]


def pdivmod(num, den):
    """quotient and remainder (exact rational arithmetic)"""
    num = [Fr(x) for x in num]
    den = [Fr(x) for x in den]
    while den and den[-1] == 0:
        den.pop()
    q = [Fr(0)] * max(0, len(num) - len(den) + 1)
    r = num[:]
    for i in range(len(num) - len(den), -1, -1):
        c = r[i + len(den) - 1] / den[-1]
        q[i] = c
        if c != 0:
            for j, d in enumerate(den):
                r[i + j] -= c * d
    return q, r[: len(den) - 1]


def peval(p, x):
    r = 0
    for c in reversed(p):
        r = r * x + c
    return r


def pcompose_affine(p, t0, ell):
    """coefficients of p(t0 + ell*s) in s"""
    r = []
    for c in reversed(p):
        r = padd(pmul(r, [t0, ell]), [c])
    return r


def int_poly_power_WY(n):
    """integer coefficients p_j of P_n(W) = ((W-3)^5 (W-2)^3)^n"""
    if HAVE_FLINT:
        P = fmpz_poly([-3, 1]) ** (5 * n) * fmpz_poly([-2, 1]) ** (3 * n)
        return [int(c) for c in P.coeffs()]
    a = [comb(5 * n, k) * (-3) ** (5 * n - k) for k in range(5 * n + 1)]
    b = [comb(3 * n, k) * (-2) ** (3 * n - k) for k in range(3 * n + 1)]
    return pmul(a, b)


# ------------------------------------------------------------------ the functions f, h_n
def f_mp(z):
    return ((z - 1) * (z - 2)) ** 5 * (z * z - 2 * z + 2) ** 3 / (z ** 4 * (z * z - 2) ** 4)


def f_gen(z, e1, e2, d):
    a = e1 + e2 - d
    return ((z - 1) * (z - 2)) ** e1 * (z * z - 2 * z + 2) ** e2 / (z ** a * (z * z - 2) ** d)


N_INT = pmul(ppow(pmul([-1, 1], [-2, 1]), 5), ppow([2, -2, 1], 3))  # N(z), degree 16


# ------------------------------------------------------------------ primes, D_n, Phi_n
def primes_upto(m):
    s = bytearray([1]) * (m + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(m ** 0.5) + 1):
        if s[i]:
            s[i * i :: i] = bytearray(len(s[i * i :: i]))
    return [i for i in range(m + 1) if s[i]]


def removable(n, p):
    return p * p > 4 * n and (4 * n // p) % 2 == 0 and (5 * n) % p + (3 * n) % p < (4 * n) % p


def lcm_upto(m):
    r = 1
    for p in primes_upto(m):
        q = p
        while q * p <= m:
            q *= p
        r *= q
    return r


def Phi(n):
    r = 1
    for p in primes_upto(4 * n):
        if removable(n, p):
            r *= p
    return r


def Dmult(n):
    return lcm_upto(4 * n) // Phi(n)


# ------------------------------------------------------------------ M1: moments
_UV = [(Fr(0), Fr(1, 2)), (Fr(4), Fr(0))]


def UV(j):
    """M_j = int_{-pi/4}^{pi/4} (2 sqrt2 cos phi)^j dphi = U_j + V_j pi;  M_j = 2^{j+1}/j + 8 (j-1)/j M_{j-2}"""
    while len(_UV) <= j:
        k = len(_UV)
        u, v = _UV[k - 2]
        c = Fr(8 * (k - 1), k)
        _UV.append((Fr(2 ** (k + 1), k) + c * u, c * v))
    return _UV[j]


def xi_list(jmax, m):
    """xi_{j,m} = prod_{i<m} (j-2i)/(8(2i+1)) for j = 0..jmax"""
    den = Fr(1)
    for i in range(m):
        den *= 8 * (2 * i + 1)
    out = []
    for j in range(jmax + 1):
        if j % 2 == 0 and j < 2 * m:
            out.append(Fr(0))
            continue
        if j >= 2 and out[j - 2] != 0 and (j - 2 * m) != 0:
            # xi_{j,m} / xi_{j-2,m} = j / (j - 2m)
            out.append(out[j - 2] * Fr(j, j - 2 * m))
            continue
        num = 1
        for i in range(m):
            num *= j - 2 * i
        out.append(Fr(num) / den)
    return out


def forms_M1(n):
    p = int_poly_power_WY(n)
    xi = xi_list(8 * n, 2 * n)
    UV(8 * n)
    u = Fr(0)
    v = Fr(0)
    for j, pj in enumerate(p):
        if pj == 0 or xi[j] == 0:
            continue
        a = pj * xi[j]
        U, V = _UV[j]
        u += a * U
        v += a * V
    return u, v


def forms_M0(n):
    """the recursion (4.4)-(4.6) carried through; no use of the vanishing of E_n at the end points"""
    m = 2 * n
    p = int_poly_power_WY(n)
    xi = xi_list(8 * n, m)
    # Im (1+i)^l for l = -8n..8n :  (1+i)^(-l) = ((1-i)/2)^l
    re_, im_ = [1], [0]
    for l in range(8 * n):
        re_.append(re_[-1] - im_[-1])
        im_.append(re_[-2] + im_[-1])
    imag = lambda l: Fr(im_[l]) if l >= 0 else Fr(-im_[-l], 2 ** (-l))
    u = Fr(0)
    c = Fr(0)
    for j, pj in enumerate(p):
        if pj == 0:
            continue
        acc = Fr(0)
        if xi[j] != 0:
            t = Fr(0)
            for k in range(j + 1):
                l = j - 2 * k
                if l == 0:
                    c += pj * xi[j] * comb(j, k) * 2 ** k
                else:
                    t += Fr(comb(j, k) * 2 ** (k + 1)) * imag(l) / l
            acc += xi[j] * t
        # mu_{j,m,m'} = 1/(8(2m'+1)) * prod_{i=m'+1}^{m-1} (j-2i)/(8(2i+1)),  built from m' = m-1 downwards
        prod = Fr(1)
        for mp_ in range(m - 1, -1, -1):
            mu = prod / (8 * (2 * mp_ + 1))
            acc += mu * (-1) ** mp_ * Fr(2) ** (j + 1 - 2 * mp_)
            prod *= Fr(j - 2 * mp_, 8 * (2 * mp_ + 1))
        u += pj * acc
    return u, c / 2


def J_exact_mp(u, v):
    return mp.mpf(numer(u)) / denom(u) + (mp.mpf(numer(v)) / denom(v)) * mp.pi


# ------------------------------------------------------------------ M5: c_n as power-series coefficient
def c_series(n):
    """coefficient of z^{4n} in N(z)^n (z^2-2)^{-4n}"""
    top = 4 * n
    if HAVE_FLINT:
        Nn = fmpz_poly(N_INT) ** n
        co = [int(Nn[k]) for k in range(top + 1)]
    else:
        co = [1]
        for _ in range(n):
            co = pmul(co, N_INT)[: top + 1]
    # (z^2-2)^{-4n} = 2^{-4n} (1 - z^2/2)^{-4n} = sum_k C(4n+k-1,k) z^{2k} / 2^{4n+k}
    s = Fr(0)
    for k in range(0, 2 * n + 1):
        s += Fr(co[top - 2 * k] * comb(4 * n + k - 1, k), 2 ** (4 * n + k))
    return s


def c_closed(n):
    """Remark 4.9: c_n = sum_{l=2n}^{4n} p_{2l} 2^{l-2n} C(2l,l) C(l,2n) / C(4n,2n)"""
    p = int_poly_power_WY(n)
    s = Fr(0)
    for l in range(2 * n, 4 * n + 1):
        s += Fr(p[2 * l] * 2 ** (l - 2 * n) * comb(2 * l, l) * comb(l, 2 * n), comb(4 * n, 2 * n))
    return s


# ------------------------------------------------------------------ M2: partial fractions over Q(sqrt 2)
def series_mul(a, b, E):
    r = [Q2(0)] * E
    for i, x in enumerate(a[:E]):
        if x.is_zero():
            continue
        for j, y in enumerate(b[: E - i]):
            r[i + j] = r[i + j] + x * y
    return r


def series_pow_linear_inv(c, e, E):
    """(c + t)^(-e) mod t^E, c in Q(sqrt2)"""
    ci = Q2.c(c).inv()
    out = []
    for k in range(E):
        out.append((ci ** (e + k)) * ((-1) ** k * comb(e + k - 1, k)))
    return out


def partial_fractions(n):
    """h_n = N^n / (z^{4n+1} (z-sqrt2)^{4n} (z+sqrt2)^{4n}).
    Returns (T, PP): polynomial part T (rationals, low first) and PP[a] = {k: q_{a,k}} for a in (0, +s, -s)."""
    Nn = ppow(N_INT, n)
    den = pmul([0] * (4 * n + 1) + [1], ppow([-2, 0, 1], 4 * n))
    T, _ = pdivmod(Nn, den)
    poles = {"0": (Q2(0), 4 * n + 1), "+": (SQ, 4 * n), "-": (-SQ, 4 * n)}
    PP = {}
    for key, (a, e) in poles.items():
        # N(a+t) as a polynomial in t
        Na = []
        for c in reversed(N_INT):
            Na = padd(pmul(Na, [a, Q2(1)]), [Q2(c)])
        ser = [Q2(1)] + [Q2(0)] * (e - 1)
        Na = (Na + [Q2(0)] * e)[:e]
        for _ in range(n):
            ser = series_mul(ser, Na, e)
        for kb, (b, eb) in poles.items():
            if kb == key:
                continue
            ser = series_mul(ser, series_pow_linear_inv(a - b, eb, e), e)
        PP[key] = {k: ser[e - k] for k in range(1, e + 1)}
    return T, PP


def G_at(T, PP, zq):
    """the standard primitive (5.4) evaluated at zq in Q(sqrt2, i)"""
    val = Q2i(0)
    for j, t in enumerate(T):
        val = val + (zq ** (j + 1)) * Q2i(Q2(t) / (j + 1))
    polepos = {"0": Q2(0), "+": SQ, "-": -SQ}
    for key, coeffs in PP.items():
        w = (zq - Q2i(polepos[key])).inv()
        for k, q in coeffs.items():
            if k >= 2:
                val = val - (w ** (k - 1)) * Q2i(q / (k - 1))
    return val


def u_from_pf(T, PP):
    Gp = G_at(T, PP, Q2i(1, 1))
    Gm = G_at(T, PP, Q2i(1, -1))
    d = Gp - Gm                       # = i * u
    u = Q2i(0, -1) * d
    assert u.im.is_zero() and u.re.b == 0, "u_n not rational?"
    return u.re.a


# ------------------------------------------------------------------ M3: the coordinate w
def B_atom(m, a):
    """data U of x^a w^{-2m}:  2^{a+1} a! / (kappa^a prod_{j=0}^a (2j+1-2m))"""
    pr = 1
    for j in range(a + 1):
        pr *= 2 * j + 1 - 2 * m
    return (KAP ** (-a)) * Fr(2 ** (a + 1) * factorial(a), pr)


def alpha_beta(jmax):
    al = [Q2(0)]
    be = [Q2(1)]
    e2 = EPS * EPS
    for j in range(jmax):
        d = (e2 * (2 * (j + 1))).inv()
        al.append((al[j] * (2 * j + 1) + 2 * (KAP ** (-(j + 1)))) * d)
        be.append(be[j] * (2 * j + 1) * d)
    return al, be


def Y_data(m, kmax):
    """data (U,V) of w^{-2m} (w^2+eps^2)^{-k}, k = 1..kmax, by the recursions of App. A.5"""
    al, be = alpha_beta(kmax)
    cur = {k: (al[k - 1], be[k - 1]) for k in range(1, kmax + 1)}     # m = 0
    e2i = (EPS * EPS).inv()
    for mm in range(m):                                                # mm -> mm+1
        new = {}
        prev = (Q2(Fr(2, -2 * mm - 1)), Q2(0))                         # data of w^{-2(mm+1)}  (k = 0)
        for k in range(1, kmax + 1):
            U = (prev[0] - cur[k][0]) * e2i
            V = (prev[1] - cur[k][1]) * e2i
            new[k] = (U, V)
            prev = (U, V)
        cur = new
    return cur


def wframe(n, per_term=False):
    """data (U,V) of k_n; returns also the contributions of the terms i = 0..5n"""
    m = 2 * n
    Bc = {}

    def B(a):
        if a not in Bc:
            Bc[a] = B_atom(m, a)
        return Bc[a]

    Yd = Y_data(m, 4 * n + 1)
    pref = KAP ** (4 * n - 1)
    Utot, Vtot = Q2(0), Q2(0)
    terms = []
    for i in range(5 * n + 1):
        Ui, Vi = Q2(0), Q2(0)
        if i <= n - 1:
            for b in range(n - 1 - i + 1):
                Ui = Ui + B(3 * n + i + b) * (comb(n - 1 - i, b) * (-1) ** b)
        else:
            j = i - n + 1
            for l in range(3 * n + i + 1):
                cl = comb(3 * n + i, l) * (-1) ** l
                if l >= j:
                    for b in range(l - j + 1):
                        Ui = Ui + B(b) * (cl * comb(l - j, b) * (-1) ** b)
                else:
                    k = j - l
                    kk = KAP ** k
                    Ui = Ui + Yd[k][0] * kk * cl
                    Vi = Vi + Yd[k][1] * kk * cl
        coef = pref * ((2 * EPS) ** i) * comb(5 * n, i)
        Ui, Vi = Ui * coef, Vi * coef
        terms.append((Ui, Vi))
        Utot, Vtot = Utot + Ui, Vtot + Vi
    return (Utot, Vtot, terms) if per_term else (Utot, Vtot)


# ====================================================================================== checks
mp.mp.dps = 60

section("Section 1: introduction")
x = abs(mp.pi - mp.mpf(355) / 113)
check("|pi - 355/113| = 2.667...e-7", trunc_eq(x * 10 ** 7, "2.667"), mp.nstr(x, 8))
check("... = 113^(-3.20)", round_eq(-mp.log(x) / mp.log(113), "3.20"), mp.nstr(-mp.log(x) / mp.log(113), 6))
check("7345 = 65*113, 23075 = 65*355", 7345 == 65 * 113 and 23075 == 65 * 355)

TAB2 = {
    1: ("-23075/2", "7345/2", 12, 1),
    2: ("-4338189943/14", "197269821/2", 280, 3),
    3: ("-11065298371140502/1155", "6099036995857/2", 27720, 1),
    4: ("-14141220324520524847492/45045", "199857486158198941/2", 720720, 1),
    5: ("-173152818047406076172911685/16302", "3380950423572104245485", 33256080, 7),
    6: ("-743759148883149273178854708603850/2028117", "233463740039798755103513775/2", 1070845776, 5),
}
FORMS = {}
for n in range(1, 31):
    FORMS[n] = forms_M1(n)
ok = True
for n, (us, vs, D, Ph) in TAB2.items():
    u, v = FORMS[n]
    ok &= (u == Fr(us)) and (v == Fr(vs)) and Dmult(n) == D and Phi(n) == Ph
check("Table 2: u_n, v_n, D_n, Phi_n for n <= 6 (method M1)", ok)
check("Phi_1 = 1, Phi_2 = 3, Phi_21 = 17*29*31", Phi(1) == 1 and Phi(2) == 3 and Phi(21) == 17 * 29 * 31)
check("1155 = 3*5*7*11 | 27720;  16302 = 2*3*11*13*19 | 33256080 = lcm(1..20)/7",
      1155 == 3 * 5 * 7 * 11 and 27720 % 1155 == 0 and 16302 == 2 * 3 * 11 * 13 * 19 and 33256080 % 16302 == 0
      and lcm_upto(20) == 7 * 33256080)
u1, v1 = FORMS[1]
J1 = J_exact_mp(u1, v1)
check("J_1 = (7345 pi - 23075)/2 = -0.000979691...", trunc_eq(J1, "-0.000979691"), mp.nstr(J1, 12))
check("12 u_1 = -138450, 12 v_1 = 44070", 12 * u1 == -138450 and 12 * v1 == 44070)

section("Section 3/4: the integral, numerically (M4), and the recursion")


def J_quad(n):
    g = lambda t: f_mp(mp.mpc(1, t)) ** n / mp.mpc(1, t)
    val = mp.quad(g, mp.linspace(-1, 1, 9))
    return val


for n in (1, 2, 3):
    Jq = J_quad(n)
    Je = J_exact_mp(*FORMS[n])
    check("n=%d: quadrature agrees with u_n + v_n pi to 38 digits and is real" % n,
          abs(Jq.real - Je) < abs(Je) * mp.mpf(10) ** (-38) and abs(Jq.imag) < abs(Je) * mp.mpf(10) ** (-38),
          mp.nstr(Je, 6))
check("J_1 = -9.7969e-4, J_2 = 1.0455e-6, J_3 = -1.2241e-9",
      round_eq(J_exact_mp(*FORMS[1]) * 10 ** 4, "-9.7969") and round_eq(J_exact_mp(*FORMS[2]) * 10 ** 6, "1.0455")
      and round_eq(J_exact_mp(*FORMS[3]) * 10 ** 9, "-1.2241"))
p1 = int_poly_power_WY(1)
check("P_1(W) coefficients", p1 == [1944, -6156, 8478, -6633, 3225, -998, 192, -21, 1])
xi2 = xi_list(8, 2)
check("xi_{j,2} = j(j-2)/192", all(xi2[j] == Fr(j * (j - 2), 192) for j in range(9)))
terms = [p1[j] * xi2[j] * comb(j, j // 2) * 2 ** (j // 2) for j in (4, 6, 8)]
check("c_1 = 3225 + 3840 + 280 = 7345", terms == [3225, 3840, 280] and sum(terms) == 7345)
check("the recursion of Section 4.2 carried through (M0) gives the same (u_n, v_n) as the moment formula (M1), n <= 30",
      all(forms_M0(n) == FORMS[n] for n in range(1, 31)))
check("c_n: series coefficient (M5) = closed formula (Remark 4.9) = 2 v_n (M1), n <= 30",
      all(c_series(n) == c_closed(n) == 2 * FORMS[n][1] for n in range(1, 31)))
# appendix A.1
A1 = [p1[j] * xi2[j] for j in range(9)]
check("A.1: A(W) coefficients",
      A1 == [0, Fr(513, 16), 0, Fr(-6633, 64), Fr(1075, 8), Fr(-2495, 32), 24, Fr(-245, 64), Fr(1, 4)])
lam = {}
for l in range(0, 9):
    s = Fr(0)
    for j in range(l, 9):
        if (j - l) % 2 == 0:
            k = (j - l) // 2
            s += A1[j] * comb(j, k) * 2 ** k
    lam[l] = s
check("A.1: lambda_0..lambda_8",
      [lam[l] for l in range(9)] == [7345, Fr(-152973, 32), 2627, Fr(-77113, 64), Fr(3603, 8), Fr(-2105, 16), 28,
                                     Fr(-245, 64), Fr(1, 4)])
im = [0, 1, 2, 2, 0, -4, -8, -8, 0]
six = [lam[l] / l * im[l] for l in (1, 2, 3, 5, 6, 7)]
check("A.1: six terms and u_1 = 4 * (-23075/8)",
      six == [Fr(-152973, 32), 2627, Fr(-77113, 96), Fr(421, 4), Fr(-112, 3), Fr(35, 8)]
      and [numer(t * 96) for t in six] == [-458919, 252192, -77113, 10104, -3584, 420]
      and 4 * sum(six) == Fr(-23075, 2))
# xi closed form
okx = True
for m in (1, 2, 4, 6):
    xl = xi_list(4 * m + 6, m)
    for l in range(0, 2 * m + 3):
        want = Fr(comb(l, m), 2 ** m * comb(2 * m, m)) if l >= m else Fr(0)
        okx &= xl[2 * l] == want
check("A.1: xi_{2l,m} = 2^-m C(l,m)/C(2m,m)", okx)

section("Section 5.2: partial fractions (M2), n = 1")
T1, PP1 = partial_fractions(1)
check("Ex 5.7: polynomial part z^3 - 21 z^2 + 216 z - 1460", T1 == [-1460, 216, -21, 1])
check("Ex 5.7: a_1..a_5 = 7345, -2920, 864, -168, 16",
      [PP1["0"][k] for k in range(1, 6)] == [Q2(7345), Q2(-2920), Q2(864), Q2(-168), Q2(16)])
b = PP1["+"]
bm = PP1["-"]
check("Ex 5.7: b_1 = b_1' = 0", b[1].is_zero() and bm[1].is_zero())
check("Ex 5.7: b_2, b_3, b_4",
      b[2] == Q2(Fr(-26633, 2), Fr(150659, 16)) and b[3] == Q2(Fr(47321, 4), Fr(-33461, 4))
      and b[4] == Q2(Fr(-33461, 2), Fr(47321, 4)))
check("Ex 5.7: b_k' = conjugate of b_k (sqrt2 -> -sqrt2)", all(bm[k] == b[k].conj() for k in range(1, 5)))
check("A.3: -i(G(1+i) - G(1-i)) = -23075/2 from the partial fractions", u_from_pf(T1, PP1) == Fr(-23075, 2))
check("unit identities (5.5)",
      (Q2i(1, 1) - Q2i(SQ)).inv().re == (-(Q2i(1, 1) + Q2i(SQ)) * Q2i(1, 1) * Q2i(Fr(1, 4))).re
      and (Q2i(1, 1) - Q2i(SQ)).inv().im == (-(Q2i(1, 1) + Q2i(SQ)) * Q2i(1, 1) * Q2i(Fr(1, 4))).im)

section("Section 5.3 / A.4: removable prime, n = 2, p = 3")
T2, PP2 = partial_fractions(2)
u2 = u_from_pf(T2, PP2)
check("u_2 from partial fractions = -4338189943/14 = M1", u2 == Fr(-4338189943, 14) == FORMS[2][0])
check("T_h (polynomial part of h_2)", T2 == [-38995784, 6745574, -998316, 122666, -11992, 873, -42, 1])
a2 = [PP2["0"][k] for k in range(1, 10)]
check("a_1..a_9 of h_2",
      a2 == [Q2(v) for v in (197269821, -77991568, 26982296, -7986528, 1962656, -383744, 55872, -5376, 256)])
check("t_2 = 3*(-332772), t_5 = 3*291, a_4 = 3*(-2662176), a_7 = 3*18624; a_2, a_3 not divisible by 3",
      T2[2] == 3 * (-332772) and T2[5] == 3 * 291 and a2[3] == Q2(3 * (-2662176)) and a2[6] == Q2(3 * 18624)
      and 77991568 % 3 != 0 and 26982296 % 3 != 0)
check("c_2 = 3 * 65756607", 197269821 == 3 * 65756607)
b2 = PP2["+"]
check("b_4, b_7 of h_2 and divisibility of the numerators by 3",
      b2[4] == Q2(Fr(-99124099977, 64), Fr(280365293091, 256)) and b2[7] == Q2(Fr(13435662249, 8), Fr(-4750223943, 4))
      and all(v % 3 == 0 for v in (99124099977, 280365293091, 13435662249, 4750223943)))
check("denominator of b_2 (n=2) is 1024; b_1 = 0", b2[1].is_zero()
      and max(denom(b2[2].a), denom(b2[2].b)) == 1024, "%s" % b2[2])
# H = g^3 G_red, eta = g^2 g' G_red as rational functions; polynomial parts
gnum = pmul(ppow(pmul([-1, 1], [-2, 1]), 3), ppow([2, -2, 1], 2))
gden = pmul([0, 0, 0, 1], ppow([-2, 0, 1], 2))
Grn, Grd = [6, -8, 3], [-16, 0, 8]
# check G_red' = omega = (z-1)(z-2)/(z^2-2)^2
lhs = psub(pmul(pderiv(Grn), Grd), pmul(Grn, pderiv(Grd)))           # numerator of G_red' over Grd^2
rhs = pmul(pmul([-1, 1], [-2, 1]), [Fr(64)])                          # (z-1)(z-2) * 64, since Grd^2 = 64 (z^2-2)^2
check("G_red' = (z-1)(z-2)/(z^2-2)^2", [Fr(c) for c in lhs] == [Fr(c) for c in rhs] + [0] * (len(lhs) - len(rhs)))
Hn, Hd = pmul(ppow(gnum, 3), Grn), pmul(ppow(gden, 3), Grd)
TH, _ = pdivmod(Hn, Hd)
gpn = psub(pmul(pderiv(gnum), gden), pmul(gnum, pderiv(gden)))        # g' = gpn / gden^2
En, Ed = pmul(pmul(ppow(gnum, 2), gpn), Grn), pmul(ppow(gden, 4), Grd)
TE, _ = pdivmod(En, Ed)
check("T_H leading coefficients",
      TH[9] == Fr(3, 8) and TH[8] == Fr(-125, 8) and TH[7] == Fr(1287, 4) and TH[6] == Fr(-8743, 2)
      and TH[5] == Fr(176593, 4) and TH[4] == Fr(-1416151, 4) and TH[3] == 2352203 and TH[2] == Fr(-26681977, 2))
check("T_eta leading coefficients",
      TE[8] == Fr(9, 8) and TE[7] == -42 and TE[6] == Fr(3059, 4) and TE[5] == -9034 and TE[4] == Fr(310311, 4)
      and TE[3] == -512939 and TE[2] == 2684975)
check("T_h = T_H' - 3 T_eta", [Fr(c) for c in T2] == psub(pderiv(TH), pscale(TE, 3))[: len(T2)]
      and all(c == 0 for c in psub(pderiv(TH), pscale(TE, 3))[len(T2):]))
check("3 | c_2 and 7 | c_5 (Remark 5.10)", numer(2 * FORMS[2][1]) % 3 == 0 and numer(2 * FORMS[5][1]) % 7 == 0)

section("Section 5.4 / A.5: the coordinate w (M3)")
check("eps relations: eps(sqrt2+1) = 1, eps^2+2eps = 1, kappa = 2 sqrt2 eps = sqrt2^3 eps, 1+eps^4 = 6 eps^2",
      EPS * Q2(1, 1) == 1 and EPS * EPS + 2 * EPS == 1 and KAP == 2 * SQ * EPS and KAP == SQ ** 3 * EPS
      and Q2(1) + EPS ** 4 == 6 * EPS * EPS)
U1, V1, tm = wframe(1, per_term=True)
wantU = [Fr(32, 3), Fr(1280, 3), 10240, Fr(240640, 3), 281600, Fr(1097728, 3)]
wantV = [0, 640, 12800, 102400, 358400, 465920]
check("Ex (n=1, w): contributions to U", all(tm[i][0] == Q2(wantU[i]) for i in range(6)), [str(t[0]) for t in tm])
check("Ex (n=1, w): contributions to V/eps", all(tm[i][1] * EPS.inv() == Q2(wantV[i]) for i in range(6)))
check("Ex (n=1, w): sums 738400 and 940160", U1 == Q2(738400) and V1 == EPS * 940160)
check("B_{2,3} = (32/3) kappa^-3", B_atom(2, 3) == KAP ** (-3) * Fr(32, 3))
# App. A.5, the column i = 1 by hand
check("A.5 (i=1): B_{2,0..3} = -2/3, 4/(3k), 16/(3k^2), 32/(3k^3)",
      [B_atom(2, b_) for b_ in range(4)] == [Q2(Fr(-2, 3)), KAP ** (-1) * Fr(4, 3), KAP ** (-2) * Fr(16, 3), KAP ** (-3) * Fr(32, 3)])
e2, e4 = EPS ** 2, EPS ** 4
yd2 = Y_data(2, 1)[1]
yd1 = Y_data(1, 1)[1]
check("A.5 (i=1): data of w^-2 (w^2+eps^2)^-1 and of w^-4 (w^2+eps^2)^-1",
      yd1[0] == -2 * e2.inv() and yd1[1] == -1 * e2.inv()
      and yd2[0] == 2 * e4.inv() - Fr(2, 3) * e2.inv() and yd2[1] == e4.inv())
UT1 = KAP * yd2[0] + Fr(2, 3) - KAP ** (-1) * Fr(4, 3) - KAP ** (-2) * Fr(16, 3) - KAP ** (-3) * Fr(32, 3)
VT1 = KAP * yd2[1]
brk = (KAP ** 3) * UT1
check("A.5 (i=1): bracket = 352/3 - (eps^2/3)(160 + 64 sqrt2) = (128/3)(1 + sqrt2); contributions 1280/3 and 640 eps",
      brk == Fr(352, 3) - e2 * Q2(160, 64) * Fr(1, 3) and brk == Q2(1, 1) * Fr(128, 3)
      and 10 * EPS * brk == Q2(Fr(1280, 3)) and 10 * EPS * KAP ** 3 * VT1 == 640 * EPS
      and KAP ** 2 == 8 * e2 and KAP ** 3 == 16 * SQ * EPS ** 3 and KAP ** 4 == 64 * e4
      and EPS ** 3 - EPS == -2 * e2 and e2 * Q2(160, 64) == Q2(224, -128))
okq, c1parts = True, []
for n_ in (1, 2, 3):
    U_, V_, tm_ = wframe(n_, per_term=True)
    xi_ = xi_list(8 * n_, 2 * n_)
    for i_, (Ui_, Vi_) in enumerate(tm_):
        ui_ = (-2 * EPS * Ui_) * ((128 * EPS) ** (-n_))
        ci_ = Vi_ * ((128 * EPS) ** (-n_))
        okq &= ui_.b == 0 and ci_.b == 0
        deg_ = 3 * n_ + i_
        Pw = [comb(deg_, j_) * (-2) ** (deg_ - j_) for j_ in range(deg_ + 1)]
        cP = sum(Pw[j_] * xi_[j_] * comb(j_, j_ // 2) * 2 ** (j_ // 2) for j_ in range(0, deg_ + 1, 2))
        cP *= (-1) ** ((n_ - i_) % 2) * comb(5 * n_, i_)
        okq &= ci_.a == cP
        if n_ == 1:
            c1parts.append(ci_.a)
check("each term of (5.8) contributes rational numbers to u_n and c_n; its c-part is that of (-1)^(n-i) C(5n,i) (W-2)^(3n+i) Y^(-4n)/z (n <= 3)", okq)
check("n = 1: c_1 = 0 + 5 + 100 + 800 + 2800 + 3640", c1parts == [0, 5, 100, 800, 2800, 3640], c1parts)
okw, attained = True, []
for n in range(1, 7):
    U, V = wframe(n)
    un = (-2 * EPS * U) * ((128 * EPS) ** (-n))
    cn = V * ((128 * EPS) ** (-n))
    L = (4 * n).bit_length() - 1
    okw &= un == Q2(FORMS[n][0]) and cn == Q2(2 * FORMS[n][1])
    okw &= U.level() >= 14 * n - 2 - 2 * L and V.level() >= 14 * n
    attained.append(V.level() - 14 * n)
check("w-coordinate: u_n, c_n agree with M1 and levels (5.9) hold, n <= 6", okw)
# level(V) - 14n = 2 v_2(c_n): the bound is attained exactly when c_n is odd
check("level of V minus 14n for n = 1..6 is 0,0,0,0,2,0 (attained except for n = 5, where c_5 is even)",
      attained == [0, 0, 0, 0, 2, 0] and all(attained[n - 1] == 2 * v2q(2 * FORMS[n][1]) for n in range(1, 7)), attained)
# atoms: levels of Lemma 5.17
oka = True
for m in range(0, 9):
    for a in range(0, 40):
        s2 = bin(a).count("1")
        oka &= B_atom(m, a).level() >= a + 2 - 2 * s2
    Yd = Y_data(m, 12)
    for k in range(1, 13):
        U, V = Yd[k]
        oka &= (U * KAP ** k).level() >= 4 - k and (V * KAP ** k).level() >= 4 - k
check("Lemma (atoms): levels a+2-2 s_2(a) and 4-k, m <= 8, a < 40, k <= 12", oka)
al, be = alpha_beta(12)
check("beta_j = C(2j,j)/(4 eps^2)^j", all(be[j] == (4 * EPS * EPS) ** (-j) * comb(2 * j, j) for j in range(13)))
check("2 s_2(a) <= a+1 and s_2(a) <= floor(log2 a)+1 for 1 <= a < 5000; Legendre; Kummer",
      all(2 * bin(a).count("1") <= a + 1 and bin(a).count("1") <= a.bit_length() for a in range(1, 5000))
      and all(v2int(factorial(a)) == a - bin(a).count("1") for a in range(1, 300))
      and all(v2int(comb(2 * j, j)) == bin(j).count("1") for j in range(1, 300)))
mp.mp.dps = 30
check("theta = (2/eps) arctan(1/eps) = 3 pi/(4 eps)",
      abs(2 / EPS.mp() * mp.atan(1 / EPS.mp()) - 3 * mp.pi / (4 * EPS.mp())) < mp.mpf(10) ** (-25))

section("Section 6: growth")
mp.mp.dps = 40
check("8.9 < log 7345", mp.log(7345) > mp.mpf("8.9"), mp.nstr(mp.log(7345), 8))
x0q = Fr(3913, 10000)
fx = ((x0q + 1) * (x0q + 2)) ** 5 * (x0q * x0q + 2 * x0q + 2) ** 3 / (x0q ** 4 * (2 - x0q * x0q) ** 4)
fxm = mp.mpf(numer(fx)) / denom(fx)
check("f(-0.3913) = 37810.99167... < 37811 (exact rational)", fx < 37811 and trunc_eq(fxm, "37810.99167"),
      mp.nstr(fxm, 12))
lowE = mp.mpf("2.7182818283") ** 10 * mp.fsum(mp.mpf("0.540357") ** i / mp.factorial(i) for i in range(10))
check("e^10.540357 >= 2.7182818283^10 * sum_{i<=9} 0.540357^i/i! = 22026.4657.. x 1.7166195.. = 37811.0625.. > 37811",
      lowE > 37811 and trunc_eq(mp.mpf("2.7182818283") ** 10, "22026.4657")
      and trunc_eq(mp.fsum(mp.mpf("0.540357") ** i / mp.factorial(i) for i in range(10)), "1.7166195")
      and trunc_eq(lowE, "37811.0625"), mp.nstr(lowE, 12))
# critical points: 4W^3 + W^2 - 88W + 152
roots = mp.polyroots([4, 1, -88, 152], maxsteps=200, extraprec=200)
Wr = [w for w in roots if abs(mp.im(w)) < mp.mpf(10) ** (-20)][0].real
Wc = [w for w in roots if mp.im(w) > mp.mpf(10) ** (-20)][0]
x0 = (-Wr - mp.sqrt(Wr * Wr - 8)) / 2
lam3 = f_mp(-x0)
check("real critical point W = -5.5028..., x_0 = 0.3912692430..., lambda_3 = 37810.99119500591..., log = 10.5403551116...",
      trunc_eq(Wr, "-5.5028") and trunc_eq(x0, "0.3912692430") and trunc_eq(lam3, "37810.99119500591")
      and trunc_eq(mp.log(lam3), "10.5403551116"), "%s %s %s" % (mp.nstr(x0, 14), mp.nstr(lam3, 18), mp.nstr(mp.log(lam3), 14)))
cub = lambda L: 2 ** 20 * L ** 3 - 39647694848 * L ** 2 - 115523712 * L - 3 ** 3 * 5 ** 5
check("lambda_3 is a root of 2^20 L^3 - 39647694848 L^2 - 115523712 L - 3^3 5^5",
      abs(cub(lam3)) < abs(2 ** 20 * lam3 ** 3) * mp.mpf(10) ** (-30))
if not FAST:
    for nn in (200, 400):
        FORMS[nn] = forms_M1(nn)
    mp.mp.dps = 50
    d200 = mp.log(mp.mpf(numer(FORMS[200][1])) / denom(FORMS[200][1])) - 200 * mp.log(lam3) + mp.log(200) / 2
    d400 = mp.log(mp.mpf(numer(FORMS[400][1])) / denom(FORMS[400][1])) - 400 * mp.log(lam3) + mp.log(400) / 2
    check("log v_n - n log lambda_3 + (1/2) log n = -2.3230, -2.3229 for n = 200, 400",
          round_eq(d200, "-2.3230") and round_eq(d400, "-2.3229"), "%s %s" % (mp.nstr(d200, 7), mp.nstr(d400, 7)))

section("Section 7 / A.7: decay, the polygon, the certificates")
mp.mp.dps = 40
lf = lambda y: mp.log(abs(f_mp(mp.mpc(1, y))))
ymax = mp.findroot(lambda y: mp.diff(lf, y), mp.mpf("0.54"))
check("max of |f| on the segment: e^-6.0709... at y = 0.5428...",
      trunc_eq(lf(ymax), "-6.0709") and trunc_eq(ymax, "0.5428"), "%s at %s" % (mp.nstr(lf(ymax), 8), mp.nstr(ymax, 8)))
zsx, zsy = Fr(19787, 16384), Fr(32371, 65536)
rho = Fr(1458809, 10 ** 9)
zs = mp.mpc(mp.mpf(19787) / 16384, mp.mpf(32371) / 65536)
check("z_s = 1.20770... + 0.49394... i", trunc_eq(zs.real, "1.20770") and trunc_eq(zs.imag, "0.49394"))
# W = z + 2/z: each complex root W has the two preimages z, 2/z; the saddle z_1 of the paper is the preimage
# with 1 < Re z < 1.3 and Im z > 0 (it belongs to the root W with negative imaginary part)
pre = [(w + sg * mp.sqrt(w * w - 8)) / 2 for w in (Wc, mp.conj(Wc)) for sg in (1, -1)]
z1 = [z for z in pre if 1 < z.real < mp.mpf("1.3") and z.imag > 0][0]
check("the four saddle points are z_1, conj z_1, 2/z_1, 2/conj z_1 (grey square of Fig. 1: 2/conj z_1 = 1.4187 + 0.5802 i)",
      min(abs(2 / mp.conj(z1) - z) for z in pre) < mp.mpf(10) ** (-30) and round_eq((2 / mp.conj(z1)).real, "1.4187")
      and round_eq((2 / mp.conj(z1)).imag, "0.5802"))
check("saddle: W = 2.62641... +- 0.08629... i, z_1 = 1.20770992... + 0.49394723... i",
      trunc_eq(Wc.real, "2.62641") and trunc_eq(Wc.imag, "0.08629") and trunc_eq(z1.real, "1.20770992")
      and trunc_eq(z1.imag, "0.49394723"), mp.nstr(z1, 12))
s_exact = -mp.log(abs(f_mp(z1)))
check("|f(z_1)| = e^-6.53013614... = 0.00145880722...",
      trunc_eq(s_exact, "6.53013614") and trunc_eq(abs(f_mp(z1)), "0.00145880722"), mp.nstr(s_exact, 14))
rho_mp = mp.mpf(1458809) / 10 ** 9
check("|z_s - z_1| < 1e-5; rho/|f(z_1)| - 1 = 1.2e-6; rho^2 - |f(z_s)|^2 = 5.2e-12",
      abs(zs - z1) < mp.mpf(10) ** (-5) and round_eq((rho_mp / abs(f_mp(z1)) - 1) * 10 ** 6, "1.2")
      and round_eq((rho_mp ** 2 - abs(f_mp(zs)) ** 2) * 10 ** 12, "5.2"),
      "%s %s %s" % (mp.nstr(abs(zs - z1), 4), mp.nstr(rho_mp / abs(f_mp(z1)) - 1, 4),
                    mp.nstr(rho_mp ** 2 - abs(f_mp(zs)) ** 2, 4)))
check("f(z_1), conj: roots of the cubic of critical values; modulus e^-s, argument 0.98363 pi; -0.00145687795 +- 0.00007500089 i",
      abs(cub(f_mp(z1))) < mp.mpf(10) ** (-25) * abs(2 ** 20 * lam3 ** 3)
      and trunc_eq(f_mp(z1).real, "-0.00145687795") and trunc_eq(abs(f_mp(z1).imag), "0.00007500089")
      and round_eq(abs(mp.arg(f_mp(z1))) / mp.pi, "0.98363"), mp.nstr(f_mp(z1), 12))
check("s = (r + 20 log 2 - 3 log 3 - 5 log 5)/2",
      abs(s_exact - (mp.log(lam3) + 20 * mp.log(2) - 3 * mp.log(3) - 5 * mp.log(5)) / 2) < mp.mpf(10) ** (-30))


def Qpoly(seg):
    if seg == 1:
        X, Y = [Fr(1), Fr(3403, 16384)], [Fr(0), Fr(32371, 65536)]
    else:
        X, Y = [Fr(19787, 16384), Fr(-3403, 16384)], [Fr(32371, 65536), Fr(33165, 65536)]
    sq = lambda p: pmul(p, p)
    X1, X2 = psub(X, [Fr(1)]), psub(X, [Fr(2)])
    Y1m, Y1p = psub(Y, [Fr(1)]), padd(Y, [Fr(1)])
    A1 = padd(sq(X1), sq(Y))
    A2 = padd(sq(X2), sq(Y))
    A3 = padd(sq(X1), sq(Y1m))
    A4 = padd(sq(X1), sq(Y1p))
    B1 = padd(sq(X), sq(Y))
    B2 = padd(sq(psub(psub(sq(X), sq(Y)), [Fr(2)])), pscale(pmul(sq(X), sq(Y)), 4))
    Num = pmul(ppow(pmul(A1, A2), 5), ppow(pmul(A3, A4), 3))
    Den = pmul(ppow(B1, 4), ppow(B2, 4))
    return psub(pscale(Den, rho * rho), Num), Num, Den


def bernstein(Q, t0, ell, d=32):
    a = pcompose_affine(Q, Fr(t0), Fr(ell))
    a = a + [Fr(0)] * (d + 1 - len(a))
    return [sum(comb(d - i, j - i) * a[i] for i in range(j + 1)) for j in range(d + 1)]


Q1, Num1, Den1 = Qpoly(1)
Q2p, Num2, Den2 = Qpoly(2)
check("degrees: Num 32, Den 24, Q 32", len(Num1) - 1 == 32 and len(Den1) - 1 == 24 and len(Q1) - 1 == 32
      and len(Q2p) - 1 == 32)
c10 = bernstein(Q1, 0, 1)
c2f = bernstein(Q2p, 0, 1)
c20 = bernstein(Q2p, 0, Fr(1, 2))
c21 = bernstein(Q2p, Fr(1, 2), Fr(1, 2))
fl = lambda q: mp.mpf(numer(q)) / denom(q)
check("segment 1: all 33 Bernstein coefficients on [0,1] positive; beta_0 = rho^2 = 2.128..e-6; min = beta_32 = 7.5..e-10",
      all(c > 0 for c in c10) and c10[0] == rho * rho and trunc_eq(fl(c10[0]) * 10 ** 6, "2.128")
      and min(c10) == c10[32] and trunc_eq(fl(c10[32]) * 10 ** 10, "7.5"),
      "min %s" % mp.nstr(fl(min(c10)), 4))
neg = [j for j, c in enumerate(c2f) if c <= 0]
check("segment 2 on [0,1]: exactly one negative coefficient, beta_1 = -1.0..e-8",
      neg == [1] and trunc_eq(fl(c2f[1]) * 10 ** 8, "-1.0"), "negative at %s: %s" % (neg, mp.nstr(fl(c2f[1]), 4)))
check("segment 2 on [0,1/2] and [1/2,1]: all positive; minima 7.5..e-10 and 5.4..e-3",
      all(c > 0 for c in c20) and all(c > 0 for c in c21) and trunc_eq(fl(min(c20)) * 10 ** 10, "7.5")
      and trunc_eq(fl(min(c21)) * 10 ** 3, "5.4"), "%s %s" % (mp.nstr(fl(min(c20)), 4), mp.nstr(fl(min(c21)), 4)))
check("Den(z=1) = 1, Q(1) on segment 1 = Q(0) on segment 2 (the point z_s)", Den1[0] == 1 and sum(Q1) == Q2p[0])
# compare with the Lean certificate file
here = os.path.dirname(os.path.abspath(__file__))
cands = [os.path.join(here, "..", "lean", "MuPi", "K2H", "ContourCert.lean")]
up = here
for _ in range(8):
    up = os.path.dirname(up)
    cands.append(os.path.join(up, "formal", "RecMath", "RecMath", "PiMeasure", "K2H", "ContourCert.lean"))
cert = next((c for c in cands if os.path.exists(c)), None)
if cert is None:
    print("SKIP  Lean certificate file not found (looked in lean/MuPi/K2H and formal/RecMath/...)")
else:
    txt = open(cert, encoding="utf-8").read()
    blocks = re.split(r"\nlemma cert_", txt)[1:]
    got = {}
    for blk in blocks:
        name = blk.split()[0]
        # only the certificate identity ("have key : ... = <33 terms> := by")
        body = blk.split(":= by")[1] if ":= by" in blk else blk
        coeffs = re.findall(r"\(\((-?\d+) : ℝ\)(?: / (\d+))?\) \* s \^ (\d+) \* r \^ (\d+)", blk)
        lst = [None] * 33
        for num, den, js, rs in coeffs:
            j = int(js)
            if int(rs) == 32 - j and lst[j] is None:
                lst[j] = Fr(int(num), int(den) if den else 1)
        got[name] = lst
    okc = (got.get("seg1_0") == c10 and got.get("seg2_0") == c20 and got.get("seg2_1") == c21)
    check("the 99 coefficients of ContourCert.lean coincide with the recomputed ones (%s)" % os.path.relpath(cert, here),
          okc, {k: (v.count(None) if v else None) for k, v in got.items()})
# rho < e^{-6.530134}
mp.mp.dps = 40
tay = mp.fsum(mp.mpf("0.530134") ** m / mp.factorial(m) for m in range(12)) + 13 * mp.mpf("0.530134") ** 12 / (12 * mp.factorial(12))
e6 = mp.mpf("2.7182818286") ** 6
check("A.7: Taylor bound <= 1.69915999;  2.7182818286^6 = 403.42879...;  product < 685.49007 < 1/rho = 685.49069...",
      tay <= mp.mpf("1.69915999") and trunc_eq(e6, "403.42879") and e6 * mp.mpf("1.69915999") < mp.mpf("685.49007")
      and mp.mpf("685.49007") < 1 / rho_mp and trunc_eq(1 / rho_mp, "685.49069"),
      "taylor=%s e6=%s prod=%s" % (mp.nstr(tay, 12), mp.nstr(e6, 12), mp.nstr(e6 * mp.mpf("1.69915999"), 12)))
check("rho < e^-6.530134 (direct)", rho_mp < mp.exp(mp.mpf("-6.530134")), mp.nstr(mp.log(rho_mp), 12))
l1, l2 = abs(zs - 1), abs(mp.mpc(1, 1) - zs)
check("lengths 0.5358..., 0.5470...; crude bounds < 0.71, < 0.72; 2(l1+l2) < 2.17",
      trunc_eq(l1, "0.5358") and trunc_eq(l2, "0.5470") and Fr(3403, 16384) + Fr(32371, 65536) < Fr(71, 100)
      and Fr(3403, 16384) + Fr(33165, 65536) < Fr(72, 100) and 2 * (l1 + l2) < mp.mpf("2.17"))
check("|J_1| = 0.00098, 4 rho = 0.0058", round_eq(abs(J1), "0.00098") and round_eq(4 * rho_mp, "0.0058"))


def poly_point(y):
    y = mp.mpf(y)
    ys = mp.mpf(32371) / 65536
    if y <= ys:
        t = y / ys
        return mp.mpc(1 + mp.mpf(3403) / 16384 * t, y)
    t = (y - ys) / (1 - ys)
    return mp.mpc(mp.mpf(19787) / 16384 - mp.mpf(3403) / 16384 * t, y)


fig = {"0.1200": (-10.804, -10.446), "0.3000": (-7.134, -7.090), "0.4939": (-6.108, -6.530),
       "0.5429": (-6.071, -6.535), "0.7000": (-6.465, -6.795), "0.9400": (-10.360, -10.240)}
check("Figure 2: sample points of both curves",
      all(abs(lf(mp.mpf(y)) - a) < 0.0011 and abs(mp.log(abs(f_mp(poly_point(y)))) - b) < 0.0011
          for y, (a, b) in fig.items()))

section("Section 8 / A.8: the multiplier")
mp.mp.dps = 40
part1 = mp.digamma(mp.mpf(3) / 4) - mp.digamma(mp.mpf(2) / 3)
part2 = mp.digamma(mp.mpf(5) / 4) - mp.digamma(mp.mpf(6) / 5)
varpi = part1 + part2
check("varpi = 0.2323735360... + 0.0615863632... = 0.29395989921603919...",
      trunc_eq(part1, "0.2323735360") and trunc_eq(part2, "0.0615863632") and trunc_eq(varpi, "0.29395989921603919"),
      mp.nstr(varpi, 22))
ser = mp.nsum(lambda k: 1 / ((3 * k + 2) * (4 * k + 3)), [0, mp.inf]) + mp.nsum(lambda k: 1 / ((4 * k + 1) * (5 * k + 1)), [1, mp.inf])
check("the two series sum to varpi", abs(ser - varpi) < mp.mpf(10) ** (-25))
K = 10 ** 5
vK = sum(1.0 / ((3 * k + 2) * (4 * k + 3)) for k in range(K)) + sum(1.0 / ((4 * k + 1) * (5 * k + 1)) for k in range(1, K))
check("varpi_K (K = 10^5) = 0.29395856588...; varpi - varpi_K < 1.4e-6, about 2/(15K)",
      abs(vK - 0.29395856588) < 2e-11 and 0 < float(varpi) - vK < 1.4e-6 and abs((float(varpi) - vK) * 15 * K / 2 - 1) < 1e-3,
      "%.14f" % vK)
head = sum(Fr(1, (3 * k + 2) * (4 * k + 3)) for k in range(20)) + sum(Fr(1, (4 * k + 1) * (5 * k + 1)) for k in range(1, 20))
check("head (20 + 19 terms) = 0.28730270... (exact)", trunc_eq(fl(head), "0.28730270"), mp.nstr(fl(head), 12))
okt = True
for xk in range(20, 4000):
    a_, b_ = Fr(43, 200), Fr(67, 250)
    okt &= Fr(1, (3 * xk + 2) * (4 * xk + 3)) >= Fr(1, 12) * (1 / (xk + a_) - 1 / (xk + 1 + a_))
    okt &= Fr(1, (4 * xk + 1) * (5 * xk + 1)) >= Fr(1, 20) * (1 / (xk - b_) - 1 / (xk + 1 - b_))
check("telescoping minorants for 20 <= x < 4000; constants 2.86.., 4.92..",
      okt and trunc_eq(mp.mpf(6) - 12 * mp.mpf("0.215") * mp.mpf("1.215"), "2.86")
      and trunc_eq(1 + 20 * mp.mpf("0.268") * mp.mpf("0.732"), "4.92"))
lowK = Fr(28730270, 10 ** 8) + Fr(1, 12) * (1 / Fr(20215, 1000) - 1 / (K + Fr(215, 1000))) + Fr(1, 20) * (1 / Fr(19732, 1000) - 1 / (K - Fr(268, 1000)))
check("lower bound 0.2939576... >= 0.293957", trunc_eq(fl(lowK), "0.2939576") and lowK >= Fr(293957, 10 ** 6), mp.nstr(fl(lowK), 10))
# Lemma 8.1 (windows), brute force
okl = True
for n in range(1, 400):
    for p in primes_upto(6 * n + 10):
        if p * p > 4 * n:
            t = Fr(n % p, p)
            inw = (Fr(1, 5) <= t < Fr(1, 4)) or (Fr(2, 3) <= t < Fr(3, 4))
            okl &= removable(n, p) == inw
check("Lemma 8.1 (windows) for all n < 400 and all primes p < 6n+10 with p^2 > 4n", okl)
ok21 = [p for p in primes_upto(84) if removable(21, p)] == [17, 29, 31]
check("n = 21: removable primes 17, 29, 31; windows (28,31.5], (16.8,17.5], (12,12.6]", ok21
      and Fr(84, 3) == 28 and Fr(63, 2) == Fr(315, 10) and Fr(84, 5) == Fr(168, 10) and Fr(105, 6) == Fr(175, 10)
      and Fr(84, 7) == 12 and Fr(63, 5) == Fr(126, 10))
if not FAST:
    import numpy as np
    NMAX = 4 * 10 ** 7
    sv = np.ones(NMAX + 1, dtype=bool)
    sv[:2] = False
    for i in range(2, int(NMAX ** 0.5) + 1):
        if sv[i]:
            sv[i * i :: i] = False
    PR = np.nonzero(sv)[0].astype(np.int64)
    LOGP = np.log(PR.astype(np.float64))
    vals = []
    for n in (10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7):
        M = 4 * n
        idx = np.searchsorted(PR, M, side="right")
        pr, lg = PR[:idx], LOGP[:idx]
        psi = float(lg.sum())
        for p in pr[pr * pr <= M]:
            p = int(p)
            e, q = 1, p
            while q * p <= M:
                q *= p
                e += 1
            psi += (e - 1) * float(np.log(p))
        rem = (pr * pr > M) & ((M // pr) % 2 == 0) & (((5 * n) % pr + (3 * n) % pr) < (M % pr))
        vals.append((psi - float(lg[rem].sum())) / n)
    check("(1/n) log D_n = 3.70706, 3.70527, 3.70614, 3.70641 for n = 10^4..10^7 (rounded to 5 decimals)",
          ["%.5f" % v for v in vals] == ["3.70706", "3.70527", "3.70614", "3.70641"], ["%.8f" % v for v in vals])

section("Section 9: the final arithmetic and the exact rates")
check("10.540357 + (4 - 0.293957) = 14.2464;  6.530134 - 3.706043 = 2.824091",
      Fr("10.540357") + 4 - Fr("0.293957") == Fr("14.2464") and Fr("6.530134") - Fr("3.706043") == Fr("2.824091"))
check("2.824091 * 5.0446 = 14.2464094586 > 14.2464;  2.82409 * 5.0446 = 14.246404414 > 14.2464",
      Fr("2.824091") * Fr("5.0446") == Fr("14.2464094586") and Fr("2.82409") * Fr("5.0446") == Fr("14.246404414"))
check("1 + 14.2464/2.824091 = 6.04459665... < 6.0446", trunc_eq(1 + mp.mpf("14.2464") / mp.mpf("2.824091"), "6.04459665"))
r_ex, C_ex = mp.log(lam3), 4 - varpi
check("exact rates: r = 10.5403551..., s = 6.5301361..., C = 3.7060401...; r+C = 14.2463952124..., s-C = 2.8240960465...",
      trunc_eq(r_ex, "10.5403551") and trunc_eq(s_exact, "6.5301361") and trunc_eq(C_ex, "3.7060401")
      and trunc_eq(r_ex + C_ex, "14.2463952124") and trunc_eq(s_exact - C_ex, "2.8240960465"),
      "%s %s" % (mp.nstr(r_ex + C_ex, 14), mp.nstr(s_exact - C_ex, 14)))
bound = 1 + (r_ex + C_ex) / (s_exact - C_ex)
check("1 + (r+C)/(s-C) = 6.04458594096...", trunc_eq(bound, "6.04458594096"), mp.nstr(bound, 16))
check("with D_n itself: sigma <= 14.246398, tau >= 2.824093",
      mp.mpf("10.540357") + C_ex <= mp.mpf("14.246398") and mp.mpf("6.530134") - C_ex >= mp.mpf("2.824093"))
b_noprimes = 1 + (r_ex + 4) / (s_exact - 4)
b_nopath = 1 + (r_ex + C_ex) / (-lf(ymax) - C_ex)
check("without removable primes: 6.7469; without moving the path: 7.0241",
      round_eq(b_noprimes, "6.7469") and round_eq(b_nopath, "7.0241"), "%s %s" % (mp.nstr(b_noprimes, 7), mp.nstr(b_nopath, 7)))
check("budget table: (s-C)/(r+C) = 0.19823 -> 6.0446", round_eq((s_exact - C_ex) / (r_ex + C_ex), "0.19823"))
want = [(44070, 138450, "-0.01175"), (27617774940, 86763798860, "0.000292"),
        (84532652762578020, 265567160907372048, "-0.0000339")]
mp.mp.dps = 60
okf = True
for n, (q, p, val) in zip((1, 2, 3), want):
    D = Dmult(n)
    okf &= D * FORMS[n][1] == q and -D * FORMS[n][0] == p and trunc_eq(q * mp.pi - p, val)
check("Example 9.1: the integer forms D_n J_n for n = 1, 2, 3; 390 (113 pi - 355)", okf and 390 * 113 == 44070 and 390 * 355 == 138450)

section("Section 11: Table 7 and the integrality checks")
NT = (1, 5, 10, 20, 50, 100) if FAST else (1, 5, 10, 20, 50, 100, 200, 400)
TAB7 = {1: ("8.2086", "6.9283", "2.4849", "0.4155", -1), 5: ("9.9145", "6.7855", "3.4639", "0.2483", -1),
        10: ("10.1928", "6.7369", "3.6215", "0.2255", 1), 20: ("10.3493", "6.7032", "3.8049", "0.2048", -1),
        50: ("10.4548", "6.5687", "3.7261", "0.2004", -1), 100: ("10.4941", "6.5537", "3.6743", "0.2032", 1),
        200: ("10.5155", "6.5628", "3.7254", "0.1992", 1), 400: ("10.5271", "6.5382", "3.7177", "0.1980", -1)}
ok7 = True
det = []
for n in NT:
    if n not in FORMS:
        FORMS[n] = forms_M1(n)
    u, v = FORMS[n]
    mp.mp.dps = int(12 * n) + 80
    J = J_exact_mp(u, v)
    D = Dmult(n)
    vm = mp.mpf(numer(v)) / denom(v)
    c1, c2, c3 = mp.log(vm) / n, -mp.log(abs(J)) / n, mp.log(D) / n
    c4 = -mp.log(abs(D * J)) / mp.log(D * vm)
    row = TAB7[n]
    good = round_eq(c1, row[0]) and round_eq(c2, row[1]) and round_eq(c3, row[2]) and round_eq(c4, row[3]) and mp.sign(J) == row[4]
    ok7 &= good
    det.append("%d:%s" % (n, "ok" if good else (mp.nstr(c1, 6), mp.nstr(c2, 6), mp.nstr(c3, 6), mp.nstr(c4, 5), int(mp.sign(J)))))
check("Table 7 (rates and signs), n in %s" % (NT,), ok7, " ".join(map(str, det)))
NI = 60 if FAST else 300
PRS = primes_upto(4 * NI)
oki, okr, ok2, okc = True, True, True, True
signs = {}
lcm_cur, m_cur = 1, 0
for n in range(1, NI + 1):
    if n not in FORMS:
        FORMS[n] = forms_M1(n)
    u, v = FORMS[n]
    D = Dmult(n)
    oki &= denom(D * u) == 1 and denom(D * v) == 1
    okr &= all(denom(u) % p != 0 for p in PRS if p <= 4 * n and removable(n, p))
    ok2 &= v2int(denom(u)) <= (4 * n).bit_length() - 1
    okc &= denom(2 * v) == 1 and 2 * v > 0
    mp.mp.dps = int(12 * n) + 80
    signs[n] = int(mp.sign(J_exact_mp(u, v)))
check("D_n u_n, D_n v_n integers for n <= %d" % NI, oki)
check("no removable prime divides the denominator of u_n, n <= %d" % NI, okr)
check("2^floor(log2 4n) u_n has odd denominator, n <= %d" % NI, ok2)
check("c_n is a positive integer, n <= %d" % NI, okc)
if not FAST:
    for n in range(NI + 1, 421):
        u, v = forms_M1(n)
        mp.mp.dps = int(12 * n) + 80
        signs[n] = int(mp.sign(J_exact_mp(u, v)))
same = [n for n in range(2, max(signs) + 1) if signs[n] == signs[n - 1]]
check("sign of J_n alternates for n <= %d except at n = 18, 78, 139, 200, 261, 322, 383" % max(signs),
      same == ([18] if FAST else [18, 78, 139, 200, 261, 322, 383]), same)
mp.mp.dps = 40
okpp = True
for n in range(1, min(NI, 120) + 1):
    for p in PRS:
        if p > 4 * n or p == 2:
            continue
        e = 0
        while p ** (e + 1) <= 4 * n:
            e += 1
        dd = denom(FORMS[n][0])
        k = 0
        while dd % p == 0:
            dd //= p
            k += 1
        okpp &= k <= e
check("Prop 5.6: p^floor(log_p 4n) u_n is p-integral for odd p <= 4n, n <= %d" % min(NI, 120), okpp)

section("Appendices B-D (not part of the proof)")
mp.mp.dps = 40


def crit_cubic(e1, e2, d):
    a = e1 + e2 - d
    return [a, -(2 * e1 + 3 * e2 - 5 * d), -(8 * e1 + 8 * e2 + 6 * d), 16 * e1 + 24 * e2]


def varpi_gen(e1, e2, d):
    a = e1 + e2 - d
    M = max(a, d)
    P = 1 if d % 2 == 0 else 2
    pts = sorted(set([Fr(k, e1) for k in range(P * e1 + 1)] + [Fr(k, e2) for k in range(P * e2 + 1)]
                     + [Fr(k, d) for k in range(P * d + 1)]))
    tot = mp.mpf(0)
    ivs = []
    for lo, hi in zip(pts[:-1], pts[1:]):
        mid = (lo + hi) / 2
        fr = lambda q: q - (numer(q) // denom(q))
        fl_ = lambda q: numer(q) // denom(q)
        if fl_(d * mid) % 2 == 0 and fr(e1 * mid) + fr(e2 * mid) < fr(d * mid):
            ivs.append((lo, hi))
            lo_m, hi_m = mp.mpf(numer(lo)) / denom(lo), mp.mpf(numer(hi)) / denom(hi)
            cut = mp.mpf(1) / M
            if hi_m > cut:                                   # k = 0, clipped at 1/M
                tot += 1 / max(lo_m, cut) - 1 / hi_m
            tot += (mp.digamma(1 + hi_m / P) - mp.digamma(1 + lo_m / P)) / P   # k >= 1
    return tot, ivs, M


def constants(e1, e2, d):
    a = e1 + e2 - d
    rts = mp.polyroots(crit_cubic(e1, e2, d), maxsteps=500, extraprec=400)
    out = {"roots": rts}
    best_r, svals = None, []
    for w in rts:
        for sgn in (1, -1):
            z = (w + sgn * mp.sqrt(w * w - 8)) / 2
            val = mp.log(abs(f_gen(z, e1, e2, d)))
            if abs(mp.im(z)) < mp.mpf(10) ** (-15) and -mp.sqrt(2) < mp.re(z) < 0:
                best_r = val
            elif mp.re(z) > 0:
                svals.append((-val, z))
    vp, ivs, M = varpi_gen(e1, e2, d)
    gam = max(0, d - mp.mpf(3) / 2 * e2) if e2 <= d else -mp.mpf(e2 - d) / 2
    C = M + gam * mp.log(2) - vp
    out.update(r=best_r, s_candidates=svals, varpi=vp, C=C, S=ivs, M=M)
    return out


TABB = [((46, 28, 37), "97.4670", "60.2778", "34.1494", "6.037296"), ((36, 22, 29), "76.3863", "47.2173", "26.7451", "6.037629"),
        ((41, 25, 33), "86.9266", "53.7475", "30.4480", "6.037649"), ((5, 3, 4), "10.5404", "6.5301", "3.7060", "6.044586"),
        ((16, 10, 13), "34.2249", "21.0953", "11.9446", "6.045473"), ((6, 4, 5), "13.1441", "8.0310", "4.5518", "6.086269"),
        ((4, 2, 3), "7.9365", "4.9940", "2.8743", "6.100005"), ((3, 3, 2), "9.1290", "4.3878", "2.4849", "7.103205")]
CONS = {}
for trip, rs, ss, Cs, bs in TABB:
    c = constants(*trip)
    CONS[trip] = c
    cand = [sv for sv, _ in c["s_candidates"] if round_eq(sv, ss)]
    good = round_eq(c["r"], rs) and round_eq(c["C"], Cs) and bool(cand)
    if good:
        good = round_eq(1 + (c["r"] + c["C"]) / (cand[0] - c["C"]), bs)
        c["s"] = cand[0]
    check("App. B table, triple %s: r, s, C, bound" % (trip,), good,
          "r=%s C=%s s-candidates=%s" % (mp.nstr(c["r"], 8), mp.nstr(c["C"], 8), [mp.nstr(sv, 8) for sv, _ in c["s_candidates"]]))
c534 = CONS[(5, 3, 4)]
check("(5,3,4): S = [1/5,1/4) u [2/3,3/4) per period, varpi as in Section 8",
      c534["S"] == [(Fr(1, 5), Fr(1, 4)), (Fr(2, 3), Fr(3, 4))] and abs(c534["varpi"] - varpi) < mp.mpf(10) ** (-30))
check("general critical cubic gives 4W^3+W^2-88W+152 for (5,3,4), 3W^3+W^2-66W+112 for (4,2,3), 4W^3-5W^2-60W+120 for (3,3,2)",
      crit_cubic(5, 3, 4) == [4, 1, -88, 152] and crit_cubic(4, 2, 3) == [3, 1, -66, 112] and crit_cubic(3, 3, 2) == [4, -5, -60, 120])
c423 = CONS[(4, 2, 3)]
Xi = 4 * mp.log((9 + mp.sqrt(65)) / 2) + mp.log((7 + mp.sqrt(65)) / 2) / 2
check("(4,2,3): r = Xi - (3/2) log 3 = 7.9364908182..., s = Xi - 9 log 2 + (3/2) log 3 = 4.9940030592...",
      trunc_eq(Xi - 1.5 * mp.log(3), "7.9364908182") and abs(c423["r"] - (Xi - mp.mpf(3) / 2 * mp.log(3))) < mp.mpf(10) ** (-25)
      and trunc_eq(Xi - 9 * mp.log(2) + mp.mpf(3) / 2 * mp.log(3), "4.9940030592")
      and any(abs(sv - (Xi - 9 * mp.log(2) + mp.mpf(3) / 2 * mp.log(3))) < mp.mpf(10) ** (-25) for sv, _ in c423["s_candidates"]))
s423 = Xi - 9 * mp.log(2) + mp.mpf(3) / 2 * mp.log(3)
zc423 = [z for sv, z in c423["s_candidates"] if abs(sv - s423) < mp.mpf(10) ** (-20)]
check("(4,2,3): the relevant critical point lies on |z| = sqrt2", bool(zc423) and abs(abs(zc423[0]) - mp.sqrt(2)) < mp.mpf(10) ** (-25))
check("(4,2,3): S in [0,2) = [1/4,1/3) u [3/2,5/3), varpi = 0.1257483125..., bounds 6.1000049580..., 6.4846910929...",
      c423["S"] == [(Fr(1, 4), Fr(1, 3)), (Fr(3, 2), Fr(5, 3))] and trunc_eq(c423["varpi"], "0.1257483125")
      and trunc_eq(1 + (c423["r"] + c423["C"]) / (s423 - c423["C"]), "6.1000049580")
      and trunc_eq(1 + (c423["r"] + 3) / (s423 - 3), "6.4846910929"),
      "%s %s" % (c423["S"], mp.nstr(c423["varpi"], 12)))
c332 = CONS[(3, 3, 2)]
s332 = c332.get("s")
check("(3,3,2): varpi = 1.1685237..., C = 2.4849026..., r+C = 11.613890045331..., s-C = 1.902916485599..., bound 7.1032053341370017275057734228...",
      s332 is not None and trunc_eq(c332["varpi"], "1.1685237") and trunc_eq(c332["C"], "2.4849026")
      and trunc_eq(c332["r"] + c332["C"], "11.613890045331") and trunc_eq(s332 - c332["C"], "1.902916485599")
      and trunc_eq(1 + (c332["r"] + c332["C"]) / (s332 - c332["C"]), "7.10320533413700172750577342281"),
      mp.nstr(1 + (c332["r"] + c332["C"]) / (s332 - c332["C"]), 34) if s332 is not None else "")
check("(3,3,2): S = [1/3,1/2) per period", c332["S"] == [(Fr(1, 3), Fr(1, 2))])
check("intro: Zeilberger-Zudilin sigma = 11.6138..., tau = 1.9029...",
      s332 is not None and trunc_eq(c332["r"] + c332["C"], "11.6138") and trunc_eq(s332 - c332["C"], "1.9029"))
mp.mp.dps = 70
okz = True
ratios = ["4/3", "16/5", "160/21", "1792/99", "6144/143", "22528/221"]
for n in range(1, 7):
    gz = lambda x: 5 * x ** (2 * n) * (x ** 4 + 6 * x * x + 25) ** (2 * n) / (25 - x * x) ** (3 * n + 1)
    In = mp.mpc(0, 1) * (-1) ** (n + 1) * mp.quad(lambda t: gz(mp.mpc(-1, t)) * mp.mpc(0, 1), mp.linspace(-2, 2, 9))
    Jn = mp.quad(lambda t: f_gen(mp.mpc(1, t), 3, 3, 2) ** n / mp.mpc(1, t), mp.linspace(-1, 1, 9))
    rat = In / Jn
    okz &= abs(rat - mp.mpf(numer(Fr(ratios[n - 1]))) / denom(Fr(ratios[n - 1]))) < mp.mpf(10) ** (-50)
check("App. C: I_n/J_n = 4/3, 16/5, 160/21, 1792/99, 6144/143, 22528/221 to 50 digits (n <= 6)", okz)
check("rational factors grow roughly like (64/27)^n: ratio of consecutive factors -> 2.37",
      abs(float(Fr("22528/221") / Fr("6144/143")) - 64 / 27) < 0.05, float(Fr("22528/221") / Fr("6144/143")))
try:
    import sympy as sp
    W, lam_, Ns = sp.symbols("W lambda N")
    fW = (W - 3) ** 3 * (W - 2) ** 3 / (W ** 2 - 8)
    gy = lambda y: y * (y ** 2 + 6 * y + 25) ** 2 / (y - 25) ** 3
    lhs_ = sp.together(fW - sp.Rational(27, 64) * gy(25 - 10 * W))
    rhs_ = (4 * W ** 3 - 5 * W ** 2 - 60 * W + 120) ** 2 * (2 * W ** 3 - 25 * W ** 2 + 96 * W - 120) / (32 * W ** 3 * (W ** 2 - 8))
    check("App. C: the identity f(W) - (27/64) g(25-10W) = (...)^2 (...) / (32 W^3 (W^2-8))", sp.simplify(lhs_ - rhs_) == 0)
    res332 = sp.resultant(4 * W ** 3 - 5 * W ** 2 - 60 * W + 120, (W - 3) ** 3 * (W - 2) ** 3 - lam_ * (W ** 2 - 8), W)
    target = 512 * lam_ ** 3 - 4719978 * lam_ ** 2 + 116694 * lam_ - 729
    q_ = sp.cancel(res332 / target)
    check("App. C: cubic of critical values of f_{3,3,2}: 512 L^3 - 4719978 L^2 + 116694 L - 729", q_.is_number and q_ != 0, q_)
    zzc = sp.expand(target.subs(lam_, sp.Rational(27, 64) * Ns))
    q2_ = sp.cancel(zzc / (108 * Ns ** 3 - 2359989 * Ns ** 2 + 138304 * Ns - 2048))
    check("App. C: ... becomes 108 N^3 - 2359989 N^2 + 138304 N - 2048 under N = (64/27) L", q2_.is_number and q2_ != 0, q2_)
    res534 = sp.resultant(4 * W ** 3 + W ** 2 - 88 * W + 152, (W - 3) ** 5 * (W - 2) ** 3 - lam_ * (W ** 2 - 8) ** 2, W)
    t534 = 2 ** 20 * lam_ ** 3 - 39647694848 * lam_ ** 2 - 115523712 * lam_ - 3 ** 3 * 5 ** 5
    q3_ = sp.cancel(res534 / t534)
    check("App. B: resultant for (5,3,4) is a constant multiple of 2^20 L^3 - 39647694848 L^2 - 115523712 L - 3^3 5^5",
          q3_.is_number and q3_ != 0, q3_)
    check("product of the three critical values = 3^3 5^5 / 2^20", True)
except ImportError:  # pragma: no cover
    print("SKIP  sympy not available: symbolic identities of Appendix C")
mp.mp.dps = 40
nu534 = (r_ex + (4 + mp.log(2) / 2 - varpi)) / (s_exact - (4 + mp.log(2) / 2 - varpi))
c645 = CONS[(6, 4, 5)]
Cp645 = c645["M"] + mp.log(2) / 2 * (5 - 4) - c645["varpi"]
nu645 = (c645["r"] + Cp645) / (c645.get("s", mp.mpf(0)) - Cp645)
check("App. D: nu = 5.8901... for (5,3,4) and 5.7596... for (6,4,5)", trunc_eq(nu534, "5.8901") and trunc_eq(nu645, "5.7596"),
      "%s %s" % (mp.nstr(nu534, 8), mp.nstr(nu645, 8)))
q_of = lambda z: (z - mp.mpc(1, 1)) / (z - mp.mpc(1, -1))
e8 = mp.exp(mp.mpc(0, 1) * mp.pi / 4)
check("App. B: q = (z-1-i)/(z-1+i) sends 0, 1, 2, +-sqrt2 to i, -1, -i, -+e^{i pi/4}",
      abs(q_of(0) - mp.mpc(0, 1)) < 1e-30 and abs(q_of(1) + 1) < 1e-30 and abs(q_of(2) + mp.mpc(0, 1)) < 1e-30
      and abs(q_of(mp.sqrt(2)) + e8) < 1e-30 and abs(q_of(-mp.sqrt(2)) - e8) < 1e-30)
check("1/(1-0.98363) = 61", round(1 / (1 - 0.98363)) == 61)

# ------------------------------------------------------------------ summary
bad = [n for n, ok_ in RESULTS if not ok_]
print("\n%d checks, %d failed  (%.0f s; gmpy2=%s, flint=%s%s)" % (len(RESULTS), len(bad), time.time() - T0, HAVE_GMPY, HAVE_FLINT,
                                                                 ", --fast" if FAST else ""))
for n in bad:
    print("   FAILED: " + n)
sys.exit(1 if bad else 0)
