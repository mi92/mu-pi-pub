"""A-R653 E34: INDEPENDENT exact evaluation of K2H(e1,e2,d) in the w-frame, over Q(sqrt2) (no Gaussian arithmetic, no z-frame
partial fractions).  eps = sqrt2-1, c = 1+eps^2 = 2 sqrt2 eps, tau = w^2+eps^2, T = 1-w^2 = c - tau.
  K_n = f.p. int_{-1}^{1} (1-w^2)^{E2} (1+eps^2 w^2)^{E1} w^{-2m} (w^2+eps^2)^{-A-1} dw = U + V*theta,  theta = 3 pi/(4 eps)
  J'_n = -(-1)^m 2^{(e2-2.5d)n+1} eps^{(e2-d)n+1} K_n = u_n - 3 v_n pi     (class of the path through z = -sqrt2)
so u_n = -(-1)^m 2^{(e2-2.5d)n+1} eps^{(e2-d)n+1} U,   v_n = (-1)^m 2^{(e2-2.5d)n-1} eps^{(e2-d)n} V.
Compares with the z-frame partial-fraction code (gen2/k2h.raw) and prints 2-adic valuations of the two parts."""
import sys
from fractions import Fraction as Fr
from math import comb
sys.path.insert(0, "scripts")
class Q2:                                        # a + b*sqrt2
    __slots__ = ("a", "b")
    def __init__(s, a=0, b=0): s.a, s.b = Fr(a), Fr(b)
    def __add__(s, o): o = o if isinstance(o, Q2) else Q2(o); return Q2(s.a + o.a, s.b + o.b)
    __radd__ = __add__
    def __neg__(s): return Q2(-s.a, -s.b)
    def __sub__(s, o): o = o if isinstance(o, Q2) else Q2(o); return Q2(s.a - o.a, s.b - o.b)
    def __mul__(s, o):
        if not isinstance(o, Q2): return Q2(s.a*o, s.b*o)
        return Q2(s.a*o.a + 2*s.b*o.b, s.a*o.b + s.b*o.a)
    __rmul__ = __mul__
    def inv(s):
        nrm = s.a*s.a - 2*s.b*s.b; return Q2(s.a/nrm, -s.b/nrm)
    def __truediv__(s, o): o = o if isinstance(o, Q2) else Q2(o); return s*o.inv()
    def __pow__(s, k):
        if k < 0: return s.inv()**(-k)
        r = Q2(1); base = s
        while k:
            if k & 1: r = r*base
            base = base*base; k >>= 1
        return r
    def __eq__(s, o): o = o if isinstance(o, Q2) else Q2(o); return s.a == o.a and s.b == o.b
    def __repr__(s): return f"({s.a} + {s.b}*r2)"
def v2r(x):
    if x == 0: return None
    n, d = abs(x.numerator), x.denominator
    return (n & -n).bit_length() - 1 - ((d & -d).bit_length() - 1)
def v2(x):                                       # 2-adic valuation on Q(sqrt2), v(sqrt2) = 1/2
    va, vb = v2r(x.a), v2r(x.b)
    c = [t for t in (va, None if vb is None else vb + Fr(1, 2)) if t is not None]
    return min(c) if c else None
EPS = Q2(-1, 1); EPS2 = EPS*EPS; C = Q2(1) + EPS2
def binom_neg(k, j):                             # C(-k, j) = (-1)^j C(k+j-1, j)
    return (-1)**j*comb(k + j - 1, j)
def M_table(kmax):
    """M_i = int_{-1}^{1} (w^2+eps^2)^{-i} dw = alpha_i + beta_i*theta;  M_{i+1} = 1/(i eps^2 c^i) + (2i-1)/(2i eps^2) M_i."""
    al = {1: Q2(0)}; be = {1: Q2(1)}; e2i = EPS2.inv(); ci = Q2(1)
    for i in range(1, kmax):
        ci = ci*C
        al[i + 1] = (e2i/ci)*Fr(1, i) + al[i]*e2i*Fr(2*i - 1, 2*i); be[i + 1] = be[i]*e2i*Fr(2*i - 1, 2*i)
    return al, be
def K(e1, e2, d, n):
    E1, E2, A, m = e1*n, e2*n, (e1 + e2 - d)*n, d*n//2
    assert d*n % 2 == 0
    # numerator as a polynomial in tau: (c - tau)^{E2} * (c(1-eps^2) + eps^2 tau)^{E1}
    g = C*(Q2(1) - EPS2)
    p1 = [C**(E2 - j)*((-1)**j*comb(E2, j)) for j in range(E2 + 1)]
    p2 = [g**(E1 - j)*EPS2**j*comb(E1, j) for j in range(E1 + 1)]
    nu = [Q2(0)]*(E1 + E2 + 1)
    for i, x in enumerate(p1):
        for j, y in enumerate(p2): nu[i + j] = nu[i + j] + x*y
    al, be = M_table(A + 2)
    U1 = Q2(0); U2 = Q2(0); V = Q2(0)                    # part 1 (l >= 0), part 2 rational, part 2 theta
    e2pow = {}
    for idx, coef in enumerate(nu):
        l = idx - A - 1
        if coef == 0: continue
        if l >= 0:                                       # X_l = sum_i C(l,i) eps^{2(l-i)} * 2/(2i-2m+1)
            X = Q2(0)
            for i in range(l + 1): X = X + EPS2**(l - i)*(comb(l, i)*Fr(2, 2*i - 2*m + 1))
            U1 = U1 + coef*X
        else:
            k = -l
            Xr = Q2(0)
            for i in range(1, m + 1): Xr = Xr + EPS2**(-(k + m - i))*(binom_neg(k, m - i)*Fr(2, 1 - 2*i))
            Xt = Q2(0)
            for i in range(1, k + 1):
                b = (-EPS2)**(-(m + k - i))*binom_neg(m, k - i)
                Xr = Xr + b*al[i]; Xt = Xt + b*be[i]
            U2 = U2 + coef*Xr; V = V + coef*Xt
    return U1, U2, V, m
def forms(e1, e2, d, n):
    U1, U2, V, m = K(e1, e2, d, n)
    sg = (-1)**m
    pw = Fr(2)**((2*e2 - 5*d)*n//2)
    u = (U1 + U2)*EPS**((e2 - d)*n + 1)*(-sg*pw*2)
    v = V*EPS**((e2 - d)*n)*(sg*pw/2)
    return u, v, (U1, U2, V, pw, m)
if __name__ == "__main__":
    from k2h import raw
    e1, e2, d = (int(x) for x in sys.argv[1].split(",")); ns = [int(x) for x in sys.argv[2].split(",")]
    for n in ns:
        u, v, (U1, U2, V, pw, m) = forms(e1, e2, d, n)
        uz, r0, leak = raw((e1, 0, e2, 0, d), n)
        uz = Fr(int(uz.p), int(uz.q)); vz = Fr(int(r0.p), int(r0.q))/2
        print(f"n={n}: w-frame u rational: {u.b == 0}, v rational: {v.b == 0};  u matches z-frame: {u.a == uz}, v matches: {v.a == vz}")
        base = v2r(pw) + 1
        print(f"     2-adic: v(const) = {base};  v(part1) = {v2(U1)}, v(part2 rational) = {v2(U2)}, v(part2 theta-coefficient) = {v2(V)};  3m = {3*m};"
              f"  v2(u_n) = {v2r(u.a)}, v2(v_n) = {v2r(v.a)}")
