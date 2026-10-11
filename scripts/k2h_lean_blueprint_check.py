"""Exact check (in Q(sqrt2)) of the explicit w-frame decomposition that the Lean proof of the 2-adic
part formalises.  Triple (5,3,4): E1=5n, E2=3n, A=4n, m=2n, G=n.
   k_n(w) = c^{2m-1} * sum_i C(E1,i) (2 eps)^i * x^{E2+i} (1-x)^{G-1-i} w^{-2m},   x=(1-w^2)/c
   u_n = -2 eps (128 eps)^{-n} U,   c_n = (128 eps)^{-n} V
Also prints the 2-adic valuations of every group of terms against the bounds used in the proof."""
from fractions import Fraction as F
from math import comb
import sys

class Q2:                       # a + b*sqrt2
    __slots__ = ("a", "b")
    def __init__(s, a=0, b=0): s.a, s.b = F(a), F(b)
    def __add__(s, o): o = o if isinstance(o, Q2) else Q2(o); return Q2(s.a+o.a, s.b+o.b)
    __radd__ = __add__
    def __neg__(s): return Q2(-s.a, -s.b)
    def __sub__(s, o): o = o if isinstance(o, Q2) else Q2(o); return Q2(s.a-o.a, s.b-o.b)
    def __rsub__(s, o): return Q2(o) - s
    def __mul__(s, o):
        o = o if isinstance(o, Q2) else Q2(o); return Q2(s.a*o.a+2*s.b*o.b, s.a*o.b+s.b*o.a)
    __rmul__ = __mul__
    def inv(s): d = s.a*s.a-2*s.b*s.b; return Q2(s.a/d, -s.b/d)
    def __truediv__(s, o): o = o if isinstance(o, Q2) else Q2(o); return s*o.inv()
    def __rtruediv__(s, o): return Q2(o)*s.inv()
    def __pow__(s, k):
        if k < 0: return s.inv()**(-k)
        r = Q2(1)
        for _ in range(k): r = r*s
        return r
    def iszero(s): return s.a == 0 and s.b == 0
    def __repr__(s): return f"({s.a} + {s.b}*sqrt2)"

def v2q(q):
    if q == 0: return 10**9
    n, d, v = q.numerator, q.denominator, 0
    while n % 2 == 0: n //= 2; v += 1
    while d % 2 == 0: d //= 2; v -= 1
    return v
def val(x):                     # valuation in units of 1/2  (v(sqrt2)=1)
    if x.iszero(): return 10**9
    return v2q(x.a*x.a - 2*x.b*x.b)   # norm has v = 2*v(x); in half-units that is v(norm)

s = Q2(0, 1); eps = s - 1; c = 1 + eps*eps
assert (c - 2*s*eps).iszero()

def run(n):
    E1, E2, A, m, G = 5*n, 3*n, 4*n, 2*n, n
    L = (4*n).bit_length() - 1
    dB = {}
    def DB(a):
        if a not in dB:
            dB[a] = c**(-a) * 2 * sum(F(comb(a, i)*(-1)**i, 2*i-2*m+1) for i in range(a+1))
        return dB[a]
    alpha, beta = {1: Q2(0)}, {1: Q2(1)}
    for i in range(1, A+2):
        alpha[i+1] = (2*c**(-i) + (2*i-1)*alpha[i]) / (2*i*eps*eps)
        beta[i+1] = (2*i-1)*beta[i] / (2*i*eps*eps)
    R, S = {}, {}
    for mm in range(0, m+1):
        for k in range(0, A+2):
            if k == 0: R[mm, k], S[mm, k] = Q2(F(2, 1-2*mm)), Q2(0)
            elif mm == 0: R[mm, k], S[mm, k] = alpha[k], beta[k]
            else:
                R[mm, k] = (R[mm, k-1] - R[mm-1, k]) / (eps*eps)
                S[mm, k] = (S[mm, k-1] - S[mm-1, k]) / (eps*eps)
    U, V = Q2(0), Q2(0)
    minT1 = minT2 = minT3 = minT4 = 10**9
    for i in range(E1+1):
        coef = comb(E1, i) * (2*eps)**i
        if i < G:
            for b in range(G-1-i+1):
                t = coef * comb(G-1-i, b) * (-1)**b * DB(E2+i+b)
                minT1 = min(minT1, val(t)); U = U + t
        else:
            N, j = E2+i, i-G+1
            for l in range(N+1):
                cc = coef * comb(N, l) * (-1)**l
                if l >= j:
                    for b in range(l-j+1):
                        t = cc * comb(l-j, b) * (-1)**b * DB(b)
                        minT2 = min(minT2, val(t)); U = U + t
                else:
                    k = j-l
                    t = cc * c**k * R[m, k]; minT3 = min(minT3, val(t)); U = U + t
                    t = cc * c**k * S[m, k]; minT4 = min(minT4, val(t)); V = V + t
    U = c**(2*m-1) * U; V = c**(2*m-1) * V
    un = -2*eps * (128*eps)**(-n) * U
    cn = (128*eps)**(-n) * V
    assert un.b == 0 and cn.b == 0, (un, cn)
    # bounds used (half units): T1 >= 2G+1-2L ; T2 >= 2G+1 ; T3,T4 >= 2G+3
    print(f"n={n}: u_n={un.a}  c_n={cn.a}   v2(u_n)={v2q(un.a)} (need >= {-L})  v2(c_n)={v2q(cn.a)}")
    print(f"      half-unit minima: T1={minT1} (bound {2*G+1-2*L})  T2={minT2} (bound {2*G+1})"
          f"  T3={minT3} (bound {2*G+3})  T4={minT4} (bound {2*G+3})")
    assert minT1 >= 2*G+1-2*L and minT2 >= 2*G+1 and minT3 >= 2*G+3 and minT4 >= 2*G+3
    # lemma-level checks
    for a in range(0, 2*m): assert val(DB(a)) >= a + 2 - 2*bin(a).count("1"), a
    for i in range(1, A+2):
        assert val(alpha[i]) >= -4*(i-1) and val(beta[i]) >= -4*(i-1), i
    for k in range(1, A+2):
        assert val(c**k*R[m, k]) >= 4-k and val(c**k*S[m, k]) >= 4-k, k
    return un.a, cn.a

for n in range(1, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 5):
    u, cc = run(n)
    if n == 1: assert (u, cc) == (F(-23075, 2), F(7345)), (u, cc)
print("OK")
