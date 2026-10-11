"""A-R653: 40-digit constants for the headline triples (rule-based bound function)."""
import sys
from mpmath import mp, mpf, log, digamma, polyroots, fabs, sqrt, findroot, pi
mp.dps = 45
sys.path.insert(0, "scripts")
from k2h_rule import window, slope2
from fractions import Fraction as Fr
def consts(e1, e2, d):
    a = e1 + e2 - d; M = max(a, d)
    cub = [mpf(a), mpf(-(2*e1 + 3*e2 - 5*d)), mpf(-(8*e1 + 8*e2 + 6*d)), mpf(16*e1 + 24*e2)]
    roots = polyroots(cub, maxsteps=500, extraprec=400)
    lF = lambda W: (2*e1*log(fabs(W - 3)) + 2*e2*log(fabs(W - 2)) - d*log(fabs(W*W - 8)))/2
    r8 = sqrt(mpf(8))
    real = [W.real for W in roots if fabs(W.imag) < mpf(10)**(-35)]
    r = [lF(W) for W in real if fabs(W) > r8][0]
    others = [W for W in roots if not (fabs(W.imag) < mpf(10)**(-35) and fabs(W) > r8)]
    s = -max(lF(W) for W in others)
    cut = Fr(1, M); sav = mpf(0)
    for lo, hi in window(e1, e2, d):
        sav += (digamma(mpf(hi.numerator)/hi.denominator/2 + 1) - digamma(mpf(lo.numerator)/lo.denominator/2 + 1))/2
        if hi > cut:
            a0 = max(lo, cut); sav += mpf(a0.denominator)/a0.numerator - mpf(hi.denominator)/hi.numerator
    sl = slope2(e2, d)
    C = M + mpf(sl.numerator)/sl.denominator*log(2) - sav
    return cub, roots, r, s, sav, C, 1 + (r + C)/(s - C), 1 + (r + M)/(s - M) if s > M else None
for t in sys.argv[1:]:
    e1, e2, d = (int(x) for x in t.split(","))
    cub, roots, r, s, sav, C, mu, mu0 = consts(e1, e2, d)
    print(f"K2H({e1},{e2},{d}): cubic {[int(c) for c in cub]}")
    print("   critical W:", [mp.nstr(W, 20) for W in roots])
    print("   r      =", mp.nstr(r, 40)); print("   s      =", mp.nstr(s, 40)); print("   saving =", mp.nstr(sav, 40)); print("   C      =", mp.nstr(C, 40))
    print("   mu     =", mp.nstr(mu, 40), "   (without prime saving:", mp.nstr(mu0, 20) if mu0 else None, ")")
    print("   windows on [0,2):", [(str(a), str(b)) for a, b in window(e1, e2, d)])
