"""A-R653 E27: asymptotic scan of K2H(e1,e2,d) with the BASELINE arithmetic C = M = max(e1+e2-d, d) (no savings, no 2-adic
gain assumed).  r = log|f| at the real saddle, s = -max log|f| over the non-real critical points.
f = [(z-1)(z-2)]^{e1}(z^2-2z+2)^{e2} / (z^{A}(z^2-2)^{d}), A = e1+e2-d."""
import sys, itertools
from mpmath import mp, mpf, mpc, log, fabs, polyroots
mp.dps = 30
def rates(e1, e2, d):
    e1, e2, d = mpf(e1), mpf(e2), mpf(d); A = e1 + e2 - d
    # numerator of f'/f over the common denominator z(z-1)(z-2)(z^2-2z+2)(z^2-2)
    def pmul(p, q):
        r = [mpf(0)]*(len(p) + len(q) - 1)
        for i, a in enumerate(p):
            for j, b in enumerate(q): r[i + j] += a*b
        return r
    def padd(p, q):
        n = max(len(p), len(q)); p = [mpf(0)]*(n - len(p)) + p; q = [mpf(0)]*(n - len(q)) + q
        return [a + b for a, b in zip(p, q)]
    z = [1, 0]; z1 = [1, -1]; z2 = [1, -2]; E = [1, -2, 2]; Q = [1, 0, -2]
    P = lambda *fs: __import__("functools").reduce(pmul, [[mpf(c) for c in f] for f in fs])
    num = [mpf(0)]
    num = padd(num, [e1*c for c in P([2, -3], z, E, Q)])           # e1*(2z-3)/((z-1)(z-2))
    num = padd(num, [e2*c for c in P([2, -2], z, z1, z2, Q)])      # e2*(2z-2)/E
    num = padd(num, [-A*c for c in P(z1, z2, E, Q)])               # -A/z
    num = padd(num, [-d*c for c in P([2, 0], z, z1, z2, E)])       # -d*2z/Q
    while len(num) > 1 and fabs(num[0]) < mpf(10)**(-25): num = num[1:]
    roots = polyroots(num, maxsteps=500, extraprec=300)
    lf = lambda w: e1*log(fabs((w-1)*(w-2))) + e2*log(fabs(w*w-2*w+2)) - A*log(fabs(w)) - d*log(fabs(w*w-2))
    real = [lf(w.real) for w in roots if fabs(w.imag) < mpf(10)**(-15)]
    cplx = [lf(w) for w in roots if fabs(w.imag) >= mpf(10)**(-15)]
    return (max(real) if real else None), (-max(cplx) if cplx else None), A
def mu0(e1, e2, d):
    r, s, A = rates(e1, e2, d)
    if r is None or s is None: return None
    M = max(A, d)
    return (1 + (r + M)/(s - M), r, s, M) if s - M > 0 else None
if __name__ == "__main__":
    if len(sys.argv) > 1:
        for t in sys.argv[1:]:
            e = [mpf(x) for x in t.split(",")]; print(t, [mp.nstr(x, 8) for x in mu0(*e)])
    else:
        res = []
        N = 40
        for i in range(1, 3*N + 1):
            for j in range(1, 3*N + 1):
                x, y = mpf(i)/N, mpf(j)/N               # e1/d, e2/d
                if x + y <= 1: continue
                try: m = mu0(x, y, 1)
                except Exception: m = None
                if m: res.append((float(m[0]), float(x), float(y), float(m[1]), float(m[2]), float(m[3])))
        res.sort()
        print("baseline bound (C = M) over e1/d, e2/d on a 1/40 grid; best 12: (mu, e1/d, e2/d, r, s, M)")
        for t in res[:12]: print("  %.4f  e1/d=%.3f e2/d=%.3f  r=%.4f s=%.4f M=%.3f" % t)
