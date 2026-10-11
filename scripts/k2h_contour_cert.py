"""A-R653 E43: rigorous (interval arithmetic, mean-value form) certificate that on the polygon
   1 - i -> conj(z1) -> 1 -> z1 -> 1 + i   one has  log|f(z)| <= -s + tol,   z1 = the saddle of smallest modulus in Im z > 0.
On a segment z(t) = p + (q-p) t, t in [0,1], from the saddle p to a zero q of f of order e_q:
   phi(t) = log|f(z(t))|,  phi'(t) = e_q/(t-1) + sum_{j != q} c_j Re[(q-p)/(z(t)-zeta_j)].
Cell [t0,t1]:  phi <= phi(mid) + (t1-t0)/2 * sup|phi'|;  last cell: sup phi' < 0, so phi <= phi(t0)."""
import sys
from mpmath import mp, mpf, mpc, iv, polyroots, sqrt, log, fabs
def run(e1, e2, d, N):
    mp.dps = 40; iv.dps = 30
    a = e1 + e2 - d
    cub = [mpf(a), mpf(-(2*e1 + 3*e2 - 5*d)), mpf(-(8*e1 + 8*e2 + 6*d)), mpf(16*e1 + 24*e2)]
    roots = polyroots(cub, maxsteps=500, extraprec=400)
    r2 = sqrt(mpf(2))
    sing = [(e1, mpc(1, 0)), (e1, mpc(2, 0)), (e2, mpc(1, 1)), (e2, mpc(1, -1)), (-a, mpc(0, 0)), (-d, mpc(r2, 0)), (-d, mpc(-r2, 0))]
    lf = lambda z: sum(c*log(fabs(z - zeta)) for c, zeta in sing)
    cands = []
    for W in roots:
        if fabs(W.imag) < mpf(10)**(-30) and fabs(W) > sqrt(mpf(8)): continue
        for sg in (1, -1):
            z = (W + sg*sqrt(W*W - 8))/2
            if z.imag > 0: cands.append(z)
    s = -max(lf(z) for z in cands)
    z1 = sorted([z for z in cands if fabs(lf(z) + s) < mpf(10)**(-25)], key=lambda z: fabs(z))[0]
    worst = -mpf(10)**9
    for q, eq in ((mpc(1, 1), e2), (mpc(1, 0), e1)):
        p = z1; dx, dy = q.real - p.real, q.imag - p.imag
        others = [(c, zeta) for c, zeta in sing if fabs(zeta - q) > mpf(10)**(-20)]
        def dphi(T):
            x = iv.mpf(p.real) + iv.mpf(dx)*T; y = iv.mpf(p.imag) + iv.mpf(dy)*T
            tot = iv.mpf(eq)/(T - 1)
            for c, zeta in others:
                ax = x - iv.mpf(zeta.real); ay = y - iv.mpf(zeta.imag)
                tot += iv.mpf(c)*(iv.mpf(dx)*ax + iv.mpf(dy)*ay)/(ax*ax + ay*ay)
            return tot
        for k in range(N):
            t0, t1 = mpf(k)/N, mpf(k + 1)/N
            if k < N - 1:
                D = dphi(iv.mpf([t0, t1])); L = max(abs(D.a), abs(D.b))
                u = lf(p + (q - p)*(t0 + t1)/2) + (t1 - t0)/2*L
            else:
                D = dphi(iv.mpf([t0, t1 - mpf(10)**(-25)]))
                assert D.b < 0, "phi not decreasing on the last cell"
                u = lf(p + (q - p)*t0)
            if u > worst: worst = u
    return s, z1, worst
if __name__ == "__main__":
    e1, e2, d = (int(x) for x in sys.argv[1].split(",")); N = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
    s, z1, worst = run(e1, e2, d, N)
    print(f"K2H({e1},{e2},{d}): saddle z1 = {mp.nstr(z1, 20)}, s = {mp.nstr(s, 25)}")
    print(f"   certified: log|f| <= {mp.nstr(worst, 20)} on [z1,1+i] and [z1,1]  (N = {N});  excess over -s: {mp.nstr(worst + s, 5)}")
