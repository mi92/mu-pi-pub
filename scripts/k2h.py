"""A-R653 E25: family K2H.  Omega = N(z)^n dz / ( z^A (z^2-2)^{d n} ),
N = [(z-1)(z-2)]^{e1} [(z+1)(z+2)]^{e3} (z^2-2z+2)^{e2} (z^2+2z+2)^{e4} (and (z^2-2)^{-d} in the numerator if d<0),
A = (deg N * n - 2 d n)/2 + 1  (equal pole orders at 0 and infinity; symmetry z -> 2/z).  Path 1-i -> 1+i."""
import sys, itertools, math, json
from math import gcd
from fractions import Fraction as Fr
from multiprocessing import Pool
sys.path.insert(0, "scripts")
from flint import fmpz_poly
from gen2 import forms2
from mpmath import mp, mpf, pi, log, fabs
def raw(par, n):
    e1, e3, e2, e4, d = par
    N = (fmpz_poly([-1, 1])*fmpz_poly([-2, 1]))**(e1*n) * (fmpz_poly([1, 1])*fmpz_poly([2, 1]))**(e3*n) \
        * fmpz_poly([2, -2, 1])**(e2*n) * fmpz_poly([2, 2, 1])**(e4*n)
    dd = max(d, 0)*n
    if d < 0: N = N * fmpz_poly([-2, 0, 1])**(-d*n)
    Z = N.degree(); 
    if (Z - 2*dd) % 2 or Z - 2*dd < 0: return None
    A = (Z - 2*dd)//2 + 1
    return forms2(N, A, (-2, 1), dd, (1, 1))
def profile(par, n):
    out = raw(par, n)
    if out is None: return None
    u, r0, leak = out
    if leak != 0 or r0 == 0: return None
    uu = Fr(int(u.p), int(u.q)); best = None
    for fac in (Fr(1, 2), Fr(-3, 2)):
        v = Fr(int(r0.p), int(r0.q))*fac
        L = math.lcm(uu.denominator, v.denominator); U = int(uu*L); V = int(v*L); g = gcd(U, V)
        mp.dps = int(len(str(abs(V)))*1.1) + 60
        J = fabs(mpf(U) + mpf(V)*pi)/g; Vg = mpf(abs(V))/g
        if Vg < 2 or J == 0 or J >= 1: continue
        lJ, lV, lD = float(log(J)), float(log(Vg)), float(log(mpf(L)/g))
        if best is None or -lJ/lV > best[0]: best = (-lJ/lV, lJ, lV, lD)
    return best
def work(job):
    par, deg = job
    size = 2*(par[0] + par[1] + par[2] + par[3]) + 2*max(-par[4], 0); n0 = max(2, round(deg/size)); n0 += n0 % 2
    ds = []
    for n in (n0, n0 + 2):
        try: b = profile(par, n)
        except Exception as ex: b = None
        ds.append(-1.0 if b is None else b[0])
    return (min(ds), sum(ds)/2, par, n0)
if __name__ == "__main__":
    if sys.argv[1] == "search":
        deg = int(sys.argv[2])
        jobs = [((e1, e3, e2, e4, d), deg) for e1 in range(0, 5) for e3 in range(0, 3) for e2 in range(1, 5) for e4 in range(0, 3)
                for d in range(-2, 6) if d < e1 + e3 + e2 + e4 and math.gcd(e1, e3, e2, e4, abs(d)) == 1]
        print(len(jobs), "candidates", flush=True)
        with Pool(9) as p: res = sorted(p.map(work, jobs, chunksize=6), reverse=True)
        json.dump(res, open(f"e25_k2h_deg{deg}.json", "w"))
        print("top 20 (min delta, avg, (e1 {1,2}, e3 {-1,-2}, e2 {1+-i}, e4 {-1+-i}, d), n0):")
        for r in res[:20]: print(f"  {r[0]:.4f} {r[1]:.4f}  {tuple(r[2])}  n0={r[3]}")
    else:
        par = tuple(int(x) for x in sys.argv[2].split(",")); ns = [int(x) for x in sys.argv[3].split(",")]
        print("par", par, "   n  delta   (log|J|-logD)/n  (log|V|-logD)/n  logD/n")
        for n in ns:
            b = profile(par, n)
            print(f"   {n:4d}  " + ("None" if b is None else f"{b[0]:.5f}  {(b[1]-b[3])/n:8.4f}  {(b[2]-b[3])/n:8.4f}  {b[3]/n:7.4f}"), flush=True)
