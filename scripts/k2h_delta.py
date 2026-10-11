"""A-R653 E38: exact integer forms of K2H(e1,e2,d) with the THEOREM multiplier D_n = 2*lcm(1..Mn)/Phi_n and their sizes.
Prints log|v|/n, -log|J|/n, log D_n/n and delta_n = (-log|J| - log D)/(log|v| + log D); compare with r, s, C."""
import sys, math
from fractions import Fraction as Fr
from multiprocessing import Pool
sys.path.insert(0, "scripts")
from k2h import raw
from k2h_rule import bound
from sympy import primerange
from mpmath import mp, mpf, pi, log, fabs
def one(job):
    e1, e2, d, n = job
    M = max(e1 + e2 - d, d)
    u, r0, leak = raw((e1, 0, e2, 0, d), n)
    uu = Fr(int(u.p), int(u.q)); v = Fr(int(r0.p), int(r0.q))/2
    L = 1
    for k in range(2, M*n + 1): L = L*k//math.gcd(L, k)
    Phi = 1
    for p in primerange(3, M*n + 1):
        if p*p > M*n and (d*n//p) % 2 == 0 and (e1*n) % p + (e2*n) % p < (d*n) % p: Phi *= p
    Dn = 2*L//Phi
    ok = (uu*Dn).denominator == 1 and (v*Dn).denominator == 1 and leak == 0
    mp.dps = len(str(abs(v.numerator))) + int(0.6*(e1 + e2 + d)*n) + 80
    J = fabs(mpf(uu.numerator)/uu.denominator + mpf(v.numerator)/v.denominator*pi)
    lv, lJ, lD = float(log(fabs(mpf(v.numerator)/v.denominator)))/n, float(-log(J))/n, float(log(mpf(Dn)))/n
    return n, ok, lv, lJ, lD, (lJ - lD)/(lv + lD)
if __name__ == "__main__":
    e1, e2, d = (int(x) for x in sys.argv[1].split(",")); ns = [int(x) for x in sys.argv[2].split(",")]
    b = bound(e1, e2, d)
    mp.dps = 30
    print(f"K2H({e1},{e2},{d}): theory r = {float(b[1]):.5f}, s = {float(b[2]):.5f}, C = {float(b[3]):.5f}, delta = {float((b[2]-b[3])/(b[1]+b[3])):.5f}, mu = {float(b[0]):.6f}")
    with Pool(min(9, len(ns))) as p: res = p.map(one, [(e1, e2, d, n) for n in ns], chunksize=1)
    print("    n   integral   log|v|/n   -log|J|/n   log D/n    delta_n    1+1/delta_n")
    for n, ok, lv, lJ, lD, dl in res: print(f"  {n:4d}   {ok!s:6s}   {lv:9.4f}   {lJ:9.4f}   {lD:8.4f}   {dl:8.5f}   {1 + 1/dl:8.4f}")
