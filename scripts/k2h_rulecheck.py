"""A-R653 E37: exact test of the arithmetic claims for K2H(e1,e2,d) over a range of n (dn even):
 (1) v_n*2 integer;  (2) D_n*u_n integer with D_n = 2^g * lcm(1..Mn)/Phi_n, Phi_n = product of removable primes
     (p > sqrt(Mn), floor(dn/p) even, {e1 n/p}+{e2 n/p} < {dn/p});  g = the proven 2-adic allowance;
 (3) per prime: rule-removable primes never divide the denominator of u_n (violations must be 0); count extras."""
import sys, math
from fractions import Fraction as Fr
from multiprocessing import Pool
sys.path.insert(0, "scripts")
from k2h import raw
from sympy import primerange
def removable(e1, e2, d, n, p):
    D = d*n
    if (D//p) % 2: return False
    return (e1*n) % p + (e2*n) % p < D % p
def one(job):
    e1, e2, d, n = job
    M = max(e1 + e2 - d, d)
    u, r0, leak = raw((e1, 0, e2, 0, d), n)
    uu = Fr(int(u.p), int(u.q)); v = Fr(int(r0.p), int(r0.q))/2
    den = uu.denominator
    L = 1
    for k in range(2, M*n + 1): L = L*k//math.gcd(L, k)
    viol = extra = npred = 0
    Phi = 1
    for p in primerange(3, M*n + 1):
        if p*p <= M*n: continue
        pred = removable(e1, e2, d, n, p); absent = den % p != 0
        if pred:
            npred += 1; Phi *= p
            if not absent: viol += 1
        elif absent: extra += 1
    v2den = (den & -den).bit_length() - 1
    v2num = (abs(uu.numerator) & -abs(uu.numerator)).bit_length() - 1
    v2L = (L & -L).bit_length() - 1
    Dn = L//Phi
    ok_u = (uu*Dn).denominator == 1; ok_v = (2*v).denominator == 1; ok_v1 = v.denominator == 1
    big = max([p for p in primerange(M*n + 1, 4*M*n) if den % p == 0] or [0])
    return (n, leak == 0, ok_u, ok_v, ok_v1, viol, extra, npred, v2den - v2num if v2den else -v2num, v2L, big)
if __name__ == "__main__":
    e1, e2, d = (int(x) for x in sys.argv[1].split(",")); nlo, nhi = int(sys.argv[2]), int(sys.argv[3])
    step = 1 if d % 2 == 0 else 2
    if d % 2 and nlo % 2: nlo += 1
    with Pool(9) as p: res = p.map(one, [(e1, e2, d, n) for n in range(nlo, nhi + 1, step)], chunksize=1)
    print(f"K2H({e1},{e2},{d}), n in [{nlo},{nhi}] step {step}:  all zero-residue at ±sqrt2: {all(r[1] for r in res)};  (lcm(1..Mn)/Phi_n)*u_n integer for all n: {all(r[2] for r in res)};"
          f"  2*v_n integer: {all(r[3] for r in res)};  v_n integer: {all(r[4] for r in res)}")
    print(f"   rule violations (removable prime divides denominator): {sum(r[5] for r in res)} out of {sum(r[7] for r in res)} predicted;  extra absent primes: {sum(r[6] for r in res)};"
          f"  primes > Mn in denominator: {max(r[10] for r in res)}")
    print("   max 2-adic exponent of denominator of u_n (v2den), with v2(lcm):", [(r[0], r[8], r[9]) for r in res][::max(1, len(res)//10)])
    bad = [r[0] for r in res if not r[2]]
    if bad: print("   n where D_n*u_n is NOT an integer:", bad)
