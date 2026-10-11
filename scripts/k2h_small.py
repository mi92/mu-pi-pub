import sys, math
from fractions import Fraction as Fr
sys.path.insert(0, "scripts")
from k2h import raw
from sympy import primerange, factorint
from mpmath import mp, mpf, pi
e1, e2, d = (int(x) for x in sys.argv[1].split(",")); ns = [int(x) for x in sys.argv[2].split(",")]
M = max(e1 + e2 - d, d)
for n in ns:
    u, r0, leak = raw((e1, 0, e2, 0, d), n)
    uu = Fr(int(u.p), int(u.q)); v = Fr(int(r0.p), int(r0.q))/2
    L = 1
    for k in range(2, M*n + 1): L = L*k//math.gcd(L, k)
    Phi = 1
    for p in primerange(3, M*n + 1):
        if p*p > M*n and (d*n//p) % 2 == 0 and (e1*n) % p + (e2*n) % p < (d*n) % p: Phi *= p
    Dn = L//Phi
    P, Q = uu*Dn, v*Dn
    mp.dps = 60
    lam = mpf(P.numerator)/P.denominator + mpf(Q.numerator)/Q.denominator*pi
    print(f"n={n}: u_n = {uu}, v_n = {v}; lcm(1..{M*n}) = {L}, Phi_n = {Phi}, D_n = {Dn};  D_n*J_n = {P} + {Q}*pi = {mp.nstr(lam, 12)}")
    print(f"      den(u_n) = {dict(factorint(uu.denominator))}")
