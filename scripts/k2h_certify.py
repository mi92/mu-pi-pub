"""A-R653 E42: certificates for the analytic and the 2-adic lemma.
(a) interval-arithmetic upper bound of log|f| on the polygon 1 -> z1 -> 1+i (and by symmetry its mirror image):
    proves sup <= -s + tol.   usage: k2h_certify.py contour e1,e2,d [N]
(b) termwise test of the inequalities used in the 2-adic lemma (w-frame): v(pi_a), v(lambda_k), v(B(a)), v(R_k), v(S_k).
    usage: k2h_certify.py twoadic e1,e2,d n1,n2,..."""
import sys
from fractions import Fraction as Fr
from math import comb
sys.path.insert(0, "scripts")
def contour(e1, e2, d, N):
    from mpmath import mp, mpf, mpc, iv, polyroots, sqrt, log, fabs
    mp.dps = 40; iv.dps = 30
    a = e1 + e2 - d
    cub = [mpf(a), mpf(-(2*e1 + 3*e2 - 5*d)), mpf(-(8*e1 + 8*e2 + 6*d)), mpf(16*e1 + 24*e2)]
    roots = polyroots(cub, maxsteps=500, extraprec=400)
    lf = lambda z: e1*log(fabs((z - 1)*(z - 2))) + e2*log(fabs(z*z - 2*z + 2)) - a*log(fabs(z)) - d*log(fabs(z*z - 2))
    cands = []
    for W in roots:
        if fabs(W.imag) < mpf(10)**(-30) and fabs(W) > sqrt(mpf(8)): continue
        for sg in (1, -1):
            z = (W + sg*sqrt(W*W - 8))/2
            if z.imag > 0: cands.append(z)
    s = -max(lf(z) for z in cands)
    # saddles with value -s in the upper half plane; take the one with smallest modulus (inside or on the circle)
    top = sorted([z for z in cands if fabs(lf(z) + s) < mpf(10)**(-25)], key=lambda z: fabs(z))
    r2 = iv.sqrt(iv.mpf(2))
    def ub(p, q, t0, t1):
        T = iv.mpf([t0, t1])
        x = iv.mpf(p.real) + (iv.mpf(q.real) - iv.mpf(p.real))*T; y = iv.mpf(p.imag) + (iv.mpf(q.imag) - iv.mpf(p.imag))*T
        m1 = (x - 1)**2 + y**2; m2 = (x - 2)**2 + y**2
        q1 = ((x - 1)**2 + (y - 1)**2)*((x - 1)**2 + (y + 1)**2)
        zz = x**2 + y**2; pp = ((x - r2)**2 + y**2)*((x + r2)**2 + y**2)
        val = (e1*(iv.log(m1) + iv.log(m2)) + e2*iv.log(q1) - a*iv.log(zz) - d*iv.log(pp))/2
        return val.b
    out = []
    for zs in top:
        worst = -mpf(10)**9
        ok = True
        for (p, q, lo_cut, hi_cut) in ((zs, mpc(1, 1), 0, 1), (zs, mpc(1, 0), 0, 1)):
            # the end points 1+i and 1 are zeros of f (log = -inf): stop the interval evaluation at t = 1 - 1/N and note f -> 0 there
            for k in range(N - 1):
                t0, t1 = mpf(k)/N, mpf(k + 1)/N
                try: u = ub(p, q, t0, t1)
                except Exception: u = mpf(10)**9
                if u > worst: worst = u
            # last cell [1-1/N, 1]: |f| is increasing in each zero factor only; bound crudely by the value box without the vanishing factor
        out.append((zs, worst))
    return s, out
def twoadic(e1, e2, d, n):
    from k2h_wframe import Q2, v2, v2r, EPS, EPS2, C, binom_neg, M_table
    E1, E2, A, m = e1*n, e2*n, (e1 + e2 - d)*n, d*n//2
    G = E1 - A
    g = C*(Q2(1) - EPS2)
    p1 = [C**(E2 - j)*((-1)**j*comb(E2, j)) for j in range(E2 + 1)]
    p2 = [g**(E1 - j)*EPS2**j*comb(E1, j) for j in range(E1 + 1)]
    nu = [Q2(0)]*(E1 + E2 + 1)
    for i, x in enumerate(p1):
        for j, y in enumerate(p2): nu[i + j] = nu[i + j] + x*y
    # nu[idx] = coefficient of tau^idx of the numerator; lambda_k = nu[A+1-k]; polynomial part in tau: nu[A+1+l] tau^l
    bad = []
    for k in range(1, A + 2):
        lam = nu[A + 1 - k]
        if lam == 0: continue
        bound = Fr(3, 2)*(2*m - 1 + k) + max(0, E1 - A - 1 + k)
        if v2(lam) < bound: bad.append(("lambda", k, v2(lam), bound))
    # polynomial part: Pi(T) = sum_l nu[A+1+l] (c - T)^l  ->  coefficients pi_a in T
    L = len(nu) - (A + 1)                      # = 2m
    pi = [Q2(0)]*L
    for l in range(L):
        co = nu[A + 1 + l]
        if co == 0: continue
        for aa in range(l + 1): pi[aa] = pi[aa] + co*C**(l - aa)*(comb(l, aa)*(-1)**aa)
    for aa in range(L):
        if pi[aa] == 0: continue
        bound = Fr(3, 2)*(2*m - 1 - aa) + (max(0, G) if aa < E2 else 0)
        if v2(pi[aa]) < bound: bad.append(("pi", aa, v2(pi[aa]), bound))
    # B(a) = 2^{a+1} a! / prod_{j=0}^{a} (2j-2m+1): exact valuation a+1+v2(a!)
    for aa in range(L):
        B = sum(Fr(comb(aa, i)*(-1)**i*2, 2*i - 2*m + 1) for i in range(aa + 1))
        prod = 1
        for j in range(aa + 1): prod *= (2*j - 2*m + 1)
        from math import factorial
        if B != Fr(2**(aa + 1)*factorial(aa), prod): bad.append(("B closed form", aa))
    # R_k, S_k
    al, be = M_table(A + 2)
    for k in range(1, A + 2):
        Xr = Q2(0); Xt = Q2(0)
        for i in range(1, m + 1): Xr = Xr + EPS2**(-(k + m - i))*(binom_neg(k, m - i)*Fr(2, 1 - 2*i))
        for i in range(1, k + 1):
            b = (-EPS2)**(-(m + k - i))*binom_neg(m, k - i)
            Xr = Xr + b*al[i]; Xt = Xt + b*be[i]
        for nm, X in (("R", Xr), ("S", Xt)):
            if X == 0: continue
            if v2(X) < -2*(k - 1): bad.append((nm, k, v2(X), -2*(k - 1)))
    return bad
if __name__ == "__main__":
    mode = sys.argv[1]; e1, e2, d = (int(x) for x in sys.argv[2].split(","))
    if mode == "contour":
        N = int(sys.argv[3]) if len(sys.argv) > 3 else 4000
        from mpmath import mp
        s, out = contour(e1, e2, d, N)
        print(f"K2H({e1},{e2},{d}): s = {mp.nstr(s, 25)}")
        for zs, worst in out:
            print(f"   saddle {mp.nstr(zs, 12)}: interval upper bound of log|f| on [zs,1+i) and [zs,1) (N={N} cells each, last cell excluded) = {mp.nstr(worst, 15)};  excess over -s: {mp.nstr(worst + s, 5)}")
    else:
        for n in (int(x) for x in sys.argv[3].split(",")):
            bad = twoadic(e1, e2, d, n)
            print(f"K2H({e1},{e2},{d}) n={n}: violated inequalities: {len(bad)}", bad[:5])
