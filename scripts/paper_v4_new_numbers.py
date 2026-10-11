#!/usr/bin/env python3
"""
Recompute the numbers that were ADDED in paper/K2H_paper_v4.tex (version 4, 5 October 2026).
All numbers that version 4 shares with version 3 are checked by scripts/paper_v3_numbers.py.

    python scripts/paper_v4_new_numbers.py            # all checks (about a minute)
    python scripts/paper_v4_new_numbers.py --data     # also print the coordinates of Figure 2

Every check prints PASS/FAIL; the exit status is non-zero if a check fails.

Checked here:
  * Section 1.2: the exponents 7.1032 and 6.0446 obtained from the rounded rates sigma, tau.
  * Section 1.4: the previous improvement (0.0013) and the step to 6.0446 (about 800 times larger).
  * Table 3 and Remark 9.1: the exact rates, and that they recompute at the printed precision.
  * Figure 1: inside/outside the circle |z| = sqrt 2, and the positions of 2/z_1 and 2/conj(z_1).
  * Section 1.3: without removable primes (multiplier lcm(1..4n)) the rates of Table 3 give about 6.747.
  * Remark 1.7: J_1 for the triples (2,2,2), (3,3,2), (5,3,4) (exact, by symbolic integration);
    355/113 and 22/7 (decimal digits, best approximations below 16604 and 57); Dalzell's and Lucas's integrals;
    the approximation -u_2/v_2 and its error.
  * Section 4.1: -i * int dz/z over the segment = pi/2.
  * Remark 4.4: the partial fractions of 1/(z(z^2-2)).
  * Appendix A.1: the two worked instances of (4.5).
  * Figure 2: log10 |J_n| (quadrature along the polygon of Section 7, independent of the exact forms) and
    log10 v_n (power-series coefficient c_n = 2 v_n), n = 1..60, and the bound 4 rho^n.
"""
import sys
import time
from math import gcd

import mpmath as mp
import sympy as sp

RESULTS = []
T0 = time.time()


def check(name, cond, detail=""):
    RESULTS.append((name, bool(cond)))
    print(("PASS  " if cond else "FAIL  ") + name + (("   [" + str(detail) + "]") if detail else ""), flush=True)


def section(title):
    print("\n== " + title + "  (t=%.1fs) ==" % (time.time() - T0), flush=True)


z, x = sp.symbols("z x")
mp.mp.dps = 40

# ---------------------------------------------------------------- Section 1.2
section("rates -> exponents (Section 1.2)")
zz = 1 + mp.mpf("11.6138") / mp.mpf("1.9029")
check("ZZ: 1 + 11.6138/1.9029 = 7.1032...", mp.nstr(zz, 5) == "7.1032", mp.nstr(zz, 10))
ours = 1 + mp.mpf("14.2464") / mp.mpf("2.82409")
check("ours: 1 + 14.2464/2.82409 < 6.0446", ours < mp.mpf("6.0446"), mp.nstr(ours, 10))
check("sigma larger, tau larger than ZZ", 14.2464 > 11.6138 and 2.82409 > 1.9029)
# Section 1.4 (a): the step to 6.0446 compared with the previous improvement 7.1032 -> 7.1019
zz, bai = mp.mpf("7.103205334137"), mp.mpf("7.101862832357")
check("previous improvement 7.1032 -> 7.1019 lowered the bound by 0.0013", mp.nstr(zz - bai, 2) == "0.0013", mp.nstr(zz - bai, 6))
ratio = (bai - mp.mpf("6.0446")) / (zz - bai)
ratio_printed = (mp.mpf("7.1019") - mp.mpf("6.0446")) / mp.mpf("0.0013")
check("the step from 7.1019 to 6.0446 is about 800 times larger (exact differences and printed numbers)",
      abs(ratio - 800) < 30 and abs(ratio_printed - 800) < 30, (mp.nstr(ratio, 5), mp.nstr(ratio_printed, 5)))

# Table 3: the exact values, printed with ten decimals, are truncations of the exact rates
mp.mp.dps = 50
roots = mp.polyroots([2 ** 20, -39647694848, -115523712, -27 * 3125], maxsteps=200, extraprec=200)
lam3 = max([x for x in roots if abs(mp.im(x)) < 1e-30], key=lambda x: mp.re(x))
cpx = [x for x in roots if abs(mp.im(x)) > 1e-30][0]
r_x, s_x = mp.log(mp.re(lam3)), -mp.log(abs(cpx))
w_x = mp.nsum(lambda k: 1 / ((3 * k + 2) * (4 * k + 3)), [0, mp.inf]) + mp.nsum(lambda k: 1 / ((4 * k + 1) * (5 * k + 1)), [1, mp.inf])
C_x = 4 - w_x
T = lambda x, d: mp.nstr(mp.floor(x * 10 ** d) / 10 ** d, d + 4)
sg_x, ta_x = r_x + C_x, s_x - C_x
mu_x = 1 + sg_x / ta_x
tab3 = [("10.540355111696", r_x, 12), ("6.53013614736", s_x, 12), ("3.706040100783", C_x, 12),
        ("14.2463952124", sg_x, 10), ("2.8240960465", ta_x, 10), ("6.04458594", mu_x, 8)]
check("Table 3 exact column: r, s, C (12 decimals), sigma, tau (10), 1+sigma/tau (8) are truncations of the exact values",
      all(T(v, d) == txt for txt, v, d in tab3), [(txt, T(v, d)) for txt, v, d in tab3])
pr = lambda txt: mp.mpf(txt)
check("Table 3 recomputes at the printed precision: r+C -> sigma, s-C -> tau, 1+sigma/tau -> mu",
      T(pr("10.540355111696") + pr("3.706040100783"), 10) == "14.2463952124"
      and T(pr("6.53013614736") - pr("3.706040100783"), 10) == "2.8240960465"
      and T(1 + pr("14.2463952124") / pr("2.8240960465"), 8) == "6.04458594")
check("Remark 9.1: 1 + 14.2463952124/2.8240960465 = 6.04458594..., as in Table 3",
      T(1 + pr("14.2463952124") / pr("2.8240960465"), 8) == "6.04458594")
mp.mp.dps = 40

# Figure 1: z_s and z_1 inside the circle |z| = sqrt 2, the images 2/z_1 and 2/conj(z_1) outside
zs = mp.mpc(mp.mpf(19787) / 16384, mp.mpf(32371) / 65536)
z1 = mp.mpc("1.2077099", "0.4939472")
im1, im2 = 2 / mp.conj(z1), 2 / z1
check("Figure 1: |z_s| < sqrt2 < |2/z_1|; 2/conj(z_1) = 1.4187 + 0.5802 i (upper square), 2/z_1 = 1.4187 - 0.5802 i",
      abs(zs) < mp.sqrt(2) < abs(im2) and mp.nstr(mp.re(im1), 5) == "1.4187" and mp.nstr(mp.im(im1), 4) == "0.5802"
      and mp.nstr(mp.im(im2), 4) == "-0.5802", (mp.nstr(abs(zs), 5), mp.nstr(abs(im2), 5)))

# ---------------------------------------------------------------- Section 1.3
section("multiplier lcm(1..4n) without removable primes (Section 1.3)")
r_ex, s_ex = mp.mpf("10.5403551"), mp.mpf("6.5301361")
base = 1 + (r_ex + 4) / (s_ex - 4)
base_proved = 1 + (mp.mpf("10.540357") + 4) / (mp.mpf("6.530134") - 4)
check("1 + (r+4)/(s-4) = 6.747 (exact rates)", mp.nstr(base, 4) == "6.747", mp.nstr(base, 10))
check("1 + (r+4)/(s-4) = 6.747 (proved bounds for r, s)", mp.nstr(base_proved, 4) == "6.747", mp.nstr(base_proved, 10))


# ---------------------------------------------------------------- Remark 1.7
section("n = 1 for three members of the family (Remark 1.7), exact")


def J1_symbolic(e1, e2, d):
    a = e1 + e2 - d
    h = ((z - 1) * (z - 2)) ** e1 * (z ** 2 - 2 * z + 2) ** e2 / (z ** (a + 1) * (z ** 2 - 2) ** d)
    F = sp.integrate(sp.apart(sp.together(h), z, extension=sp.sqrt(2)), z)
    return -sp.I * (F.subs(z, 1 + sp.I) - F.subs(z, 1 - sp.I))


for (tr, u, v, p, q) in [((2, 2, 2), sp.Integer(-77), sp.Rational(49, 2), 22, 7),
                         ((3, 3, 2), sp.Integer(-2818), sp.Integer(897), 2818, 897),
                         ((5, 3, 4), sp.Rational(-23075, 2), sp.Rational(7345, 2), 355, 113)]:
    val = J1_symbolic(*tr)
    diff = abs(sp.N(val - (u + v * sp.pi), 120))
    check("J_1%s = %s + %s pi = %s (pi - %d/%d)" % (tr, u, v, v, p, q),
          diff < sp.Float("1e-100") and sp.Rational(p, q) == -u / v and gcd(p, q) == 1, "|diff| = %s" % sp.N(diff, 3))
    printed = {(2, 2, 2): "-0.030979", (3, 3, 2): "0.0086102", (5, 3, 4): "-0.00097969"}[tr]
    xv = sp.N(u + v * sp.pi, 40)
    nd = len(printed.split(".")[1])
    trunc = sp.floor(abs(xv) * 10 ** nd) / sp.Integer(10) ** nd
    check("J_1%s printed as %s... (truncation)" % (tr, printed), sp.sign(xv) * trunc == sp.Rational(printed))

check("355/113 = 3.14159292...", mp.nstr(mp.mpf(355) / 113, 9) == "3.14159292")
check("355/113 correct to 6 decimals (pi = 3.141592|65..., 355/113 = 3.141592|92...)",
      int(mp.floor(mp.pi * 10 ** 6)) == int(mp.floor(mp.mpf(355) / 113 * 10 ** 6)))
first = None
for qq in range(1, 20000):
    pp = int(mp.nint(qq * mp.pi))
    if qq != 113 and abs(mp.mpf(pp) / qq - mp.pi) < abs(mp.mpf(355) / 113 - mp.pi):
        first = (pp, qq)
        break
check("no fraction with denominator < 16604 is closer to pi than 355/113", first == (52163, 16604), first)
first = None
for qq in range(8, 200):
    pp = int(mp.nint(qq * mp.pi))
    if abs(mp.mpf(pp) / qq - mp.pi) < abs(mp.mpf(22) / 7 - mp.pi):
        first = (pp, qq)
        break
check("no fraction with denominator < 57 is closer to pi than 22/7 (other than 22/7 itself)", first == (179, 57), first)
I_d = sp.integrate(x ** 4 * (1 - x) ** 4 / (1 + x ** 2), (x, 0, 1))
check("Dalzell: int_0^1 x^4(1-x)^4/(1+x^2) dx = 22/7 - pi", sp.simplify(I_d - (sp.Rational(22, 7) - sp.pi)) == 0)
I_l = sp.integrate(x ** 8 * (1 - x) ** 8 * (25 + 816 * x ** 2) / (3164 * (1 + x ** 2)), (x, 0, 1))
check("Lucas: int_0^1 x^8(1-x)^8(25+816x^2)/(3164(1+x^2)) dx = 355/113 - pi",
      sp.simplify(I_l - (sp.Rational(355, 113) - sp.pi)) == 0)
lrho = -mp.log(mp.mpf("0.001458809"))
check("log(1/rho) = 6.53..., r + log(1/rho) = 17.07 with the exact r (so about e^{-17n})",
      mp.nstr(lrho, 3) == "6.53" and abs(mp.mpf("10.5403551") + lrho - 17) < 0.1, mp.nstr(mp.mpf("10.5403551") + lrho, 6))
check("proved part: r > 8.9 and -log(rho) > 6.53 give r - log(rho) > 15.43 > 15.4 (error < e^{-15.4n} for large n)",
      lrho > mp.mpf("6.53") and mp.mpf("8.9") + mp.mpf("6.53") > mp.mpf("15.4"), mp.nstr(mp.mpf("8.9") + lrho, 6))
u2, v2 = sp.Rational(-4338189943, 14), sp.Rational(197269821, 2)
a2 = -u2 / v2
err2 = mp.mpf(sp.N(a2 - sp.pi, 30))
check("-u_2/v_2 = 4338189943/1380888747, which differs from pi by 1.05...e-14 (truncated)",
      a2 == sp.Rational(4338189943, 1380888747) and mp.floor(abs(err2) * mp.mpf(10) ** 16) == 105, mp.nstr(err2, 8))

# ---------------------------------------------------------------- Section 3.2
section("W and Y (Section 3.2)")
W = z + 2 / z
Y = z - 2 / z
ph = sp.symbols("phi", real=True)
zc = sp.sqrt(2) * sp.exp(sp.I * ph)
# ---------------------------------------------------------------- Section 4.1
section("where pi comes from (Section 4.1)")
seg = mp.quad(lambda t: 1 / (1 + 1j * t), [-1, 1])  # -i * int dz/z with dz = i dt
check("-i * int_{1-i}^{1+i} dz/z = pi/2", abs(seg - mp.pi / 2) < mp.mpf(10) ** -30, mp.nstr(seg, 12))
check("Log(1+i) - Log(1-i) = i pi/2", abs(mp.log(1 + 1j) - mp.log(1 - 1j) - 1j * mp.pi / 2) < mp.mpf(10) ** -30)

# ---------------------------------------------------------------- Remark 4.4
section("partial fractions example (Remark 4.4)")
pf = sp.apart(1 / (z * (z ** 2 - 2)), z, extension=sp.sqrt(2))
target = -sp.Rational(1, 2) / z + sp.Rational(1, 4) / (z - sp.sqrt(2)) + sp.Rational(1, 4) / (z + sp.sqrt(2))
check("1/(z(z^2-2)) = -(1/2)/z + (1/4)/(z-sqrt2) + (1/4)/(z+sqrt2)", sp.simplify(pf - target) == 0, pf)

# ---------------------------------------------------------------- Appendix A.1
section("two instances of (4.5) (Appendix A.1)")
X01 = 1 / (z * Y ** 2)
check("(W/Y)' = -8/(z Y^2)", sp.simplify(sp.diff(W / Y, z) + 8 / (z * Y ** 2)) == 0)
check("1/(z Y^2) = z/(z^2-2)^2", sp.simplify(X01 - z / (z ** 2 - 2) ** 2) == 0)
Gv = (-sp.Rational(1, 8) * W / Y)
val = sp.simplify(-sp.I * (Gv.subs(z, 1 + sp.I) - Gv.subs(z, 1 - sp.I)))
num = mp.quad(lambda t: (1 + 1j * t) / ((1 + 1j * t) ** 2 - 2) ** 2, [-1, 1])
check("-i int_{1-i}^{1+i} dz/(z Y^2) = 1/4", val == sp.Rational(1, 4) and abs(num - 0.25) < mp.mpf(10) ** -30, val)
X21 = W ** 2 / (z * Y ** 2)
rhs = sp.Rational(1, 8) * (2 * W ** 2 / z - sp.diff(W ** 3 / Y, z))
check("X_2^(1) = (1/8)[2 X_2^(0) - (W^3/Y)']", sp.simplify(X21 - rhs) == 0)
check("X_2^(0) = W^2/z = z + 4/z + 4/z^3", sp.expand(W ** 2 / z - (z + 4 / z + 4 / z ** 3)) == 0)
check("residue of X_2^(1) at 0 is 1", sp.residue(sp.together(X21), z, 0) == 1)
G21 = sp.Rational(1, 4) * (z ** 2 / 2 - 2 / z ** 2) - sp.Rational(1, 8) * W ** 3 / Y   # X_2^(1) = 1/z + G21'
check("X_2^(1) = 1/z + G' with G = (1/4)(z^2/2 - 2/z^2) - (1/8) W^3/Y", sp.simplify(X21 - 1 / z - sp.diff(G21, z)) == 0)
check("G(1+i) = i, G(1-i) = -i for the second instance",
      sp.simplify(G21.subs(z, 1 + sp.I) - sp.I) == 0 and sp.simplify(G21.subs(z, 1 - sp.I) + sp.I) == 0)
val21 = sp.nsimplify(sp.simplify(-sp.I * (G21.subs(z, 1 + sp.I) - G21.subs(z, 1 - sp.I))))
num21 = mp.quad(lambda t: ((1 + 1j * t) + 2 / (1 + 1j * t)) ** 2 / ((1 + 1j * t) * ((1 + 1j * t) - 2 / (1 + 1j * t)) ** 2), [-1, 0, 1])
check("-i int_{1-i}^{1+i} W^2/(z Y^2) dz = pi/2 + %s" % val21,
      abs(num21 - (mp.pi / 2 + mp.mpf(sp.N(val21, 40)))) < mp.mpf(10) ** -30, mp.nstr(num21, 15))

# ---------------------------------------------------------------- Figure 2
section("Figure 2: |J_n| and v_n for n <= 60")
mp.mp.dps = 30
zs = mp.mpc(mp.mpf(19787) / 16384, mp.mpf(32371) / 65536)
rho = mp.mpf("0.001458809")
POLY = [mp.mpc(1, -1), mp.conj(zs), mp.mpc(1, 0), zs, mp.mpc(1, 1)]


def f_mp(w):
    return ((w - 1) * (w - 2)) ** 5 * (w * w - 2 * w + 2) ** 3 / (w ** 4 * (w * w - 2) ** 4)


def J_polygon(n):
    tot = mp.mpc(0)
    for A, B in zip(POLY, POLY[1:]):
        tot += mp.quad(lambda t: f_mp(A + t * (B - A)) ** n / (A + t * (B - A)) * (B - A), mp.linspace(0, 1, 33))
    return -1j * tot


def c_coeff(nmax):
    """c_n = coefficient of z^{4n} in N(z)^n (z^2-2)^{-4n}, exact (sympy series of polynomials)"""
    out = {}
    N = sp.Poly(((z - 1) * (z - 2)) ** 5 * (z ** 2 - 2 * z + 2) ** 3, z)
    for n in range(1, nmax + 1):
        Nn = (N ** n).all_coeffs()[::-1]                      # low degree first
        # (z^2-2)^{-4n} = (-1/2)^{4n} sum_k binom(4n+k-1,k) (z^2/2)^k
        s = sp.Integer(0)
        for k in range(0, 2 * n + 1):
            j = 4 * n - 2 * k
            if j < len(Nn):
                s += Nn[j] * sp.binomial(4 * n + k - 1, k) * sp.Rational(1, 2 ** k)
        out[n] = s * sp.Rational(1, 2 ** (4 * n))
    return out


cs = c_coeff(60)
check("c_n is a positive integer, n <= 60", all(c.is_integer and c > 0 for c in cs.values()))
check("c_1 = 7345, c_2 = 197269821", cs[1] == 7345 and cs[2] == 197269821)
logJ, logv, sgn = {}, {}, {}
for n in range(1, 61):
    Jn = J_polygon(n)
    logJ[n] = mp.log10(abs(mp.re(Jn)))
    sgn[n] = 1 if mp.re(Jn) > 0 else -1
    logv[n] = mp.log10(mp.mpf(int(cs[n])) / 2)
check("J_1 = -9.7969e-4, J_2 = 1.0455e-6, J_3 = -1.2241e-9 (polygon quadrature)",
      [mp.nstr(sgn[n] * mp.mpf(10) ** logJ[n], 5) for n in (1, 2, 3)] == ["-0.00097969", "1.0455e-6", "-1.2241e-9"])
check("|J_n| <= 4 rho^n for n <= 60", all(logJ[n] <= mp.log10(4) + n * mp.log10(rho) for n in logJ))
# compare with the exact forms of the numerical audit (audit_numeric/results.jsonl), where present
try:
    import json
    import os
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "audit_numeric", "results.jsonl")
    rows = {r["n"]: r for r in (json.loads(l) for l in open(path))}
    dev = max(abs(logJ[n] - mp.log10(abs(mp.mpf(rows[n]["J"])))) for n in range(1, 61))
    devv = max(abs(logv[n] - mp.mpf(rows[n]["log_abs_v"]) / mp.log(10)) for n in range(1, 61))
    check("polygon quadrature agrees with the exact forms of audit_numeric (n <= 60)", dev < 1e-12 and devv < 1e-12,
          "max dev %s, %s" % (mp.nstr(dev, 3), mp.nstr(devv, 3)))
except FileNotFoundError:
    print("(audit_numeric/results.jsonl not found; comparison skipped)")
# |u_n| = v_n pi - J_n, since J_n = u_n + v_n pi with v_n > 0 and u_n < 0
logu = {n: mp.log10(mp.mpf(10) ** logv[n] * mp.pi - sgn[n] * mp.mpf(10) ** logJ[n]) for n in range(1, 61)}
check("Figure 2 caption: for every plotted n (n <= 60), |J_n| < 10^{-7n} |u_n| (u_n and -v_n pi agree to more than 7n digits)",
      all(logu[n] - logJ[n] > 7 * n for n in range(1, 61)), mp.nstr(min((logu[n] - logJ[n]) / n for n in range(1, 61)), 8))
breaks = [n for n in range(2, 61) if sgn[n] == sgn[n - 1]]
check("signs of J_n alternate for n <= 60 except J_17, J_18 (first break at n = 18)", breaks == [18], breaks)
resid = {n: logJ[n] - (mp.log10(4) + n * mp.log10(rho)) for n in range(1, 61)}
check("largest dip below the bound line (n <= 60) at n = 17", min(resid, key=lambda n: resid[n]) == 17,
      mp.nstr(resid[17], 4))
slope_J = (logJ[60] - logJ[30]) / 30
slope_v = (logv[60] - logv[30]) / 30
check("slopes of Figure 2 (n = 30..60) close to r/ln10 = 4.578 and -s/ln10 = -2.836",
      abs(slope_v - mp.mpf("10.5403551") / mp.log(10)) < 0.01 and abs(slope_J + mp.mpf("6.5301361") / mp.log(10)) < 0.01
      and mp.nstr(mp.mpf("10.5403551") / mp.log(10), 4) == "4.578" and mp.nstr(mp.mpf("6.5301361") / mp.log(10), 4) == "2.836",
      (mp.nstr(slope_v, 5), mp.nstr(slope_J, 5)))
check("Figure 2: log10(rho) = -2.836..., r/log10 = 4.58 (rounded), labels 'slope ~ 4.6' and '~ -2.8'",
      mp.nstr(mp.log10(rho), 4) == "-2.836" and mp.nstr(mp.mpf("10.5403551") / mp.log(10), 3) == "4.58"
      and mp.nstr(slope_v, 2) == "4.6" and mp.nstr(slope_J, 2) == "-2.8")
if "--data" in sys.argv:
    print("% log10 v_n")
    print(" ".join("(%d,%.2f)" % (n, logv[n]) for n in range(1, 61)))
    print("% log10 |J_n|")
    print(" ".join("(%d,%.2f)" % (n, logJ[n]) for n in range(1, 61)))
    print("%% slopes 30..60: v %.4f, J %.4f; log10 rho = %.6f" % (slope_v, slope_J, mp.log10(rho)))

bad = [n for n, ok in RESULTS if not ok]
print("\n%d checks, %d failed%s  (%.1fs)" % (len(RESULTS), len(bad), (": " + "; ".join(bad)) if bad else "", time.time() - T0))
sys.exit(1 if bad else 0)
