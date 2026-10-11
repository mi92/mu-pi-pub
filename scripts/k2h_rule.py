"""A-R653 E36: bound function of the K2H family from the three (provable) rules.
  rates r, s: critical values (k2h_scan.rates);  M = max(e1+e2-d, d);
  2-adic slope: e2 >= d: -(e2-d)/2;  e2 <= d: max(0, d - 1.5 e2);
  removable primes: x = n/p >= 1/M with floor(d x) even and {e1 x}+{e2 x} < {d x};  saving = int_S dx/x^2.
  C = M + slope*log 2 - saving;  mu = 1 + (r + C)/(s - C)."""
import sys, math
from fractions import Fraction as Fr
from mpmath import mp, mpf, log, digamma
sys.path.insert(0, "scripts")
from k2h_scan import rates
mp.dps = 30
def window(e1, e2, d):
    """S intersected with [0,2) as a list of (a,b) Fractions."""
    A0 = e1 + e2 - d
    pts = sorted(set([Fr(j, e1) for j in range(2*e1 + 1)] + [Fr(j, e2) for j in range(2*e2 + 1)] + [Fr(j, d) for j in range(2*d + 1)]))
    out = []
    for lo, hi in zip(pts[:-1], pts[1:]):
        f1, f2, fd = math.floor(e1*lo), math.floor(e2*lo), math.floor(d*lo)
        if fd % 2: continue
        b = min(hi, Fr(f1 + f2 - fd, A0))
        if b > lo:
            if out and out[-1][1] == lo: out[-1] = (out[-1][0], b)
            else: out.append((lo, b))
    return out
def saving(e1, e2, d):
    M = max(e1 + e2 - d, d); cut = Fr(1, M); tot = mpf(0)
    for a, b in window(e1, e2, d):
        tot += (digamma(mpf(b.numerator)/b.denominator/2 + 1) - digamma(mpf(a.numerator)/a.denominator/2 + 1))/2
        if b > cut:
            a0 = max(a, cut); tot += mpf(a0.denominator)/a0.numerator - mpf(b.denominator)/b.numerator
    return tot
def slope2(e2, d): return -Fr(e2 - d, 2) if e2 >= d else max(Fr(0), d - Fr(3*e2, 2))
def bound(e1, e2, d, with_saving=True):
    r, s, A0 = rates(e1, e2, d)
    if r is None or s is None: return None
    M = max(e1 + e2 - d, d); sl = slope2(e2, d); sv = saving(e1, e2, d) if with_saving else mpf(0)
    C = M + mpf(sl.numerator)/sl.denominator*log(2) - sv
    if s - C <= 0: return None
    return 1 + (r + C)/(s - C), r, s, C, sv, sl
if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] != "scan":
        for t in sys.argv[1:]:
            e1, e2, d = (int(x) for x in t.split(","))
            b = bound(e1, e2, d)
            print(t, "window on [0,2):", [(str(a), str(bb)) for a, bb in window(e1, e2, d)])
            print("    mu =", mp.nstr(b[0], 15), " r =", mp.nstr(b[1], 12), " s =", mp.nstr(b[2], 12), " C =", mp.nstr(b[3], 12), " saving =", mp.nstr(b[4], 10), " 2-adic slope =", b[5],
                  "  baseline (no saving):", mp.nstr(bound(e1, e2, d, False)[0], 10))
    else:
        dmax = int(sys.argv[2]) if len(sys.argv) > 2 else 12
        res = []
        for d in range(1, dmax + 1):
            for e1 in range(1, 3*d + 1):
                for e2 in range(1, 2*d + 1):
                    if math.gcd(math.gcd(e1, e2), d) != 1 or e1 + e2 <= d: continue
                    try: b = bound(e1, e2, d)
                    except Exception as ex: b = None
                    if b: res.append((float(b[0]), (e1, e2, d), float(b[1]), float(b[2]), float(b[3]), float(b[4]), str(b[5])))
        res.sort()
        print(len(res), "triples with a positive bound; top 30: mu, (e1,e2,d), r, s, C, saving, 2-adic slope")
        for t in res[:30]: print("  %.6f  %-12s r=%.4f s=%.4f C=%.4f saving=%.4f slope=%s" % (t[0], str(t[1]), t[2], t[3], t[4], t[5], t[6]))
