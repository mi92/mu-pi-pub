"""Generate Bernstein certificates for  |f534(z)|^2 <= rho^2  on the two segments 1 -> zs and zs -> 1+i,
and write them as Lean lemmas (file ContourCert.lean).

P(t) = rho^2 * Den(x(t),y(t)) - Num(x(t),y(t)),  deg 32.  On [u, u+h]:
   P(u + h*s) = sum_j beta_j s^j (1-s)^(32-j),   all beta_j >= 0   (exact rational arithmetic).
usage: lean_contour_gen.py <rho as a fraction> <out.lean> <maxdepth> <Re zs> <Im zs> [module prefix]
   e.g. lean_contour_gen.py 1458809/1000000000 ContourCert.lean 16 19787/16384 32371/65536 MuPi
"""
import sys
from fractions import Fraction as F
from math import comb

D = 32

def padd(a, b):
    n = max(len(a), len(b)); return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
def pmul(a, b):
    r = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b): r[i+j] += x*y
    return r
def pscale(c, a): return [c*x for x in a]
def ppow(a, k):
    r = [F(1)]
    for _ in range(k): r = pmul(r, a)
    return r
def psub(a, b): return padd(a, pscale(F(-1), b))

def polyP(x, y, rho2):
    """x, y: polynomials in the parameter; returns rho2*Den - Num as polynomial."""
    one = [F(1)]
    x1 = psub(x, one); x2 = psub(x, [F(2)]); y1 = psub(y, one); yp = padd(y, one)
    sq = lambda a: pmul(a, a)
    q1 = padd(sq(x1), sq(y)); q2 = padd(sq(x2), sq(y))
    q3 = padd(sq(x1), sq(y1)); q4 = padd(sq(x1), sq(yp))
    q5 = padd(sq(x), sq(y))
    q6 = padd(sq(psub(psub(sq(x), sq(y)), [F(2)])), pscale(F(4), pmul(sq(x), sq(y))))
    num = pmul(ppow(pmul(q1, q2), 5), ppow(pmul(q3, q4), 3))
    den = pmul(ppow(q5, 4), ppow(q6, 4))
    return psub(pscale(rho2, den), num)

def compose_affine(p, u, h):
    """coefficients of p(u + h*s) in s"""
    res = [F(0)]
    for c in reversed(p):
        res = padd(pmul(res, [u, h]), [c])
    return res

def bernstein(a):
    """power coefficients a_i (degree D) -> beta_j with sum_j beta_j s^j (1-s)^(D-j)"""
    a = a + [F(0)] * (D + 1 - len(a))
    return [sum(F(comb(D - i, j - i)) * a[i] for i in range(j + 1)) for j in range(D + 1)]

def certify(p, u, h, depth, maxdepth, out):
    b = bernstein(compose_affine(p, u, h))
    if all(c >= 0 for c in b):
        out.append((u, h, b)); return True
    if depth >= maxdepth: return False
    return certify(p, u, h/2, depth+1, maxdepth, out) and certify(p, u + h/2, h/2, depth+1, maxdepth, out)

def lean_rat(q):
    q = F(q)
    return f"({q.numerator} : ℝ)" if q.denominator == 1 else f"(({q.numerator} : ℝ) / {q.denominator})"

if __name__ == "__main__":
    rho = F(sys.argv[1]); outpath = sys.argv[2]; maxdepth = int(sys.argv[3]) if len(sys.argv) > 3 else 14
    XS, YS = F(sys.argv[4]), F(sys.argv[5])
    rho2 = rho*rho
    segs = {"seg1": ([F(1), XS - 1], [F(0), YS]),          # 1 + t (zs - 1)
            "seg2": ([XS, 1 - XS], [YS, 1 - YS])}          # zs + t (1 + i - zs)
    lines = []
    summary = {}; certs = {}
    for name, (x, y) in segs.items():
        p = polyP(x, y, rho2)
        out = []
        ok = certify(p, F(0), F(1), 0, maxdepth, out)
        summary[name] = (ok, len(out)); certs[name] = out
        if not ok: continue
        for idx, (u, h, b) in enumerate(out):
            xs = f"({lean_rat(x[0])} + {lean_rat(x[1])} * ({lean_rat(u)} + {lean_rat(h)} * s))"
            ys = f"({lean_rat(y[0])} + {lean_rat(y[1])} * ({lean_rat(u)} + {lean_rat(h)} * s))"
            terms = " +\n      ".join(f"{lean_rat(c)} * s ^ {j} * r ^ {D - j}" for j, c in enumerate(b))
            lines.append(f"""
/-- `{name}`, subinterval `[{u}, {u + h}]` -/
lemma cert_{name}_{idx} (s r : ℝ) (hr : r = 1 - s) (hs : 0 ≤ s) (hr0 : 0 ≤ r) :
    numR {xs} {ys} ≤ rhoSq * denR {xs} {ys} := by
  have key : rhoSq * denR {xs} {ys} - numR {xs} {ys}
      = {terms} := by
    subst hr
    unfold numR denR rhoSq
    ring
  have hpos : 0 ≤ {terms} := by positivity
  linarith
""")
    for name, (x, y) in segs.items():
        if not summary[name][0]: continue
        out = certs[name]
        # dispatch theorem for the whole segment
        X = f"({lean_rat(x[0])} + {lean_rat(x[1])} * t)"
        Y = f"({lean_rat(y[0])} + {lean_rat(y[1])} * t)"
        body = []
        indent = "  "
        for idx, (u, h, b) in enumerate(out):
            U, H = lean_rat(u), lean_rat(h)
            last = idx == len(out) - 1
            lower = "h0" if idx == 0 else "hlo.le"
            block = f"""have hc := cert_{name}_{idx} ((t - {U}) / {H}) (1 - (t - {U}) / {H}) rfl
    (div_nonneg (by linarith [{lower}]) (by norm_num))
    (by rw [sub_nonneg, div_le_one (by norm_num)]; linarith)
  rw [show {U} + {H} * ((t - {U}) / {H}) = t by ring] at hc
  exact hc"""
            if last:
                body.append("  " + block)
            else:
                E = lean_rat(u + h)
                body.append(f"  rcases le_or_gt t {E} with hup | hlo\n  · " + block.replace("\n", "\n  ").replace("linarith)", "linarith [hup])", 1) if False else
                            f"  by_cases hup : t ≤ {E}\n  · " + block.replace("\n  ", "\n    ") + f"\n  have hlo : {E} < t := not_le.1 hup")
        lines.append(f"""
/-- the polynomial inequality on the whole segment `{name}` -/
theorem {name}_poly (t x y : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (hx : x = {X}) (hy : y = {Y}) :
    numR x y ≤ rhoSq * denR x y := by
  subst hx hy
""" + "\n".join(body) + "\n")
    prefix = sys.argv[6] if len(sys.argv) > 6 else "RecMath.PiMeasure"
    hdr = f"""import {prefix}.K2H.ContourDefs

/-! Generated by `R653/scripts/lean_contour_gen.py {sys.argv[1]} … {sys.argv[4]} {sys.argv[5]}`.  Bernstein certificates. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace PiMeasure
"""
    open(outpath, "w").write(hdr + "".join(lines) + "\nend PiMeasure\n")
    print(summary, " file bytes:", sum(len(l) for l in lines))
    for name, (x, y) in segs.items():
        if summary[name][0]:
            pass
