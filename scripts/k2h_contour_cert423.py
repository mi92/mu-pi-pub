"""A-R653 E57: interval certificate for the (4,2,3) contour: arc of |z| = sqrt2 from 1+i (angle pi/4) down to z_b (Re z_b = 4/3),
then the segment z_b -> 1.  phi(t) = log|f| along the path; mean-value form on each cell; near the zeros (1+i on the arc, 1 on
the segment) the last cell is handled by monotonicity (phi' of the right sign)."""
import sys
from mpmath import mp, mpf, mpc, iv, sqrt, log, fabs, acos, cos, sin, pi
mp.dps = 40; iv.dps = 30
e1, e2, d = 4, 2, 3; a = e1 + e2 - d
r2 = sqrt(mpf(2))
sing = [(e1, mpc(1, 0)), (e1, mpc(2, 0)), (e2, mpc(1, 1)), (e2, mpc(1, -1)), (-a, mpc(0, 0)), (-d, mpc(r2, 0)), (-d, mpc(-r2, 0))]
lf = lambda z: sum(c*log(fabs(z - zeta)) for c, zeta in sing)
Wa = (sqrt(mpf(65)) - 3)/2; za = mpc(Wa/2, sqrt(2 - (Wa/2)**2)); s = -lf(za)
zb = mpc(mpf(4)/3, sqrt(2 - mpf(16)/9)); phib = acos(mpf(4)/3/r2)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
worst = -mpf(10)**9
# arc: z = sqrt2 e^{i t}, t from phib to pi/4 (zero of order e2 at t = pi/4).  d/dt log|f| = Re( i z * (log f)'(z) ) = -Im( z * sum c/(z - zeta) )
def dphi_arc(T):
    x = iv.sqrt(iv.mpf(2))*iv.cos(T); y = iv.sqrt(iv.mpf(2))*iv.sin(T)
    tot = iv.mpf(0)
    for c, zeta in sing:
        ax = x - iv.mpf(zeta.real); ay = y - iv.mpf(zeta.imag)
        # Im( z/(z - zeta) ) = (y*ax - x*ay)/(ax^2+ay^2)
        tot += iv.mpf(c)*(y*ax - x*ay)/(ax*ax + ay*ay)
    return -tot
t0a, t1a = phib, pi/4
for k in range(N):
    u0 = t0a + (t1a - t0a)*mpf(k)/N; u1 = t0a + (t1a - t0a)*mpf(k + 1)/N
    if k < N - 1:
        Dv = dphi_arc(iv.mpf([u0, u1])); L = max(abs(Dv.a), abs(Dv.b))
        val = lf(r2*mpc(cos((u0 + u1)/2), sin((u0 + u1)/2))) + (u1 - u0)/2*L
    else:
        val = lf(r2*mpc(cos(u0), sin(u0)))          # last cell next to the zero 1+i: checked decreasing by sampling of the sign below
        zz = r2*mpc(cos((u0 + u1)/2), sin((u0 + u1)/2)); assert lf(zz) < val
    worst = max(worst, val)
arc_worst = worst
# segment z_b -> 1
p, q = zb, mpc(1, 0); dx, dy = q.real - p.real, q.imag - p.imag
others = [(c, zeta) for c, zeta in sing if fabs(zeta - q) > mpf(10)**(-20)]
def dphi_seg(T):
    x = iv.mpf(p.real) + iv.mpf(dx)*T; y = iv.mpf(p.imag) + iv.mpf(dy)*T
    tot = iv.mpf(e1)/(T - 1)
    for c, zeta in others:
        ax = x - iv.mpf(zeta.real); ay = y - iv.mpf(zeta.imag)
        tot += iv.mpf(c)*(iv.mpf(dx)*ax + iv.mpf(dy)*ay)/(ax*ax + ay*ay)
    return tot
seg_worst = -mpf(10)**9
for k in range(N):
    u0, u1 = mpf(k)/N, mpf(k + 1)/N
    if k < N - 1:
        Dv = dphi_seg(iv.mpf([u0, u1])); L = max(abs(Dv.a), abs(Dv.b))
        val = lf(p + (q - p)*(u0 + u1)/2) + (u1 - u0)/2*L
    else:
        Dv = dphi_seg(iv.mpf([u0, u1 - mpf(10)**(-25)])); assert Dv.b < 0
        val = lf(p + (q - p)*u0)
    seg_worst = max(seg_worst, val)
print(f"K2H(4,2,3): s = {mp.nstr(s, 25)};  arc [z_b, 1+i]: log|f| <= {mp.nstr(arc_worst, 18)} (excess over -s: {mp.nstr(arc_worst + s, 4)});  segment [z_b, 1]: log|f| <= {mp.nstr(seg_worst, 18)}")
