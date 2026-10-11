"""A-R653 E39: direct numerical quadrature of J_n = -i int_{1-i}^{1+i} f(z)^n dz/z along Re z = 1, compared with the exact
u_n + v_n*pi from partial fractions.  Independent of all algebra except the definition of f."""
import sys
from fractions import Fraction as Fr
sys.path.insert(0, "scripts")
from k2h import raw
from mpmath import mp, mpf, mpc, quad, pi, fabs, log
e1, e2, d = (int(x) for x in sys.argv[1].split(",")); ns = [int(x) for x in sys.argv[2].split(",")]
A = e1 + e2 - d
for n in ns:
    u, r0, leak = raw((e1, 0, e2, 0, d), n)
    uu = Fr(int(u.p), int(u.q)); v = Fr(int(r0.p), int(r0.q))/2
    mp.dps = 60 + int(8*n)
    f = lambda z: ((z - 1)*(z - 2))**(e1*n)*(z*z - 2*z + 2)**(e2*n)/(z**(A*n + 1)*(z*z - 2)**(d*n))
    I = quad(lambda y: f(mpc(1, y))*1j, [-1, -0.5, 0, 0.5, 1], maxdegree=10)
    Jq = (-1j*I)
    Jx = mpf(uu.numerator)/uu.denominator + mpf(v.numerator)/v.denominator*pi
    rel = fabs(Jq.real - Jx)/fabs(Jx)
    print(f"n={n}: quadrature J = {mp.nstr(Jq.real, 20)} (imag part {mp.nstr(Jq.imag, 3)}),  exact u+v*pi = {mp.nstr(Jx, 20)},  relative difference {mp.nstr(rel, 3)},  v_n = {v if v.denominator <= 2 and abs(v.numerator) < 10**12 else 'big'}")
