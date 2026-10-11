"""A-R653 exact tool 2:  I = int_{conj(z0)}^{z0} N(z) dz / ( z^A * Q(z)^d ),  Q = q2*z^2 + q0 (even quadratic, any sign),
N in Z[z].  Returns (u, res0, leak): -i*I = u + res0*Delta_0 + (leak must be 0: coefficient of the transcendental
primitive of 1/Q, i.e. the residue at the roots of Q).  u = 2*Im F(z0)."""
from flint import fmpz, fmpq, fmpz_poly, fmpq_poly

class GQ:                                   # Gaussian rationals
    __slots__ = ("re", "im")
    def __init__(s, re, im=0): s.re, s.im = fmpq(re), fmpq(im)
    def __mul__(s, o): return GQ(s.re*o.re - s.im*o.im, s.re*o.im + s.im*o.re)
    def __add__(s, o): return GQ(s.re + o.re, s.im + o.im)
    def inv(s):
        n = s.re*s.re + s.im*s.im; return GQ(s.re/n, -s.im/n)
    def scale(s, c): return GQ(s.re*c, s.im*c)

def forms2(N, A, Qc, d, z0):
    q0, q2 = fmpq(Qc[0]), fmpq(Qc[1])
    Nq = fmpq_poly(N); z = fmpq_poly([0, 1]); Q = fmpq_poly([q0, 0, q2])
    D = z**A * Q**d
    P, R = divmod(Nq, D) if Nq.degree() >= D.degree() else (fmpq_poly([0]), Nq)
    # R/(z^A Q^d) = U/z^A + V/Q^d, deg U < A, deg V < 2d.   U = R * Q^{-d} mod z^A
    if A > 0:
        # inverse series of Q^d mod z^A
        inv = fmpq_poly([1]); Qd = Q**d
        coeffs = [Qd[i] for i in range(min(A, Qd.degree() + 1))]
        # power-series inverse by recursion
        b = [fmpq(1) / coeffs[0]]
        for k in range(1, A):
            s = fmpq(0)
            for j in range(1, min(k, len(coeffs) - 1) + 1): s += coeffs[j] * b[k - j]
            b.append(-s / coeffs[0])
        U = fmpq_poly([R[i] for i in range(min(A, R.degree() + 1))]) * fmpq_poly(b)
        U = fmpq_poly([U[i] for i in range(min(A, U.degree() + 1))])
    else:
        U = fmpq_poly([0])
    V = R - U * Q**d
    if A > 0: V, rem = divmod(V, z**A)
    x0, y0 = fmpq(z0[0]), fmpq(z0[1]); Z0 = GQ(x0, y0)
    acc = fmpq(0)                                   # Im F(z0)
    zp = GQ(1, 0)
    for k in range(P.degree() + 1):
        zp = zp * Z0
        if P[k] != 0: acc += P[k] * zp.im / (k + 1)
    res0 = U[A - 1] if A > 0 and A - 1 <= U.degree() else fmpq(0)
    if A > 1:
        zi = Z0.inv(); zp = GQ(1, 0)
        for m in range(1, A):                       # term U_{A-1-m} z^{-m-1} -> -U z^{-m}/m
            zp = zp * zi
            c = U[A - 1 - m] if A - 1 - m <= U.degree() else fmpq(0)
            if c != 0: acc -= c * zp.im / m
    # V = sum_{k=1..d} (alpha_k + beta_k z) Q^{d-k}  -> terms (alpha_k + beta_k z)/Q^k
    leak = fmpq(0)
    if d > 0:
        terms = []; W = V
        for k in range(d, 0, -1):                   # remainder mod Q gives the Q^{-k} term for k=d first
            W, r = divmod(W, Q)
            terms.append((k, r[0] if r.degree() >= 0 else fmpq(0), r[1] if r.degree() >= 1 else fmpq(0)))
        Qz = GQ(q0, 0) + (Z0*Z0).scale(q2); Qi = Qz.inv()
        # J_k = int dz/Q^k: J_k = z/(2 q0 (k-1) Q^{k-1}) + (2k-3)/(2 q0 (k-1)) J_{k-1};  int z dz/Q^k = -1/(2 q2 (k-1) Q^{k-1}), k>=2
        # precompute rational (single-valued) part S_k and J_1-coefficient c_k of J_k
        S = {1: GQ(0, 0)}; c = {1: fmpq(1)}; Qp = GQ(1, 0)
        for k in range(2, d + 1):
            Qp = Qp * Qi                            # Q^{-(k-1)}
            S[k] = (Z0 * Qp).scale(fmpq(1) / (2*q0*(k - 1))) + S[k - 1].scale(fmpq(2*k - 3) / (2*q0*(k - 1)))
            c[k] = c[k - 1] * fmpq(2*k - 3) / (2*q0*(k - 1))
        Qp = GQ(1, 0); powQ = {0: GQ(1, 0)}
        for k in range(1, d + 1):
            Qp = Qp * Qi; powQ[k] = Qp
        for k, al, be in terms:
            acc += al * S[k].im; leak += al * c[k]
            if be != 0:
                if k == 1: leak += fmpq(10)**30     # a z/Q term would give a logarithm: flag it
                else: acc -= be * powQ[k - 1].im / (2*q2*(k - 1))
    return 2 * acc, res0, leak

if __name__ == "__main__":
    from mpmath import mp, mpf, mpc, quad, pi
    mp.dps = 30
    # kappa=-4 test: N=(z^2-2z+2)^2 (z^2+4z+8)^2, poles z^A and (z^2+4)^d, symmetric: A-1 = order at infinity
    b, d = 2, 2; A = (8 - 2*d)//2 + 1
    N = fmpz_poly([2, -2, 1])**b * fmpz_poly([8, 4, 1])**b
    u, r0, leak = forms2(N, A, (4, 1), d, (1, 1))
    f = lambda z: (z*z - 2*z + 2)**b * (z*z + 4*z + 8)**b / (z**A * (z*z + 4)**d)
    I = quad(lambda y: f(mpc(1, y)) * 1j, [-1, 0, 1])
    print("leak (must be 0):", leak, "  -i*I numeric:", mp.nstr((-1j*I).real, 15), "  exact u + res0*pi/2:", mp.nstr(mpf(int(u.p))/int(u.q) + mpf(int(r0.p))/int(r0.q)*pi/2, 15))
