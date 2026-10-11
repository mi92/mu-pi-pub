"""A-R653: symbolic verification (sympy) of the change-of-variable identities used in K2H_PROOF.md."""
import sympy as sp
z, w, W = sp.symbols('z w W')
r2 = sp.sqrt(2); eps = r2 - 1; I = sp.I
ok = lambda e: sp.simplify(sp.expand(sp.together(e))) == 0
# sigma: z -> 2/z
s = 2/z
print("sigma identities:", ok((s-1)*(s-2) - 2*(z-1)*(z-2)/z**2), ok(s**2-2*s+2 - 2*(z**2-2*z+2)/z**2), ok(s**2-2 + 2*(z**2-2)/z**2))
# W-frame
Wz = z + 2/z; Y = z - 2/z
print("W-frame:", ok((z-1)*(z-2)/z - (Wz-3)), ok((z**2-2*z+2)/z - (Wz-2)), ok(Y**2 - (Wz**2-8)), ok(sp.diff(Wz, z) - Y/z))
# w-frame: z = sqrt2 (w - i eps)/(w + i eps)
zw = r2*(w - I*eps)/(w + I*eps)
chk = [ (zw-1)*(zw-2) + r2*(1+eps**2*w**2)/(w+I*eps)**2,
        zw**2-2*zw+2 + 2*r2*eps*(1-w**2)/(w+I*eps)**2,
        zw**2-2 + 8*I*eps*w/(w+I*eps)**2,
        sp.diff(zw, w)/zw - 2*I*eps/(w**2+eps**2) ]
print("w-frame:", [ok(c) for c in chk])
print("endpoints: w=1 ->", sp.simplify(zw.subs(w, 1)), "  w=-1 ->", sp.simplify(zw.subs(w, -1)), "  w=0 ->", sp.simplify(zw.subs(w, 0)), "  w=i*eps ->", sp.simplify(zw.subs(w, I*eps)))
print("c = 1+eps^2 = 2 sqrt2 eps:", ok(1+eps**2 - 2*r2*eps), "  1-eps^2 = 2 eps:", ok(1-eps**2-2*eps), "  theta = (2/eps) atan(1/eps) = 3 pi/(4 eps):", abs(sp.N(2/eps*sp.atan(1/eps) - 3*sp.pi/(4*eps), 40)) < 1e-35)
# q-frame: q = (z - z0)/(z - conj z0)
q = sp.symbols('q'); z0 = 1 + I; zb = 1 - I
zq = (zb*q - z0)/(q - 1)
chk = [ (zq-1)*(zq-2) - I*(1+I)*(q+1)*(q+I)/(q-1)**2, zq**2-2*zq+2 + 4*q/(q-1)**2, zq**2-2 + 2*(1+I)*(q**2-I)/(q-1)**2, zq - zb*(q-I)/(q-1),
        sp.diff(zq, q)/zq - (I-1)/((q-I)*(q-1)) ]
print("q-frame:", [ok(c) for c in chk])
# critical cubic in W: d/dW log F, F = (W-3)^{2e1}(W-2)^{2e2}/(W^2-8)^d
e1, e2, d = sp.symbols('e1 e2 d')
num = sp.expand(sp.together(2*e1/(W-3) + 2*e2/(W-2) - 2*d*W/(W**2-8))*(W-3)*(W-2)*(W**2-8)/2)
target = (e1+e2-d)*W**3 - (2*e1+3*e2-5*d)*W**2 - (8*e1+8*e2+6*d)*W + 16*e1 + 24*e2
print("critical cubic:", sp.simplify(sp.expand(sp.simplify(num)) - sp.expand(target)) == 0)
