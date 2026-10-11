# Scripts that recompute the numbers of the paper

All scripts are run from the repository root with Python >= 3.10 and the packages of `../requirements.txt`
(exact rational arithmetic throughout, the library FLINT for polynomial arithmetic, mpmath for the constants).
`zsh ../verify_k2h.sh` runs the main checks in one go (about a minute); a recorded run is in `../verify_k2h.log`.

| file | what it computes | paper |
|---|---|---|
| `paper_v3_numbers.py` | recomputes every number printed in version 3 of the paper, independently of the programs that produced them; prints PASS/FAIL per number and exits non-zero on a mismatch; also compares the Bernstein certificates with `lean/MuPi/K2H/ContourCert.lean` | all sections |
| `paper_v4_new_numbers.py` | the numbers added in version 4 (Figure 2, Section 1.3, Remark 1.7, Appendix A.1) | §1, App. A |
| `k2h_identities.py` | symbolic check (sympy) of the change-of-variable identities (`z -> 2/z`, the coordinates `W`, `Y`, `w`, the critical cubic) | §3, §5.4 |
| `k2h_constants.py` | the constants `r`, `s`, `C` and the bound `1+(r+C)/(s-C)` for any triple `(e1,e2,d)`, 40 digits | §9, §11 |
| `k2h_small.py` | the exact forms `J_n = u_n + v_n pi` for small `n` by the recursion in `W`, `Y` | §4, Example 1.6 |
| `k2h_quad.py` | numerical quadrature of the integral against the exact forms | §10.3 |
| `k2h_wframe.py` | independent exact evaluation in the coordinate `w` over `Q(sqrt 2)` | §5.4, §10.3 |
| `k2h_rulecheck.py` | integrality of `D_n u_n`, `D_n v_n` with `D_n = lcm(1..4n)/Phi_n`, and the removable-prime rule, over a range of `n` | §5, Theorem 1.4(b) |
| `k2h_certify.py` | `twoadic`: the inequalities of the 2-adic lemma term by term; `contour`: interval-arithmetic bound of `log|f|` on the polygon | §5.4, §7 |
| `k2h_contour_cert.py`, `k2h_contour_cert423.py` | rigorous interval-arithmetic certificate `log|f| <= -s + tol` on the polygon, for `(5,3,4)` and `(4,2,3)` | §7 |
| `k2h_lean_blueprint_check.py` | the explicit `w`-decomposition that the Lean proof of the 2-adic part formalises, with the 2-adic levels, for `n <= N` | §5.4, §10.3 |
| `k2h_delta.py` | sizes of the exact integer forms: `log|v_n|/n`, `-log|J_n|/n`, `log D_n/n` | §6-§8, Table 7 |
| `lean_contour_gen.py` | the generator of `lean/MuPi/K2H/ContourCert.lean` (Bernstein certificates in exact rational arithmetic) | §7, App. A |
| `k2h.py`, `gen2.py`, `k2h_rule.py`, `k2h_scan.py` | library code used by the scripts above (partial fractions over `Q(i)`, the removable-prime rule) | |

Section and statement numbers in the PASS lines refer to version 4 of the paper (`K2H_paper_v4.pdf`); the
numbers themselves are the same in the journal version.
