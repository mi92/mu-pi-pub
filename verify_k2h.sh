#!/bin/zsh
# One-command reproduction of the numerical and exact checks behind the paper (about a minute on a laptop).
# Run from the repository root:   PYTHON=/path/to/venv/bin/python zsh verify_k2h.sh
# Every script can also be run on its own, e.g.  python3 scripts/k2h_small.py 5,3,4 1,2,3,4
PY="${PYTHON:-python3}"   # python >= 3.10 with the packages of requirements.txt
set -e
echo "== 1. change-of-variable identities (symbolic) =="
$PY scripts/k2h_identities.py
echo "== 2. constants of the bound function: (5,3,4), (4,2,3), (46,28,37), and the Zeilberger-Zudilin point (3,3,2) =="
$PY scripts/k2h_constants.py 5,3,4 4,2,3 46,28,37 3,3,2 | grep -E "K2H|r      =|s      =|C      =|mu     ="
echo "== 3. first exact forms of (5,3,4) =="
$PY scripts/k2h_small.py 5,3,4 1,2,3,4
echo "== 4. exact forms against numerical quadrature =="
$PY scripts/k2h_quad.py 5,3,4 1,2,3,5
echo "== 5. independent evaluation over Q(sqrt2) (w-coordinate) =="
$PY scripts/k2h_wframe.py 5,3,4 1,2,3,4
echo "== 6. integrality with D_n = lcm/Phi_n and the removable-prime rule =="
$PY scripts/k2h_rulecheck.py 5,3,4 1 60
$PY scripts/k2h_rulecheck.py 4,2,3 2 40
$PY scripts/k2h_rulecheck.py 3,3,2 1 30
echo "== 7. 2-adic lemma, term by term =="
$PY scripts/k2h_certify.py twoadic 5,3,4 1,2,3,4
echo "== 7b. the w-decomposition and 2-adic levels formalised in Lean, n <= 6 =="
$PY scripts/k2h_lean_blueprint_check.py 6 | tail -1
echo "== 8. contour certificates (interval arithmetic) =="
$PY scripts/k2h_contour_cert.py 5,3,4 4000
$PY scripts/k2h_contour_cert423.py 4000
echo "== 9. sizes of the exact integer forms of (5,3,4) =="
$PY scripts/k2h_delta.py 5,3,4 20,40,60,80
echo "== 10. every number printed in the paper, version 3 (independent recomputation; exits non-zero on a mismatch) =="
$PY scripts/paper_v3_numbers.py
echo "== 11. the numbers added in version 4 (exits non-zero on a mismatch) =="
$PY scripts/paper_v4_new_numbers.py
echo "ALL STEPS RAN"
