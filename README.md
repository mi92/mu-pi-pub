# The irrationality exponent of π is at most 6.0446

This repository contains

* `K2H_paper_v3.pdf`: the paper, with the full proof;
* `lean/`: a Lean 4 / Mathlib formalisation of the proof (Lake project `MuPi`, 20 files, 6,238 lines).

**Status.** The Lean proof is complete modulo the prime number theorem, which enters as an explicit
hypothesis. The paper has not yet been refereed.

## Main statement (`lean/MuPi/K2H/Main.lean`)

```lean
theorem PiMeasure.pi_irrationality_exponent
    (hPNT : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1)) :
    ∀ μ : ℝ, 6.0446 < μ → ExponentLE Real.pi μ
```

where `ExponentLE θ μ := ∃ b₀ : ℕ, ∀ b ≥ b₀, ∀ a : ℤ, (b : ℝ) ^ (-μ) < |θ - a / b|` (`lean/MuPi/HataLemma.lean`).

**The only hypothesis is the prime number theorem** in the form `θ(x) ~ x` (Mathlib's
`Chebyshev.theta`). The prime number theorem is not in Mathlib; it is a published, accepted result
(and formalised elsewhere, e.g. in the PrimeNumberTheoremAnd project). Everything else is proved here:
no `sorry`, no extra axioms (`#print axioms` shows `propext`, `Classical.choice`, `Quot.sound`).

## Objects

`f(z) = ((z-1)(z-2))^5 (z²-2z+2)^3 / (z^4 (z²-2)^4)`, `J_n = -i ∫_{1-i}^{1+i} f(z)^n dz/z`
(`MuPi/K2H/Defs.lean`: `f534`, `J534`), `c_n` = coefficient of `z^{4n}` in `N(z)^n (z²-2)^{-4n}` (`cPS`),
`D_n = lcm(1..4n)/Φ_n` (`Dmult`, `Phi`, `RemovablePrime`).

## Modules and the corresponding sections of the paper

Paths are relative to `lean/MuPi/`.

| Lean file | content | paper (`K2H_paper_v3`) |
|---|---|---|
| `HataLemma.lean` | `exponent_le_of_forms`: Hata's measure lemma (limsup form) | §1.2, App. A.9 |
| `K2H/Defs.lean` | definitions | §1.3 |
| `K2H/PInt.lean` | `p`-integers of `ℂ` (`PInt`), the `√2`-adic filtration `V2`, `exists_int_of_forall_PInt` | §5.1, §5.4 |
| `K2H/LinearForm.lean` | primitive pairs: `primPair_unique`, `segment_integral_of_primPair`, `J534_eq_of_primPair` | §4.1 |
| `K2H/QForm.lean` | the `W,Y` recursion: `exists_primitive_WY`, `exists_rational_primPair` (rationality) | §4.2 |
| `K2H/PF.lean` | partial fractions on `ℂ ∖ {0, ±√2}`: `Rep.ext_of_eval` (uniqueness), `Rep.hasDerivAt_eval`, `Rep.hasDerivAt_primFun`, `exists_rep` (over a subring), `InA` | §5.1, App. A.3 |
| `K2H/OddPrimes.lean` | `oddPrime_trivial`, `removable_decomp`, `oddPrime_removable` | §5.2, §5.3 |
| `K2H/TwoAdic.lean` | `twoAdic_primitive`: the coordinate `w`, the atoms, their valuations | §5.4, App. A.5 |
| `K2H/Integrality.lean` | `theoremA`: `J_n = u_n + (c_n/2)π`, `D_n u_n ∈ ℤ`, `D_n c_n/2 ∈ ℤ` | §5.5 |
| `K2H/ResidueLink.lean` | `residue_eq_cPS`: the residue constant is the power-series coefficient | §6 |
| `K2H/Forms.lean` | `linear_forms` | §4–§6 |
| `K2H/Growth.lean` | `cPS_pos`, `cPS_supermul`, `cPS_growth` (`r ≤ 10.540357`, Fekete) | §6 |
| `K2H/ContourDefs.lean`, `ContourCert.lean`, `ContourBound.lean` | `f534_le_seg1/2`, `rho_le` (`ρ ≤ e^{-6.530134}`); Bernstein certificates | §7, App. A.7 |
| `K2H/Decay.lean` | `J534_norm_le : ‖J_n‖ ≤ 4ρ^n` | §7 |
| `K2H/MultRate.lean` | `windowPrime_removable`, `DmultK_rate` (from the PNT hypothesis), `varpiK_lower` | §8, App. A.8 |
| `K2H/Reduction.lean` | `exponent_of_linear_forms` | §9, App. A.9 |
| `K2H/Main.lean` | `pi_irrationality_exponent` | §9, §10 |
| `K2H.lean` | older conditional reductions (`pi_exponent_of_newSteps`), superseded by `K2H/Main.lean` | |

Docstrings in the Lean files cite statement numbers (Lemma 3.1, Lemma 4.1, Proposition 5.7,
Lemmas 6.1–6.3, Theorem A, Theorem C) of `K2H_PROOF.md`, an earlier proof draft that is not part of
this repository, and two of them mention the module prefix `RecMath/PiMeasure` under which the files
were developed (`MuPi` here). Use the table above to find the corresponding section of the paper.

## How the formal proof is organised

* **Primitive pairs.** `(G, c)` with `G' = f^n/z − c/z` on `ℂ ∖ {0, ±√2}`; all such pairs have the
  same `c` and the same `G(1+i) − G(1−i)` (`primPair_unique`), and
  `J_n = −i(G(1+i) − G(1−i)) + cπ/2`. Every arithmetic statement is proved for a convenient pair
  and transported by uniqueness; the transcendence of `π` is never used.
* **Rationality** comes from the recursion
  `W^j Y^{-2m}/z = [ (W^{j+1} Y^{1-2m})' − (j+2−2m) W^j Y^{-2(m-1)}/z ] / (8(1−2m))`.
* **Growth.** Only the existence of `lim (1/n) log c_n` (supermultiplicativity + Fekete) and the upper
  bound `r ≤ 10.540357` are needed; the saddle-point value `r = log λ₃` is not formalised.
* **Multiplier.** Only the removable primes of the first `K = 10^5` windows are removed
  (`DmultK`); this costs `< 1.4·10^{-6}` in the rate and avoids a tail argument.
* **Numerics.** `r ≤ 10.540357`, `s ≥ 6.530134`, `ϖ_K ≥ 0.293957`, hence
  `σ ≤ 14.2464`, `τ ≥ 2.824091`, `1 + σ/τ < 6.0446`.

## Checking

Requires [elan](https://github.com/leanprover/elan); the toolchain (`leanprover/lean4:v4.30.0`) and
Mathlib (`v4.30.0`) are pinned in `lean/lean-toolchain` and `lean/lake-manifest.json`.

```
cd lean
lake exe cache get        # downloads the compiled Mathlib (once; needs network)
lake build                # compiles the 20 files of this project, a few minutes
lake env lean Check.lean  # prints the main statement, ExponentLE, and the axioms used
```

The expected axioms are `[propext, Classical.choice, Quot.sound]`. A recorded run is in
`lean/BUILD_LOG.txt`.

`MuPi/K2H/ContourCert.lean` (the Bernstein certificates for the contour bound) was produced by a
generator script using exact rational arithmetic. The script is not included; it is not needed to
trust the result, since Lean checks every certificate in that file.

## Citation

If you refer to this work, please cite the paper as follows (preprint, version 3, not yet peer-reviewed):

```bibtex
@misc{moor2026mupi,
  author       = {Michael Moor},
  title        = {A family of integrals for $\pi$ with the symmetry $z \mapsto 2/z$, and the bound $\mu(\pi) \le 6.0446$},
  year         = {2026},
  howpublished = {\url{https://github.com/mi92/mu-pi-pub}},
  note         = {Preprint, version 3 (3 October 2026). Lean 4 formalisation included. Not peer-reviewed}
}
```
