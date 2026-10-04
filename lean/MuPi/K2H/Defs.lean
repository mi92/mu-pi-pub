import Mathlib

/-!
# K2H, triple `(5,3,4)`: shared definitions

The objects of Theorem C of `R653/K2H_PROOF.md`:

* `f534`, `J534` : the integrand and the integral `J_n = -i ∫_{1-i}^{1+i} f(z)^n dz/z`;
* `RemovablePrime`, `Phi`, `Dmult` : the arithmetic multiplier `D_n = lcm(1..4n)/Φ_n`;
* `Npoly`, `cPS` : the residue `c_n = Res_{z=0} f(z)^n dz/z`, written as a power-series coefficient
  (`v_n = c_n / 2` is the coefficient of `π`).
-/

open Polynomial

namespace PiMeasure

/-- The integrand of Theorem C of `K2H_PROOF.md` (triple `(5,3,4)`). -/
noncomputable def f534 (z : ℂ) : ℂ :=
  ((z - 1) * (z - 2)) ^ 5 * (z ^ 2 - 2 * z + 2) ^ 3 / (z ^ 4 * (z ^ 2 - 2) ^ 4)

/-- `J n = -i ∫_{1-i}^{1+i} f(z)^n dz/z` along the segment `z = 1 + i t`, `t ∈ [-1, 1]`. -/
noncomputable def J534 (n : ℕ) : ℂ :=
  -Complex.I * ∫ t in (-1 : ℝ)..1,
    (f534 (1 + t * Complex.I)) ^ n / (1 + t * Complex.I) * Complex.I

/-- A prime `p` is removable for the triple `(5,3,4)` at index `n` (Theorem A of `K2H_PROOF.md`). -/
def RemovablePrime (n p : ℕ) : Prop :=
  p.Prime ∧ 4 * n < p ^ 2 ∧ Even (4 * n / p) ∧ (5 * n) % p + (3 * n) % p < (4 * n) % p

instance (n p : ℕ) : Decidable (RemovablePrime n p) := by
  unfold RemovablePrime; infer_instance

/-- `Φ_n`: the product of the removable primes `p ≤ 4n`. -/
def Phi (n : ℕ) : ℕ := ∏ p ∈ (Finset.range (4 * n + 1)).filter (RemovablePrime n), p

/-- The multiplier `D_n = lcm(1,…,4n)/Φ_n` of Theorem A. (`D₁ = 12`, `D₂ = 280`, `D₃ = 27720`.) -/
def Dmult (n : ℕ) : ℕ := Nat.lcmUpto (4 * n) / Phi n

/-- `N(X) = ((X-1)(X-2))^5 (X^2-2X+2)^3`, the numerator of `f534`, over `ℚ`. -/
noncomputable def Npoly : ℚ[X] := ((X - 1) * (X - 2)) ^ 5 * (X ^ 2 - 2 * X + 2) ^ 3

/-- `c_n = Res_{z=0} f(z)^n dz/z`: the coefficient of `X^{4n}` in the power series
`N(X)^n · (X^2-2)^{-4n}`.  (`c_1 = 7345`.) -/
noncomputable def cPS (n : ℕ) : ℚ :=
  PowerSeries.coeff (4 * n)
    (((Npoly ^ n : ℚ[X]) : PowerSeries ℚ) *
      (((X ^ 2 - 2 : ℚ[X]) ^ (4 * n) : ℚ[X]) : PowerSeries ℚ)⁻¹)

end PiMeasure
