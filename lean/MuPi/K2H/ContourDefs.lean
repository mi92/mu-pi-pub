import MuPi.K2H.Defs

/-!
# The size of `f534` on a path: real-variable form

`|f534(x+iy)|² = numR x y / denR x y`, so `|f534| ≤ ρ` is the polynomial inequality
`numR ≤ ρ²·denR`.
-/

namespace PiMeasure

/-- `|numerator of f|²` as a function of `x = Re z`, `y = Im z` -/
noncomputable def numR (x y : ℝ) : ℝ :=
  (((x - 1) ^ 2 + y ^ 2) * ((x - 2) ^ 2 + y ^ 2)) ^ 5 *
    (((x - 1) ^ 2 + (y - 1) ^ 2) * ((x - 1) ^ 2 + (y + 1) ^ 2)) ^ 3

/-- `|denominator of f|²` -/
noncomputable def denR (x y : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2) ^ 4 * ((x ^ 2 - y ^ 2 - 2) ^ 2 + 4 * x ^ 2 * y ^ 2) ^ 4

/-- the bound `ρ` for `|f534|` on the contour; `ρ ≤ exp(-6.530134)` -/
noncomputable def rho : ℝ := 1458809 / 1000000000

/-- `ρ²` -/
noncomputable def rhoSq : ℝ := (1458809 / 1000000000) ^ 2

lemma rhoSq_eq : rhoSq = rho ^ 2 := rfl

lemma rho_pos : 0 < rho := by unfold rho; norm_num

lemma normSq_f534 (x y : ℝ) : Complex.normSq (f534 ⟨x, y⟩) = numR x y / denR x y := by
  have h1 : Complex.normSq ((⟨x, y⟩ : ℂ) - 1) = (x - 1) ^ 2 + y ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  have h2 : Complex.normSq ((⟨x, y⟩ : ℂ) - 2) = (x - 2) ^ 2 + y ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  have h3 : Complex.normSq ((⟨x, y⟩ : ℂ) ^ 2 - 2 * ⟨x, y⟩ + 2)
      = ((x - 1) ^ 2 + (y - 1) ^ 2) * ((x - 1) ^ 2 + (y + 1) ^ 2) := by
    simp [Complex.normSq_apply, pow_two]
    ring
  have h4 : Complex.normSq (⟨x, y⟩ : ℂ) = x ^ 2 + y ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  have h5 : Complex.normSq ((⟨x, y⟩ : ℂ) ^ 2 - 2) = (x ^ 2 - y ^ 2 - 2) ^ 2 + 4 * x ^ 2 * y ^ 2 := by
    simp [Complex.normSq_apply, pow_two]
    ring
  unfold f534 numR denR
  rw [map_div₀, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, map_mul, h1, h2, h3, h4, h5]

/-- the polynomial inequality implies the bound for `|f534|` -/
lemma f534_norm_le {x y : ℝ} (hden : 0 < denR x y) (h : numR x y ≤ rhoSq * denR x y) :
    ‖f534 ⟨x, y⟩‖ ≤ rho := by
  have h1 : ‖f534 ⟨x, y⟩‖ ^ 2 ≤ rho ^ 2 := by
    rw [Complex.sq_norm, normSq_f534, div_le_iff₀ hden, ← rhoSq_eq]
    exact h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) rho_pos.le (by norm_num)).1 h1

end PiMeasure
