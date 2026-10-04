import MuPi.K2H.ContourCert

/-!
# `|f534| ≤ ρ` on the polygon `1 → zs → 1+i`, and `ρ ≤ exp(-6.530134)`

`zs` is a rational point next to the saddle point `1.20770992… + 0.49394723… i` of `f534`.
The polynomial inequalities come from the generated Bernstein certificates (`ContourCert.lean`).
-/

namespace PiMeasure

open Complex

/-- the rational vertex near the saddle point -/
noncomputable def zs : ℂ := ⟨19787 / 16384, 32371 / 65536⟩

lemma denR_pos {x y : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 5 / 4) : 0 < denR x y := by
  unfold denR
  have h1 : 0 < x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg y]
  have h2 : x ^ 2 - y ^ 2 - 2 < 0 := by nlinarith [sq_nonneg y]
  have h3 : 0 < (x ^ 2 - y ^ 2 - 2) ^ 2 + 4 * x ^ 2 * y ^ 2 := by
    have : 0 < (x ^ 2 - y ^ 2 - 2) ^ 2 := by nlinarith
    have : 0 ≤ 4 * x ^ 2 * y ^ 2 := by positivity
    linarith
  positivity

theorem f534_le_seg1 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖f534 (1 + t * (zs - 1))‖ ≤ rho := by
  intro t h0 h1
  have hre : ((1 : ℂ) + (t : ℂ) * (zs - 1)).re = (1 : ℝ) + ((3403 : ℝ) / 16384) * t := by
    simp [zs]
    ring
  have him : ((1 : ℂ) + (t : ℂ) * (zs - 1)).im = (0 : ℝ) + ((32371 : ℝ) / 65536) * t := by
    simp [zs]
    ring
  rw [← Complex.eta ((1 : ℂ) + (t : ℂ) * (zs - 1))]
  refine f534_norm_le (denR_pos ?_ ?_) (seg1_poly t _ _ h0 h1 hre him)
  · rw [hre]
    nlinarith
  · rw [hre]
    nlinarith

theorem f534_le_seg2 :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖f534 (zs + t * ((1 + Complex.I) - zs))‖ ≤ rho := by
  intro t h0 h1
  have hre : (zs + (t : ℂ) * ((1 + Complex.I) - zs)).re
      = ((19787 : ℝ) / 16384) + ((-3403 : ℝ) / 16384) * t := by
    simp [zs]
    ring
  have him : (zs + (t : ℂ) * ((1 + Complex.I) - zs)).im
      = ((32371 : ℝ) / 65536) + ((33165 : ℝ) / 65536) * t := by
    simp [zs]
    ring
  rw [← Complex.eta (zs + (t : ℂ) * ((1 + Complex.I) - zs))]
  refine f534_norm_le (denR_pos ?_ ?_) (seg2_poly t _ _ h0 h1 hre him)
  · rw [hre]
    nlinarith
  · rw [hre]
    nlinarith

/-- `ρ = 0.001458809 ≤ exp(-6.530134)` -/
theorem rho_le : rho ≤ Real.exp (-6.530134) := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hx := Real.exp_bound' (x := 0.530134) (by norm_num) (by norm_num) (n := 12) (by norm_num)
  have h6 : Real.exp 6.530134 = Real.exp 1 ^ 6 * Real.exp 0.530134 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  have hub : Real.exp 6.530134 ≤ 2.7182818286 ^ 6 *
      (∑ m ∈ Finset.range 12, (0.530134 : ℝ) ^ m / m.factorial +
        (0.530134 : ℝ) ^ 12 * (12 + 1) / (Nat.factorial 12 * 12)) := by
    rw [h6]
    exact mul_le_mul (pow_le_pow_left₀ (Real.exp_pos 1).le he.le 6) hx (Real.exp_pos _).le
      (by positivity)
  have hnum : (2.7182818286 : ℝ) ^ 6 *
      (∑ m ∈ Finset.range 12, (0.530134 : ℝ) ^ m / m.factorial +
        (0.530134 : ℝ) ^ 12 * (12 + 1) / (Nat.factorial 12 * 12)) ≤ 1000000000 / 1458809 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  rw [Real.exp_neg, rho, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  calc Real.exp 6.530134 ≤ _ := hub
    _ ≤ 1000000000 / 1458809 := hnum
    _ = (1458809 / 1000000000 : ℝ)⁻¹ := by norm_num

end PiMeasure
