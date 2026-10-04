import MuPi.HataLemma
import MuPi.K2H.Defs

/-!
# From the linear forms to the irrationality exponent

A general version of the last step: rational linear forms `J_n = u_n + v_n π`, a multiplier `D_n`
that clears the denominators for `n ≥ n₀`, the growth rate `r` of `v_n`, the decay rate `s` of
`J_n` and the rate `C` of `D_n` give `μ(π) ≤ 1 + (r + C)/(s − C)` (Hata's lemma,
`exponent_le_of_forms`).
-/

namespace PiMeasure

open Real

theorem exponent_of_linear_forms (u v : ℕ → ℚ) (D : ℕ → ℕ) (r s C K : ℝ) (n₀ : ℕ)
    (hlin : ∀ n, J534 n = (u n : ℂ) + (v n : ℂ) * (Real.pi : ℂ))
    (hint_u : ∀ n, n₀ ≤ n → ∃ k : ℤ, (D n : ℚ) * u n = k)
    (hint_v : ∀ n, n₀ ≤ n → ∃ k : ℤ, (D n : ℚ) * v n = k)
    (hgrow : ∀ η : ℝ, 0 < η → ∃ n₁ : ℕ, ∀ n, n₁ ≤ n →
      Real.exp ((r - η) * n) ≤ |(v n : ℝ)| ∧ |(v n : ℝ)| ≤ Real.exp ((r + η) * n))
    (hK : 0 < K) (hdecay : ∀ n, ‖J534 n‖ ≤ K * Real.exp (-s * n))
    (hD : ∀ η : ℝ, 0 < η → ∃ n₁ : ℕ, ∀ n, n₁ ≤ n →
      Real.exp ((C - η) * n) ≤ (D n : ℝ) ∧ (D n : ℝ) ≤ Real.exp ((C + η) * n))
    (hσ0 : 0 < r + C) (hτ0 : 0 < s - C) (μ : ℝ) (hμ : 1 + (r + C) / (s - C) < μ) :
    ExponentLE Real.pi μ := by
  -- integer sequences `q n = D_n v_n`, `p' n = D_n u_n` (for `n ≥ n₀`)
  have hv : ∀ n, ∃ k : ℤ, n₀ ≤ n → (D n : ℝ) * (v n : ℝ) = (k : ℝ) := by
    intro n
    by_cases hn : n₀ ≤ n
    · obtain ⟨k, hk⟩ := hint_v n hn
      exact ⟨k, fun _ => by exact_mod_cast hk⟩
    · exact ⟨0, fun h => absurd h hn⟩
  have hu : ∀ n, ∃ k : ℤ, n₀ ≤ n → (D n : ℝ) * (u n : ℝ) = (k : ℝ) := by
    intro n
    by_cases hn : n₀ ≤ n
    · obtain ⟨k, hk⟩ := hint_u n hn
      exact ⟨k, fun _ => by exact_mod_cast hk⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose q hq using hv
  choose p' hp' using hu
  have hD0 : ∀ n, (0 : ℝ) ≤ (D n : ℝ) := fun n => Nat.cast_nonneg _
  refine exponent_le_of_forms Real.pi irrational_pi q (fun n => -p' n) (r + C) (s - C) hσ0 hτ0
    ?_ ?_ μ hμ
  · -- growth of `q n`
    intro η hη
    obtain ⟨n₁, h1⟩ := hgrow (η / 2) (by positivity)
    obtain ⟨n₂, h2⟩ := hD (η / 2) (by positivity)
    refine ⟨max (max n₁ n₂) n₀, fun n hn => ?_⟩
    have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn2 : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn3 : n₀ ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨hv1, hv2⟩ := h1 n hn1
    obtain ⟨hd1, hd2⟩ := h2 n hn2
    rw [← hq n hn3, abs_mul, abs_of_nonneg (hD0 n)]
    constructor
    · calc Real.exp ((r + C - η) * n)
          = Real.exp ((C - η / 2) * n) * Real.exp ((r - η / 2) * n) := by
            rw [← Real.exp_add]
            congr 1
            ring
        _ ≤ (D n : ℝ) * |(v n : ℝ)| :=
            mul_le_mul hd1 hv1 (Real.exp_pos _).le (hD0 n)
    · calc (D n : ℝ) * |(v n : ℝ)|
          ≤ Real.exp ((C + η / 2) * n) * Real.exp ((r + η / 2) * n) :=
            mul_le_mul hd2 hv2 (abs_nonneg _) (Real.exp_pos _).le
        _ = Real.exp ((r + C + η) * n) := by
            rw [← Real.exp_add]
            congr 1
            ring
  · -- smallness of `q n π - p n = D_n J_n`
    intro η hη
    obtain ⟨n₂, h2⟩ := hD (η / 2) (by positivity)
    refine ⟨max (max n₂ ⌈Real.log K / (η / 2)⌉₊) n₀, fun n hn => ?_⟩
    have hn2 : n₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn3 : n₀ ≤ n := le_trans (le_max_right _ _) hn
    have hnK : Real.log K / (η / 2) ≤ (n : ℝ) := by
      have h1 : ⌈Real.log K / (η / 2)⌉₊ ≤ n :=
        le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
    have hK' : K ≤ Real.exp (η / 2 * n) := by
      have h1 : Real.log K ≤ η / 2 * n := by
        have := (div_le_iff₀ (by positivity : (0 : ℝ) < η / 2)).1 hnK
        linarith
      calc K = Real.exp (Real.log K) := (Real.exp_log hK).symm
        _ ≤ Real.exp (η / 2 * n) := Real.exp_le_exp.2 h1
    obtain ⟨-, hd2⟩ := h2 n hn2
    have hJ : ‖J534 n‖ = |(u n : ℝ) + (v n : ℝ) * Real.pi| := by
      rw [hlin n]
      have : ((u n : ℂ) + (v n : ℂ) * (Real.pi : ℂ))
          = (((u n : ℝ) + (v n : ℝ) * Real.pi : ℝ) : ℂ) := by
        push_cast
        ring
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    have hform : (q n : ℝ) * Real.pi - ((-p' n : ℤ) : ℝ)
        = (D n : ℝ) * ((u n : ℝ) + (v n : ℝ) * Real.pi) := by
      rw [Int.cast_neg, ← hq n hn3, ← hp' n hn3]
      ring
    change |(q n : ℝ) * Real.pi - ((-p' n : ℤ) : ℝ)| ≤ Real.exp (-(s - C - η) * n)
    rw [hform, abs_mul, abs_of_nonneg (hD0 n), ← hJ]
    calc (D n : ℝ) * ‖J534 n‖
        ≤ Real.exp ((C + η / 2) * n) * (K * Real.exp (-s * n)) :=
          mul_le_mul hd2 (hdecay n) (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp ((C + η / 2) * n) * (Real.exp (η / 2 * n) * Real.exp (-s * n)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right hK' (Real.exp_pos _).le
      _ = Real.exp (-(s - C - η) * n) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring

end PiMeasure
