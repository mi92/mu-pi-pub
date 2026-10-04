import MuPi.K2H.Integrality
import MuPi.K2H.ResidueLink

/-!
# The linear forms, with `v_n = cPS n / 2`

`J_n = u_n + (c_n/2)·π` for every `n ≥ 0`, where `c_n = cPS n` is the power-series coefficient, and
for `n ≥ 1` the multiplier `Dmult n` clears both denominators.
-/

namespace PiMeasure

open Complex

theorem linear_forms (n : ℕ) :
    ∃ u : ℚ, J534 n = (u : ℂ) + ((cPS n / 2 : ℚ) : ℂ) * (Real.pi : ℂ) ∧
      (1 ≤ n → ∃ k : ℤ, (Dmult n : ℚ) * u = k) ∧
      (1 ≤ n → ∃ k : ℤ, (Dmult n : ℚ) * (cPS n / 2) = k) := by
  obtain ⟨c, u₀, G₀, hG₀, hΔ⟩ := exists_rational_primPair n
  have hG₀' : IsPrimPair n G₀ (c : ℂ) := hG₀
  have hc : c = cPS n := by
    have := residue_eq_cPS n hG₀'
    exact_mod_cast this
  have hJ : J534 n = (u₀ : ℂ) + ((cPS n / 2 : ℚ) : ℂ) * (Real.pi : ℂ) := by
    rw [J534_eq_of_primPair hG₀', hΔ, ← hc]
    push_cast
    linear_combination (-(u₀ : ℂ)) * Complex.I_sq
  refine ⟨u₀, hJ, ?_, ?_⟩
  · intro hn
    obtain ⟨u', c', ⟨G', hG'⟩, hJ', hu', -⟩ := theoremA n hn
    have hcc : c' = cPS n := by
      have := residue_eq_cPS n hG'
      exact_mod_cast this
    have h1 : (u' : ℂ) + ((c' / 2 : ℚ) : ℂ) * (Real.pi : ℂ)
        = (u₀ : ℂ) + ((cPS n / 2 : ℚ) : ℂ) * (Real.pi : ℂ) := hJ'.symm.trans hJ
    rw [hcc] at h1
    have h2 : (u' : ℂ) = (u₀ : ℂ) := by linear_combination h1
    have huu : u' = u₀ := by exact_mod_cast h2
    rw [← huu]
    exact hu'
  · intro hn
    obtain ⟨u', c', ⟨G', hG'⟩, -, -, hv'⟩ := theoremA n hn
    have hcc : c' = cPS n := by
      have := residue_eq_cPS n hG'
      exact_mod_cast this
    rw [← hcc]
    exact hv'

end PiMeasure
