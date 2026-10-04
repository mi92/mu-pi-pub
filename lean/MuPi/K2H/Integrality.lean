import MuPi.K2H.OddPrimes
import MuPi.K2H.TwoAdic

/-!
# Theorem A for the triple `(5,3,4)`

`J_n = u_n + (c_n/2)·π` with rational `u_n`, `c_n`, and `D_n u_n ∈ ℤ`, `D_n c_n/2 ∈ ℤ` for the
multiplier `D_n = lcm(1..4n)/Φ_n` (`Dmult`).

The rational pair comes from the `W,Y`-recursion (`exists_rational_primPair`); for every prime `p`
another primitive pair carries the `p`-adic information (`twoAdic_primitive`, `oddPrime_trivial`,
`oddPrime_removable`), and all primitive pairs have the same constants (`primPair_unique`).
-/

namespace PiMeasure

open Complex

lemma not_removable_two (n : ℕ) : ¬ RemovablePrime n 2 := by
  rintro ⟨-, h1, -, h3⟩
  have hn : n = 0 := by
    norm_num at h1
    omega
  subst hn
  simp at h3

lemma Phi_dvd_lcmUpto (n : ℕ) : Phi n ∣ Nat.lcmUpto (4 * n) := by
  unfold Phi
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Finset.mem_filter.1 hp).2.1.prime
  · intro p hp
    obtain ⟨hr, hrem⟩ := Finset.mem_filter.1 hp
    have hle : p ≤ 4 * n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    unfold Nat.lcmUpto
    exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.2 ⟨hrem.1.one_lt.le, hle⟩)

lemma not_dvd_Phi {n p : ℕ} (hp : p.Prime) (hnr : ¬ RemovablePrime n p) : ¬ p ∣ Phi n := by
  intro h
  unfold Phi at h
  obtain ⟨a, ha, hpa⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 h
  have har := (Finset.mem_filter.1 ha).2
  have hpa' : p = a := (Nat.prime_dvd_prime_iff_eq hp har.1).1 hpa
  exact hnr (hpa' ▸ har)

/-- a non-removable prime keeps its full power in the multiplier -/
lemma pow_log_dvd_Dmult {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hnr : ¬ RemovablePrime n p) :
    p ^ Nat.log p (4 * n) ∣ Dmult n := by
  have h1 : p ^ Nat.log p (4 * n) ∣ Nat.lcmUpto (4 * n) := by
    unfold Nat.lcmUpto
    apply Finset.dvd_lcm (f := id)
    exact Finset.mem_Icc.2 ⟨Nat.one_le_pow _ _ hp.pos, Nat.pow_log_le_self p (by omega)⟩
  have h2 : Phi n * Dmult n = Nat.lcmUpto (4 * n) := Nat.mul_div_cancel' (Phi_dvd_lcmUpto n)
  rw [← h2] at h1
  exact (Nat.Coprime.pow_left _
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_Phi hp hnr))).dvd_of_dvd_mul_left h1

/-- **Theorem A** for the triple `(5,3,4)`. -/
theorem theoremA (n : ℕ) (hn : 1 ≤ n) :
    ∃ u c : ℚ, (∃ G : ℂ → ℂ, IsPrimPair n G (c : ℂ)) ∧
      J534 n = (u : ℂ) + ((c / 2 : ℚ) : ℂ) * (Real.pi : ℂ) ∧
      (∃ k : ℤ, (Dmult n : ℚ) * u = k) ∧ (∃ k : ℤ, (Dmult n : ℚ) * (c / 2) = k) := by
  obtain ⟨c, u, G₀, hG₀, hΔ⟩ := exists_rational_primPair n
  have hG₀' : IsPrimPair n G₀ (c : ℂ) := hG₀
  refine ⟨u, c, ⟨G₀, hG₀'⟩, ?_, ?_, ?_⟩
  · rw [J534_eq_of_primPair hG₀', hΔ]
    push_cast
    linear_combination (-(u : ℂ)) * Complex.I_sq
  · apply exists_int_of_forall_PInt
    intro p hp
    have hcast : (((Dmult n : ℚ) * u : ℚ) : ℂ) = (Dmult n : ℂ) * (u : ℂ) := by
      push_cast
      ring
    rw [hcast]
    by_cases h2 : p = 2
    · subst h2
      obtain ⟨G, c₂, hG, -, hU⟩ := twoAdic_primitive n hn
      obtain ⟨-, hΔeq⟩ := primPair_unique hG₀' hG
      have hu : -I * (G (1 + I) - G (1 - I)) = (u : ℂ) := by
        rw [← hΔeq, hΔ]
        linear_combination (-(u : ℂ)) * Complex.I_sq
      rw [hu] at hU
      obtain ⟨D', hD'⟩ := pow_log_dvd_Dmult hn Nat.prime_two (not_removable_two n)
      have e : (Dmult n : ℂ) * (u : ℂ)
          = (D' : ℂ) * ((2 : ℂ) ^ Nat.log 2 (4 * n) * (u : ℂ)) := by
        rw [hD']
        push_cast
        ring
      rw [e]
      exact PInt.mul Nat.prime_two (PInt.natCast Nat.prime_two D') hU
    · by_cases hrem : RemovablePrime n p
      · obtain ⟨G, cp, hG, hU⟩ := oddPrime_removable n p hrem
        obtain ⟨-, hΔeq⟩ := primPair_unique hG₀' hG
        rw [← hΔeq, hΔ] at hU
        have hu : (u : ℂ) = -I * (I * (u : ℂ)) := by
          linear_combination ((u : ℂ)) * Complex.I_sq
        have hpu : PInt p (u : ℂ) := by
          rw [hu]
          exact PInt.mul hp (PInt.of_isIntegral hp I_isIntegral).neg hU
        exact PInt.mul hp (PInt.natCast hp _) hpu
      · obtain ⟨G, cp, hG, -, hU⟩ := oddPrime_trivial n p hp h2
        obtain ⟨-, hΔeq⟩ := primPair_unique hG₀' hG
        rw [← hΔeq, hΔ] at hU
        obtain ⟨D', hD'⟩ := pow_log_dvd_Dmult hn hp hrem
        have e : (Dmult n : ℂ) * (u : ℂ)
            = ((D' : ℂ) * (-I)) * ((p : ℂ) ^ Nat.log p (4 * n) * (I * (u : ℂ))) := by
          rw [hD']
          push_cast
          linear_combination ((D' : ℂ) * (p : ℂ) ^ Nat.log p (4 * n) * (u : ℂ)) * Complex.I_sq
        rw [e]
        exact PInt.mul hp
          (PInt.mul hp (PInt.natCast hp D') (PInt.of_isIntegral hp I_isIntegral).neg) hU
  · apply exists_int_of_forall_PInt
    intro p hp
    have hcast : (((Dmult n : ℚ) * (c / 2) : ℚ) : ℂ) = (Dmult n : ℂ) * ((c : ℂ) / 2) := by
      push_cast
      ring
    rw [hcast]
    by_cases h2 : p = 2
    · subst h2
      obtain ⟨G, c₂, hG, hc₂, -⟩ := twoAdic_primitive n hn
      obtain ⟨hceq, -⟩ := primPair_unique hG₀' hG
      rw [← hceq] at hc₂
      obtain ⟨D', hD'⟩ := pow_log_dvd_Dmult hn Nat.prime_two (not_removable_two n)
      have hL : 1 ≤ Nat.log 2 (4 * n) :=
        (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 (by omega)
      obtain ⟨L', hL'⟩ : ∃ L', Nat.log 2 (4 * n) = L' + 1 := ⟨Nat.log 2 (4 * n) - 1, by omega⟩
      have e : (Dmult n : ℂ) * ((c : ℂ) / 2) = ((2 ^ L' * D' : ℕ) : ℂ) * (c : ℂ) := by
        rw [hD', hL']
        push_cast
        ring
      rw [e]
      exact PInt.mul Nat.prime_two (PInt.natCast Nat.prime_two _) hc₂
    · obtain ⟨G, cp, hG, hcp, -⟩ := oddPrime_trivial n p hp h2
      obtain ⟨hceq, -⟩ := primPair_unique hG₀' hG
      rw [← hceq] at hcp
      have h2inv : PInt p ((2 : ℂ)⁻¹) := two_inv_mem hp h2
      have e : (Dmult n : ℂ) * ((c : ℂ) / 2) = (Dmult n : ℂ) * ((c : ℂ) * (2 : ℂ)⁻¹) := by ring
      rw [e]
      exact PInt.mul hp (PInt.natCast hp _) (PInt.mul hp hcp h2inv)

end PiMeasure
