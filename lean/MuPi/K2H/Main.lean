import MuPi.K2H.Forms
import MuPi.K2H.Growth
import MuPi.K2H.Decay
import MuPi.K2H.MultRate
import MuPi.K2H.Reduction
import MuPi.K2H

/-!
# The irrationality exponent of `π` is at most `6.0446`

`pi_irrationality_exponent`: the prime number theorem in the form `θ(x)/x → 1` implies
`ExponentLE π μ` for every `μ > 6.0446`, i.e. `|π − a/b| > b^{-μ}` for all large `b`.

Ingredients (all proved in this directory, for the K2H integrals of the triple `(5,3,4)`):

* `linear_forms` : `J_n = u_n + (c_n/2)π`, and `D_n u_n, D_n c_n/2 ∈ ℤ` (Theorem A);
* `cPS_growth` : `(1/n) log c_n → r ≤ 10.540357`;
* `J534_norm_le`, `rho_le` : `|J_n| ≤ 4 e^{-6.530134 n}`;
* `DmultK_rate`, `varpiK_lower` : the multiplier `lcm(1..4n)/Φ_n^{(K)}` (removable primes in the
  first `K = 10^5` windows) has rate `4 − ϖ_K ≤ 3.706043`;
* `exponent_of_linear_forms` : Hata's lemma.

The prime number theorem is the only hypothesis.
-/

namespace PiMeasure

open Filter Topology

lemma PhiK_dvd_Phi {K n : ℕ} (hn : 4 * K ^ 2 ≤ n) : PhiK K n ∣ Phi n := by
  unfold PhiK Phi
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, windowPrime_removable hn hp.2⟩

lemma PhiK_pos (K n : ℕ) : 0 < PhiK K n :=
  Finset.prod_pos fun p hp => (Finset.mem_filter.1 hp).2.1.pos

lemma Dmult_dvd_DmultK {K n : ℕ} (hn : 4 * K ^ 2 ≤ n) : Dmult n ∣ DmultK K n := by
  obtain ⟨E, hE⟩ := PhiK_dvd_Phi hn
  have h1 : Phi n * Dmult n = Nat.lcmUpto (4 * n) := Nat.mul_div_cancel' (Phi_dvd_lcmUpto n)
  refine ⟨E, ?_⟩
  unfold DmultK
  rw [← h1, hE, mul_assoc, Nat.mul_div_cancel_left _ (PhiK_pos K n)]
  ring

lemma DmultK_pos (K n : ℕ) : 0 < DmultK K n :=
  Nat.div_pos (Nat.le_of_dvd (Nat.lcmUpto_pos _) (PhiK_dvd_lcmUpto K n)) (PhiK_pos K n)

/-- **Main theorem.** The prime number theorem (in the form `θ(x) ~ x`) implies that the
irrationality exponent of `π` is at most `6.0446`. -/
theorem pi_irrationality_exponent
    (hPNT : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1)) :
    ∀ μ : ℝ, 6.0446 < μ → ExponentLE Real.pi μ := by
  intro μ hμ
  obtain ⟨r, hr0, hr, hgrow⟩ := cPS_growth
  choose u hu using linear_forms
  have hD := DmultK_rate hPNT 100000
  have hCle : 4 - varpiK 100000 ≤ 3.706043 := by
    have := varpiK_lower
    linarith
  have hC0 : 0 ≤ 4 - varpiK 100000 := by
    by_contra hneg
    rw [not_le] at hneg
    obtain ⟨n₁, h⟩ := hD (-(4 - varpiK 100000) / 2) (by linarith)
    have h1 := (h (max n₁ 1) (le_max_left _ _)).2
    have hpos : (1 : ℝ) ≤ (DmultK 100000 (max n₁ 1) : ℝ) := by
      exact_mod_cast DmultK_pos 100000 (max n₁ 1)
    have hlt : Real.exp ((4 - varpiK 100000 + -(4 - varpiK 100000) / 2) * ((max n₁ 1 : ℕ) : ℝ))
        < 1 := by
      rw [Real.exp_lt_one_iff]
      have hn1 : (1 : ℝ) ≤ ((max n₁ 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right n₁ 1
      nlinarith
    linarith
  apply exponent_of_linear_forms (fun n => u n) (fun n => cPS n / 2)
    (fun n => DmultK 100000 n) r 6.530134 (4 - varpiK 100000) 4 (max 1 (4 * 100000 ^ 2))
  · exact fun n => (hu n).1
  · intro n hn
    have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : 4 * 100000 ^ 2 ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨k, hk⟩ := (hu n).2.1 hn1
    obtain ⟨E, hE⟩ := Dmult_dvd_DmultK hn2
    refine ⟨E * k, ?_⟩
    rw [hE]
    push_cast
    linear_combination (E : ℚ) * hk
  · intro n hn
    have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : 4 * 100000 ^ 2 ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨k, hk⟩ := (hu n).2.2 hn1
    obtain ⟨E, hE⟩ := Dmult_dvd_DmultK hn2
    refine ⟨E * k, ?_⟩
    rw [hE]
    push_cast
    linear_combination (E : ℚ) * hk
  · -- growth of `v n = cPS n / 2`
    intro η hη
    obtain ⟨n₁, h1⟩ := hgrow (η / 2) (by positivity)
    refine ⟨max n₁ ⌈2 * Real.log 2 / η⌉₊, fun n hn => ?_⟩
    obtain ⟨ha, hb⟩ := h1 n (le_trans (le_max_left _ _) hn)
    have hpos : (0 : ℝ) < (cPS n : ℝ) := by exact_mod_cast cPS_pos n
    have habs : |((cPS n / 2 : ℚ) : ℝ)| = (cPS n : ℝ) / 2 := by
      push_cast
      rw [abs_of_pos (by positivity)]
    rw [habs]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    constructor
    · have hn2 : 2 * Real.log 2 / η ≤ (n : ℝ) :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hn)
      have hlog : Real.log 2 ≤ η / 2 * n := by
        rw [div_le_iff₀ hη] at hn2
        linarith
      have h2 : (2 : ℝ) ≤ Real.exp (η / 2 * n) := by
        calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          _ ≤ Real.exp (η / 2 * n) := Real.exp_le_exp.2 hlog
      have h3 : Real.exp ((r - η) * n) * Real.exp (η / 2 * n) = Real.exp ((r - η / 2) * n) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h4 : Real.exp ((r - η) * n) * 2 ≤ (cPS n : ℝ) := by
        calc Real.exp ((r - η) * n) * 2
            ≤ Real.exp ((r - η) * n) * Real.exp (η / 2 * n) :=
              mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
          _ = Real.exp ((r - η / 2) * n) := h3
          _ ≤ (cPS n : ℝ) := ha
      linarith
    · have hmono : Real.exp ((r + η / 2) * n) ≤ Real.exp ((r + η) * n) := by
        apply Real.exp_le_exp.2
        nlinarith
      linarith
  · norm_num
  · -- decay of `J_n`
    intro n
    obtain ⟨c, u₀, G₀, hG₀, -⟩ := exists_rational_primPair n
    have h := J534_norm_le n (G := G₀) (c := (c : ℂ)) hG₀
    have hρ : rho ^ n ≤ Real.exp (-6.530134 * n) := by
      calc rho ^ n ≤ (Real.exp (-6.530134)) ^ n := pow_le_pow_left₀ rho_pos.le rho_le n
        _ = Real.exp (-6.530134 * n) := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
    linarith [mul_le_mul_of_nonneg_left hρ (by norm_num : (0 : ℝ) ≤ 4)]
  · exact hD
  · linarith
  · linarith
  · have h1 : (r + (4 - varpiK 100000)) / (6.530134 - (4 - varpiK 100000))
        ≤ 14.2464 / 2.824091 :=
      div_le_div₀ (by norm_num) (by linarith) (by norm_num) (by linarith)
    have h2 : (1 : ℝ) + 14.2464 / 2.824091 < 6.0446 := by norm_num
    linarith

/-- The same statement with Mathlib's `LiouvilleWith`: `π` is not a Liouville number of any
exponent `p > 6.0446` (assuming the prime number theorem). -/
theorem pi_not_liouvilleWith
    (hPNT : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1)) (p : ℝ) (hp : 6.0446 < p) :
    ¬ LiouvilleWith p Real.pi :=
  (pi_irrationality_exponent hPNT ((6.0446 + p) / 2) (by linarith)).not_liouvilleWith p
    (by linarith)

end PiMeasure
