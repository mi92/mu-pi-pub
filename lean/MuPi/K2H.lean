import MuPi.HataLemma
import MuPi.K2H.Defs

/-!
# The bound `μ(π) ≤ 6.0446` from the K2H linear forms: early conditional reductions

This file contains the first, conditional formalisation: Lemma 2.1 (`K2H_symmetry`), the bridge to
Mathlib's `LiouvilleWith`, and reductions that take the analytic and arithmetic facts as hypotheses
(`pi_exponent_of_K2H_forms`, `pi_exponent_of_inputs`, `pi_exponent_of_newSteps`).

**These hypotheses are now proved**: see `RecMath/PiMeasure/K2H/Main.lean`
(`pi_irrationality_exponent`), whose only hypothesis is the prime number theorem `θ(x) ~ x`, and
`RecMath/PiMeasure/README.md` for the list of modules.
-/

open Real

namespace PiMeasure

/-- **Conditional theorem.** If integer sequences `q n, p n` approximate `π` with growth rate
`σ ≤ 14.2464` and decay rate `τ ≥ 2.824096` (the K2H forms of `K2H_PROOF.md`, Theorem C), then the
irrationality exponent of `π` is at most `6.0446`. -/
theorem pi_exponent_of_K2H_forms (q p : ℕ → ℤ) (σ τ : ℝ)
    (hσ0 : 0 < σ) (hσ : σ ≤ 14.2464) (hτ : 2.824096 ≤ τ)
    (hq : ∀ η : ℝ, 0 < η → ∃ n₁ : ℕ, ∀ n, n₁ ≤ n →
      Real.exp ((σ - η) * n) ≤ |(q n : ℝ)| ∧ |(q n : ℝ)| ≤ Real.exp ((σ + η) * n))
    (he : ∀ η : ℝ, 0 < η → ∃ n₁ : ℕ, ∀ n, n₁ ≤ n →
      |(q n : ℝ) * Real.pi - p n| ≤ Real.exp (-(τ - η) * n)) :
    ∀ μ : ℝ, 6.0446 < μ → ExponentLE Real.pi μ := by
  intro μ hμ
  have hτ0 : (0 : ℝ) < τ := by linarith
  have hratio : σ / τ ≤ 14.2464 / 2.824096 :=
    div_le_div₀ (by norm_num) hσ (by norm_num) hτ
  have hnum : (1 : ℝ) + 14.2464 / 2.824096 < 6.0446 := by norm_num
  exact exponent_le_of_forms Real.pi irrational_pi q p σ τ hσ0 hτ0 hq he μ (by linarith)

/-- `ExponentLE θ μ` implies that `θ` is not `LiouvilleWith p` (Mathlib's notion) for any `p > μ`. -/
theorem ExponentLE.not_liouvilleWith {θ μ : ℝ} (h : ExponentLE θ μ) (pp : ℝ)
    (hp : μ < pp) : ¬ LiouvilleWith pp θ := by
  rintro ⟨C, hC⟩
  obtain ⟨b₀, hb₀⟩ := h
  -- for large `n`, `n^(pp-μ) ≥ C`, so `C / n^pp ≤ n^(-μ) < |θ - m/n|`
  have hpos : 0 < pp - μ := by linarith
  -- threshold: n ≥ max b₀ N with N^(pp-μ) ≥ max C 1
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → max C 1 ≤ (n : ℝ) ^ (pp - μ) := by
    refine ⟨⌈(max C 1) ^ (1 / (pp - μ))⌉₊ + 1, fun n hn => ?_⟩
    have hC1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
    have hn' : (max C 1) ^ (1 / (pp - μ)) ≤ (n : ℝ) := by
      have := Nat.le_ceil ((max C 1) ^ (1 / (pp - μ)))
      have h2 : ((⌈(max C 1) ^ (1 / (pp - μ))⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h2
      linarith
    have hbase : (0 : ℝ) ≤ (max C 1) ^ (1 / (pp - μ)) := by positivity
    calc max C 1 = ((max C 1) ^ (1 / (pp - μ))) ^ (pp - μ) := by
          rw [← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hpos.ne', Real.rpow_one]
      _ ≤ (n : ℝ) ^ (pp - μ) := Real.rpow_le_rpow hbase hn' hpos.le
  have hfreq := hC.and_eventually (Filter.eventually_ge_atTop (max b₀ N + 1))
  obtain ⟨n, ⟨m, hm, hlt⟩, hn⟩ := hfreq.exists
  have hnb₀ : b₀ ≤ n := by omega
  have hnN : N ≤ n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := by linarith
  have h1 := hb₀ n hnb₀ m
  have h2 := hN n hnN
  -- C / n^pp ≤ n^(-μ)
  have h3 : C / (n : ℝ) ^ pp ≤ (n : ℝ) ^ (-μ) := by
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hnpos _)]
    have hsplit : (n : ℝ) ^ (-μ) * (n : ℝ) ^ pp = (n : ℝ) ^ (pp - μ) := by
      rw [← Real.rpow_add hnpos]; congr 1; ring
    rw [hsplit]
    exact le_trans (le_max_left _ _) h2
  linarith

/-- Lemma 2.1 of `K2H_PROOF.md` (the algebraic heart of the construction): the integrand
`f(z) = ((z-1)(z-2))^{e₁} (z²-2z+2)^{e₂} / (z^{a} (z²-2)^{d})` with `a = e₁ + e₂ - d` satisfies
`f(2/z) = (-1)^d · f(z)`. -/
theorem K2H_symmetry (e₁ e₂ a d : ℕ) (hade : e₁ + e₂ = a + d) (z : ℂ) (hz : z ≠ 0)
    (hz2 : z ^ 2 - 2 ≠ 0) :
    ((2 / z - 1) * (2 / z - 2)) ^ e₁ * ((2 / z) ^ 2 - 2 * (2 / z) + 2) ^ e₂ /
        ((2 / z) ^ a * ((2 / z) ^ 2 - 2) ^ d)
      = (-1) ^ d * (((z - 1) * (z - 2)) ^ e₁ * (z ^ 2 - 2 * z + 2) ^ e₂ / (z ^ a * (z ^ 2 - 2) ^ d)) := by
  have h1 : (2 / z - 1) * (2 / z - 2) = 2 * ((z - 1) * (z - 2)) / z ^ 2 := by field_simp; ring
  have h2 : (2 / z) ^ 2 - 2 * (2 / z) + 2 = 2 * (z ^ 2 - 2 * z + 2) / z ^ 2 := by field_simp; ring
  have h3 : (2 / z) ^ 2 - 2 = -2 * (z ^ 2 - 2) / z ^ 2 := by field_simp; ring
  rw [h1, h2, h3]
  have hpow2 : (2 : ℂ) ^ e₁ * 2 ^ e₂ = 2 ^ a * 2 ^ d := by rw [← pow_add, hade, pow_add]
  have hpowz : (z ^ 2) ^ e₁ * (z ^ 2) ^ e₂ = (z ^ 2) ^ a * (z ^ 2) ^ d := by rw [← pow_add, hade, pow_add]
  rw [div_pow, div_pow, div_pow, div_pow, mul_pow, mul_pow, mul_pow]
  field_simp
  have hneg : (-(2 * (z ^ 2 - 2))) ^ d * (-1) ^ d = 2 ^ d * (z ^ 2 - 2) ^ d := by
    rw [← mul_pow, ← mul_pow]; congr 1; ring
  linear_combination
    ((z - 1) ^ e₁ * (z - 2) ^ e₁ * (z * (z - 2) + 2) ^ e₂ * (z ^ a) ^ 2 * (z ^ 2) ^ d * (z ^ 2 - 2) ^ d) * hpow2
    - ((z - 1) ^ e₁ * (z - 2) ^ e₁ * (z * (z - 2) + 2) ^ e₂ * 2 ^ a * 2 ^ d * (z ^ 2 - 2) ^ d) * hpowz
    - ((z - 1) ^ e₁ * (z - 2) ^ e₁ * (z * (z - 2) + 2) ^ e₂ * (z ^ 2) ^ e₁ * (z ^ 2) ^ e₂ * 2 ^ a) * hneg

/-! ## The concrete integral and the list of unformalised inputs -/

/-- The statements of `K2H_PROOF.md` that are **not** formalised: Theorem A (the linear forms and
their denominators), Lemmas 6.1–6.3 (the three rates) and the numerical constants of Theorem C. -/
structure K2HInputs where
  /-- rational part of the linear form -/
  u : ℕ → ℚ
  /-- coefficient of `π` -/
  v : ℕ → ℚ
  /-- the multiplier `D_n = lcm(1..4n)/Φ_n` -/
  D : ℕ → ℕ
  /-- growth rate `r + C` -/
  σ : ℝ
  /-- decay rate `s - C` -/
  τ : ℝ
  /-- Theorem A(i): `J_n = u_n + v_n π` -/
  linear_form : ∀ n, J534 n = (u n : ℂ) + (v n : ℂ) * (Real.pi : ℂ)
  /-- Theorem A(ii): `D_n u_n ∈ ℤ` -/
  int_u : ∀ n, ∃ k : ℤ, (D n : ℚ) * u n = k
  /-- Theorem A(ii): `D_n v_n ∈ ℤ` -/
  int_v : ∀ n, ∃ k : ℤ, (D n : ℚ) * v n = k
  σ_pos : 0 < σ
  /-- Theorem C: `r + C = 14.24639…` -/
  σ_le : σ ≤ 14.2464
  /-- Theorem C: `s - C = 2.82409…` -/
  τ_ge : 2.824096 ≤ τ
  /-- Lemmas 6.1 and 6.3: `(1/n) log |D_n v_n| → σ` -/
  growth : ∀ η : ℝ, 0 < η → ∃ n₁ : ℕ, ∀ n, n₁ ≤ n →
    Real.exp ((σ - η) * n) ≤ |(D n : ℝ) * (v n : ℝ)| ∧
      |(D n : ℝ) * (v n : ℝ)| ≤ Real.exp ((σ + η) * n)
  /-- Lemmas 6.2 and 6.3: `limsup (1/n) log |D_n J_n| ≤ -τ` -/
  decay : ∀ η : ℝ, 0 < η → ∃ n₁ : ℕ, ∀ n, n₁ ≤ n →
    ‖(D n : ℂ) * J534 n‖ ≤ Real.exp (-(τ - η) * n)

/-- **Main conditional theorem.** Given the unformalised inputs `K2HInputs` (Theorem A and
Lemmas 6.1–6.3 of `K2H_PROOF.md` for the integral `J534`), the irrationality exponent of `π` is at
most `6.0446`. -/
theorem pi_exponent_of_inputs (I : K2HInputs) : ∀ μ : ℝ, 6.0446 < μ → ExponentLE Real.pi μ := by
  -- the integer sequences
  choose kv hkv using I.int_v
  choose ku hku using I.int_u
  have hq : ∀ n, ((kv n : ℤ) : ℝ) = (I.D n : ℝ) * (I.v n : ℝ) := by
    intro n
    have h : ((I.D n : ℝ) * (I.v n : ℝ)) = ((kv n : ℤ) : ℝ) := by exact_mod_cast hkv n
    exact h.symm
  have hp : ∀ n, (((-ku n : ℤ)) : ℝ) = -((I.D n : ℝ) * (I.u n : ℝ)) := by
    intro n
    have h : ((I.D n : ℝ) * (I.u n : ℝ)) = ((ku n : ℤ) : ℝ) := by exact_mod_cast hku n
    rw [Int.cast_neg, h]
  -- `q n π - p n = D n * J n`
  have hform : ∀ n, ((((kv n : ℤ) : ℝ) * Real.pi - (((-ku n : ℤ)) : ℝ) : ℝ) : ℂ)
      = (I.D n : ℂ) * J534 n := by
    intro n
    rw [I.linear_form n, hq n, hp n]
    push_cast; ring
  refine pi_exponent_of_K2H_forms kv (fun n => -ku n) I.σ I.τ I.σ_pos I.σ_le I.τ_ge ?_ ?_
  · intro η hη
    obtain ⟨n₁, h⟩ := I.growth η hη
    exact ⟨n₁, fun n hn => by rw [hq n]; exact h n hn⟩
  · intro η hη
    obtain ⟨n₁, h⟩ := I.decay η hη
    refine ⟨n₁, fun n hn => ?_⟩
    have := h n hn
    rw [← hform n, Complex.norm_real, Real.norm_eq_abs] at this
    exact this

/-! ## Published tools versus new steps

Following the split "accept what is published, verify what is new":

* **published / standard** — Hata's measure lemma (proved above, nothing assumed); the prime number
  theorem, which enters only through the growth rate of the multiplier (`PublishedPNTConsequence`,
  the argument of Hata 1993, Lemma 2.2 and Zeilberger–Zudilin 2020, Lemma 3);
* **new** — the statements about the concrete integral `J534` and the concrete multiplier `Dmult`
  (`NewSteps`): these are the proof obligations that remain to be formalised.
-/

/-- The NEW claims of `K2H_PROOF.md` for the triple `(5,3,4)`, stated for the concrete integral
`J534` and the concrete multiplier `Dmult`. None of these fields is formalised yet. -/
structure NewSteps where
  /-- rational part of the linear form -/
  u : ℕ → ℚ
  /-- coefficient of `π` -/
  v : ℕ → ℚ
  /-- growth rate of `v n` -/
  r : ℝ
  /-- decay rate of `J534 n` -/
  s : ℝ
  /-- constant in the decay bound -/
  K : ℝ
  /-- Theorem A(i) (Lemmas 2.2, 2.3): `J_n = u_n + v_n π`. -/
  linear_form : ∀ n, J534 n = (u n : ℂ) + (v n : ℂ) * (Real.pi : ℂ)
  /-- Theorem A(ii) (Lemmas 3.1, 4.1, Proposition 5.7): `D_n u_n ∈ ℤ`. -/
  int_u : ∀ n, 1 ≤ n → ∃ k : ℤ, (Dmult n : ℚ) * u n = k
  /-- Theorem A(ii): `D_n v_n ∈ ℤ`. -/
  int_v : ∀ n, 1 ≤ n → ∃ k : ℤ, (Dmult n : ℚ) * v n = k
  /-- Lemma 6.1: `(1/n) log |v_n| → r`. -/
  growth_v : ∀ η : ℝ, 0 < η → ∃ n₁ : ℕ, ∀ n, n₁ ≤ n →
    Real.exp ((r - η) * n) ≤ |(v n : ℝ)| ∧ |(v n : ℝ)| ≤ Real.exp ((r + η) * n)
  K_pos : 0 < K
  /-- Lemma 6.2 with the contour of §8.3: `|J_n| ≤ K e^{-s n}`. -/
  decay_J : ∀ n, ‖J534 n‖ ≤ K * Real.exp (-s * n)

/-- The consequence of the (published) prime number theorem used in the proof (Lemma 6.3):
`(1/n) log D_n → C`. In the paper `C = 4 - ϖ = 3.70604…`. -/
structure PublishedPNTConsequence where
  /-- the limit of `(1/n) log D_n` -/
  C : ℝ
  mult_rate : ∀ η : ℝ, 0 < η → ∃ n₁ : ℕ, ∀ n, n₁ ≤ n →
    Real.exp ((C - η) * n) ≤ (Dmult n : ℝ) ∧ (Dmult n : ℝ) ≤ Real.exp ((C + η) * n)

/-- **The reduction, machine-checked.** The new steps (`NewSteps`), the PNT consequence and the
numerical values `r + C ≤ 14.2464`, `s - C ≥ 2.824096` imply that the irrationality exponent of `π`
is at most `6.0446`. -/
theorem pi_exponent_of_newSteps (N : NewSteps) (P : PublishedPNTConsequence)
    (hσ0 : 0 < N.r + P.C) (hσ : N.r + P.C ≤ 14.2464) (hτ : 2.824096 ≤ N.s - P.C) :
    ∀ μ : ℝ, 6.0446 < μ → ExponentLE Real.pi μ := by
  -- integer sequences `q n = D_n v_n`, `p' n = D_n u_n` (for `n ≥ 1`)
  have hv : ∀ n, ∃ k : ℤ, 1 ≤ n → (Dmult n : ℝ) * (N.v n : ℝ) = (k : ℝ) := by
    intro n
    by_cases hn : 1 ≤ n
    · obtain ⟨k, hk⟩ := N.int_v n hn
      exact ⟨k, fun _ => by exact_mod_cast hk⟩
    · exact ⟨0, fun h => absurd h hn⟩
  have hu : ∀ n, ∃ k : ℤ, 1 ≤ n → (Dmult n : ℝ) * (N.u n : ℝ) = (k : ℝ) := by
    intro n
    by_cases hn : 1 ≤ n
    · obtain ⟨k, hk⟩ := N.int_u n hn
      exact ⟨k, fun _ => by exact_mod_cast hk⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose q hq using hv
  choose p' hp' using hu
  have hD0 : ∀ n, (0 : ℝ) ≤ (Dmult n : ℝ) := fun n => Nat.cast_nonneg _
  refine pi_exponent_of_K2H_forms q (fun n => -p' n) (N.r + P.C) (N.s - P.C) hσ0 hσ hτ ?_ ?_
  · -- growth of `q n`
    intro η hη
    obtain ⟨n₁, h1⟩ := N.growth_v (η / 2) (by positivity)
    obtain ⟨n₂, h2⟩ := P.mult_rate (η / 2) (by positivity)
    refine ⟨max (max n₁ n₂) 1, fun n hn => ?_⟩
    have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn2 : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn3 : 1 ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨hv1, hv2⟩ := h1 n hn1
    obtain ⟨hd1, hd2⟩ := h2 n hn2
    rw [← hq n hn3, abs_mul, abs_of_nonneg (hD0 n)]
    constructor
    · calc Real.exp ((N.r + P.C - η) * n)
          = Real.exp ((P.C - η / 2) * n) * Real.exp ((N.r - η / 2) * n) := by
            rw [← Real.exp_add]; congr 1; ring
        _ ≤ (Dmult n : ℝ) * |(N.v n : ℝ)| :=
            mul_le_mul hd1 hv1 (Real.exp_pos _).le (hD0 n)
    · calc (Dmult n : ℝ) * |(N.v n : ℝ)|
          ≤ Real.exp ((P.C + η / 2) * n) * Real.exp ((N.r + η / 2) * n) :=
            mul_le_mul hd2 hv2 (abs_nonneg _) (Real.exp_pos _).le
        _ = Real.exp ((N.r + P.C + η) * n) := by
            rw [← Real.exp_add]; congr 1; ring
  · -- smallness of `q n π - p n = D_n J_n`
    intro η hη
    obtain ⟨n₂, h2⟩ := P.mult_rate (η / 2) (by positivity)
    refine ⟨max (max n₂ ⌈Real.log N.K / (η / 2)⌉₊) 1, fun n hn => ?_⟩
    have hn2 : n₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn3 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnK : Real.log N.K / (η / 2) ≤ (n : ℝ) := by
      have h1 : ⌈Real.log N.K / (η / 2)⌉₊ ≤ n :=
        le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
    have hK : N.K ≤ Real.exp (η / 2 * n) := by
      have h1 : Real.log N.K ≤ η / 2 * n := by
        have := (div_le_iff₀ (by positivity : (0 : ℝ) < η / 2)).1 hnK
        linarith
      calc N.K = Real.exp (Real.log N.K) := (Real.exp_log N.K_pos).symm
        _ ≤ Real.exp (η / 2 * n) := Real.exp_le_exp.2 h1
    obtain ⟨-, hd2⟩ := h2 n hn2
    -- the linear form as a real number
    have hJ : ‖J534 n‖ = |(N.u n : ℝ) + (N.v n : ℝ) * Real.pi| := by
      rw [N.linear_form n]
      have : ((N.u n : ℂ) + (N.v n : ℂ) * (Real.pi : ℂ))
          = (((N.u n : ℝ) + (N.v n : ℝ) * Real.pi : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    have hform : (q n : ℝ) * Real.pi - ((-p' n : ℤ) : ℝ)
        = (Dmult n : ℝ) * ((N.u n : ℝ) + (N.v n : ℝ) * Real.pi) := by
      rw [Int.cast_neg, ← hq n hn3, ← hp' n hn3]; ring
    show |(q n : ℝ) * Real.pi - ((-p' n : ℤ) : ℝ)| ≤ Real.exp (-(N.s - P.C - η) * n)
    rw [hform, abs_mul, abs_of_nonneg (hD0 n), ← hJ]
    calc (Dmult n : ℝ) * ‖J534 n‖
        ≤ Real.exp ((P.C + η / 2) * n) * (N.K * Real.exp (-N.s * n)) :=
          mul_le_mul hd2 (N.decay_J n) (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp ((P.C + η / 2) * n) * (Real.exp (η / 2 * n) * Real.exp (-N.s * n)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
      _ = Real.exp (-(N.s - P.C - η) * n) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end PiMeasure
