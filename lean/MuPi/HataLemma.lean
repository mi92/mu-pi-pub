import Mathlib

/-!
# Hata's measure lemma (limsup form)

This file formalises Lemma 7.1 of `R653/K2H_PROOF.md` (Hata, Acta Arith. 63 (1993), Remark 2.1):

If `θ` is irrational and `q n, p n` are integers with
* `exp ((σ - η) n) ≤ |q n| ≤ exp ((σ + η) n)` and
* `|q n θ - p n| ≤ exp (-(τ - η) n)`
for all `n ≥ n₁`, then every rational `a/b` with `b ≥ 1` satisfies
`|θ - a/b| ≥ c · b^{-κ(η)}` with `κ(η) = max (1 + (σ+η)/(τ-η)) ((σ+τ-2η)/(τ-3η))`.
Letting `η → 0` gives the irrationality exponent bound `μ(θ) ≤ 1 + σ/τ`.

Only an *upper* bound for the small linear forms is needed; the lower bound is needed for `|q n|`.
-/

open Real

namespace PiMeasure

/-- `θ` has irrationality exponent at most `μ`: for all large denominators `b` and all integers `a`,
`|θ - a/b| > b^(-μ)`. -/
def ExponentLE (θ μ : ℝ) : Prop :=
  ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b → ∀ a : ℤ, (b : ℝ) ^ (-μ) < |θ - a / b|

/-- An irrational number is never equal to `a / b` with `a : ℤ`, `b : ℕ`. -/
lemma irrational_sub_ne_zero {θ : ℝ} (hθ : Irrational θ) (a : ℤ) (b : ℕ) :
    θ - a / b ≠ 0 := by
  intro h
  have h' : θ = (a : ℝ) / (b : ℝ) := by linarith
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    simp at h'
    exact hθ.ne_zero h'
  · have hb' : ((b : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
    exact (irrational_iff_ne_rational θ).1 hθ a b hb' (by rw [Int.cast_natCast]; exact h')

set_option maxHeartbeats 6000000 in
/-- The key estimate at a fixed `η`. -/
theorem key_bound (θ : ℝ) (hθ : Irrational θ) (q p : ℕ → ℤ) (σ τ η : ℝ)
    (hσ : 0 < σ) (hη : 0 < η) (hητ : 4 * η < τ)
    (n₁ : ℕ)
    (hq : ∀ n, n₁ ≤ n →
      Real.exp ((σ - η) * n) ≤ |(q n : ℝ)| ∧ |(q n : ℝ)| ≤ Real.exp ((σ + η) * n))
    (he : ∀ n, n₁ ≤ n → |(q n : ℝ) * θ - p n| ≤ Real.exp (-(τ - η) * n)) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ b : ℕ, 1 ≤ b → ∀ a : ℤ,
      c * Real.exp (-(max (1 + (σ + η) / (τ - η)) ((σ + τ - 2 * η) / (τ - 3 * η))) * Real.log b)
        ≤ |θ - a / b| := by
  -- the two exponents and the two constants
  set κ₁ : ℝ := 1 + (σ + η) / (τ - η) with hκ₁
  set κ₂ : ℝ := (σ + τ - 2 * η) / (τ - 3 * η) with hκ₂
  set κ : ℝ := max κ₁ κ₂ with hκ
  have hτη : 0 < τ - η := by linarith
  have hτ3η : 0 < τ - 3 * η := by linarith
  have hστ : 0 < σ + τ - 2 * η := by linarith
  have hκ₁pos : 0 < κ₁ := by
    have : 0 < (σ + η) / (τ - η) := div_pos (by linarith) hτη
    linarith
  have hκ₂pos : 0 < κ₂ := div_pos hστ hτ3η
  have hκpos : 0 < κ := lt_max_of_lt_left hκ₁pos
  have hκ₁κ : κ₁ ≤ κ := le_max_left _ _
  have hκ₂κ : κ₂ ≤ κ := le_max_right _ _
  set c₁ : ℝ := Real.exp (-(σ + η) * (n₁ + 1) - κ₁ * Real.log 2) with hc₁
  set c₂ : ℝ := Real.exp (κ₂ * (-(σ + η) * (n₁ + 2) - Real.log 2)) with hc₂
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc₁pos : 0 < c₁ := Real.exp_pos _
  have hc₂pos : 0 < c₂ := Real.exp_pos _
  have hc₁le : c₁ ≤ 1 := by
    rw [hc₁, Real.exp_le_one_iff]
    have : 0 ≤ (σ + η) * (n₁ + 1) := by positivity
    nlinarith [mul_pos hκ₁pos hlog2]
  have hc₂le : c₂ ≤ 1 := by
    rw [hc₂, Real.exp_le_one_iff]
    have h1 : 0 ≤ (σ + η) * (n₁ + 2) := by positivity
    have h2 : -(σ + η) * (n₁ + 2) - Real.log 2 ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos hκ₂pos.le h2
  refine ⟨min c₁ c₂, lt_min hc₁pos hc₂pos, (min_le_left _ _).trans hc₁le, ?_⟩
  intro b hb a
  set B : ℝ := (b : ℝ) with hB
  have hB1 : (1 : ℝ) ≤ B := by rw [hB]; exact_mod_cast hb
  have hBpos : 0 < B := by linarith
  have hlb : 0 ≤ Real.log B := Real.log_nonneg hB1
  set Δ : ℝ := |θ - a / B| with hΔ
  have hΔpos : 0 < Δ := abs_pos.mpr (irrational_sub_ne_zero hθ a b)
  have hexpκ : Real.exp (-κ * Real.log B) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [mul_nonneg hκpos.le hlb]
  -- trivial case `Δ ≥ 1`
  by_cases hΔ1 : 1 ≤ Δ
  · calc min c₁ c₂ * Real.exp (-κ * Real.log B)
        ≤ 1 * 1 := by
          apply mul_le_mul _ hexpκ (Real.exp_pos _).le zero_le_one
          exact (min_le_left _ _).trans hc₁le
      _ ≤ Δ := by linarith
  have hΔ1' : Δ < 1 := lt_of_not_ge hΔ1
  have hlΔ : Real.log Δ < 0 := Real.log_neg hΔpos hΔ1'
  -- the index `N`
  set L₁ : ℝ := (Real.log 2 + Real.log B) / (τ - η) with hL₁
  set L₂ : ℝ := (-Real.log Δ) / (σ + τ - 2 * η) + 1 with hL₂
  have hL₁nn : 0 ≤ L₁ := div_nonneg (by linarith) hτη.le
  have hL₂pos : 0 < L₂ := by
    have : 0 ≤ (-Real.log Δ) / (σ + τ - 2 * η) := div_nonneg (by linarith) hστ.le
    linarith
  set Lm : ℝ := max L₁ L₂ with hLm
  have hLmnn : 0 ≤ Lm := le_trans hL₁nn (le_max_left _ _)
  set N : ℕ := n₁ + ⌈Lm⌉₊ with hN
  have hNn₁ : n₁ ≤ N := Nat.le_add_right _ _
  have hNreal : (N : ℝ) = (n₁ : ℝ) + (⌈Lm⌉₊ : ℝ) := by rw [hN]; push_cast; ring
  have hNge : Lm ≤ (N : ℝ) := by
    rw [hNreal]
    have := Nat.le_ceil Lm
    have h0 : (0 : ℝ) ≤ n₁ := by positivity
    linarith
  have hNle : (N : ℝ) ≤ (n₁ : ℝ) + Lm + 1 := by
    rw [hNreal]
    have := Nat.ceil_lt_add_one hLmnn
    linarith
  have hNL₁ : L₁ ≤ (N : ℝ) := le_trans (le_max_left _ _) hNge
  have hNL₂ : L₂ ≤ (N : ℝ) := le_trans (le_max_right _ _) hNge
  obtain ⟨hq₁, hq₂⟩ := hq N hNn₁
  have hε := he N hNn₁
  set Q : ℝ := (q N : ℝ) with hQ
  set ε : ℝ := Q * θ - p N with hε_def
  have hQpos : 0 < |Q| := lt_of_lt_of_le (Real.exp_pos _) hq₁
  have hQne : Q ≠ 0 := abs_pos.mp hQpos
  -- Fact A: exp(-(τ-η) N) ≤ 1/(2B)
  have hA : Real.exp (-(τ - η) * N) ≤ 1 / (2 * B) := by
    have h2B : 0 < 2 * B := by positivity
    have : Real.log 2 + Real.log B ≤ (τ - η) * N := by
      have := (div_le_iff₀ hτη).1 hNL₁
      linarith
    rw [show (1 : ℝ) / (2 * B) = Real.exp (-(Real.log 2 + Real.log B)) by
          rw [← Real.log_mul (by norm_num) hBpos.ne', Real.exp_neg, Real.exp_log h2B]; ring]
    exact Real.exp_le_exp.2 (by linarith)
  -- Fact B: exp(-(σ+τ-2η) N) < Δ
  have hBfact : Real.exp (-(σ + τ - 2 * η) * N) < Δ := by
    have h1 : (-Real.log Δ) / (σ + τ - 2 * η) + 1 ≤ N := hNL₂
    have h2 : -Real.log Δ + (σ + τ - 2 * η) ≤ (σ + τ - 2 * η) * N := by
      have := (div_le_iff₀ hστ).1 (show (-Real.log Δ) / (σ + τ - 2 * η) ≤ (N : ℝ) - 1 by linarith)
      nlinarith
    calc Real.exp (-(σ + τ - 2 * η) * N) < Real.exp (Real.log Δ) :=
          Real.exp_lt_exp.2 (by linarith)
      _ = Δ := Real.exp_log hΔpos
  -- Claim C: q N * a - p N * b ≠ 0
  have hΔeq : |B * θ - a| = B * Δ := by
    rw [hΔ, ← abs_of_pos hBpos, ← abs_mul, abs_of_pos hBpos]
    congr 1
    field_simp
  have hC : (q N) * a - (p N) * (b : ℤ) ≠ 0 := by
    intro h0
    have h0' : Q * a - (p N : ℝ) * B = 0 := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h0
      push_cast at this
      rw [hQ, hB]; linarith
    -- then B ε = Q (B θ - a)
    have hBe : B * ε = Q * (B * θ - a) := by rw [hε_def]; linarith
    have habs : B * |ε| = |Q| * (B * Δ) := by
      have := congrArg abs hBe
      rw [abs_mul, abs_mul, abs_of_pos hBpos, hΔeq] at this
      exact this
    have hεQ : |ε| = |Q| * Δ := by
      apply mul_left_cancel₀ hBpos.ne'
      rw [habs]; ring
    have hΔQ : Δ = |ε| / |Q| := by
      rw [eq_div_iff hQpos.ne', hεQ]; ring
    have : |ε| / |Q| ≤ Real.exp (-(σ + τ - 2 * η) * N) := by
      rw [div_le_iff₀ hQpos]
      calc |ε| ≤ Real.exp (-(τ - η) * N) := hε
        _ = Real.exp (-(σ + τ - 2 * η) * N) * Real.exp ((σ - η) * N) := by
            rw [← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp (-(σ + τ - 2 * η) * N) * |Q| :=
            mul_le_mul_of_nonneg_left hq₁ (Real.exp_pos _).le
    have hcontra : Δ < Δ := by
      calc Δ = |ε| / |Q| := hΔQ
        _ ≤ Real.exp (-(σ + τ - 2 * η) * N) := this
        _ < Δ := hBfact
    exact lt_irrefl _ hcontra
  have hone : (1 : ℝ) ≤ |Q * a - (p N : ℝ) * B| := by
    have := Int.one_le_abs hC
    have h' : ((1 : ℤ) : ℝ) ≤ ((|q N * a - p N * (b : ℤ)| : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    rw [hQ, hB]; exact h'
  -- 1 ≤ B|ε| + |Q| B Δ ≤ 1/2 + |Q| B Δ
  have hBε : B * |ε| ≤ 1 / 2 := by
    calc B * |ε| ≤ B * Real.exp (-(τ - η) * N) := mul_le_mul_of_nonneg_left hε hBpos.le
      _ ≤ B * (1 / (2 * B)) := mul_le_mul_of_nonneg_left hA hBpos.le
      _ = 1 / 2 := by field_simp
  have hmain : 1 / 2 ≤ |Q| * (B * Δ) := by
    have hid : Q * a - (p N : ℝ) * B = B * ε - Q * (B * θ - a) := by rw [hε_def]; ring
    have : |Q * a - (p N : ℝ) * B| ≤ B * |ε| + |Q| * (B * Δ) := by
      rw [hid]
      calc |B * ε - Q * (B * θ - a)| ≤ |B * ε| + |Q * (B * θ - a)| := abs_sub _ _
        _ = B * |ε| + |Q| * (B * Δ) := by rw [abs_mul, abs_mul, abs_of_pos hBpos, hΔeq]
    linarith
  -- Δ ≥ exp(-(σ+η)N) / (2B)
  have hΔlow : Real.exp (-(σ + η) * N) / (2 * B) ≤ Δ := by
    have hQB : 0 < |Q| * B := by positivity
    have h1 : 1 / (2 * (|Q| * B)) ≤ Δ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h2 : Real.exp (-(σ + η) * N) / (2 * B) ≤ 1 / (2 * (|Q| * B)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : Real.exp (-(σ + η) * N) * |Q| ≤ 1 := by
        calc Real.exp (-(σ + η) * N) * |Q| ≤ Real.exp (-(σ + η) * N) * Real.exp ((σ + η) * N) :=
              mul_le_mul_of_nonneg_left hq₂ (Real.exp_pos _).le
          _ = 1 := by rw [← Real.exp_add, show -(σ + η) * (N : ℝ) + (σ + η) * N = 0 by ring, Real.exp_zero]
      nlinarith [hBpos]
    linarith
  -- the final bound, two cases
  have hexpN : Real.exp (-(σ + η) * ((n₁ : ℝ) + Lm + 1)) ≤ Real.exp (-(σ + η) * N) :=
    Real.exp_le_exp.2 (by nlinarith [hNle, add_pos hσ hη])
  have h2B : (1 : ℝ) / (2 * B) = Real.exp (-(Real.log 2 + Real.log B)) := by
    rw [← Real.log_mul (by norm_num) hBpos.ne', Real.exp_neg, Real.exp_log (by positivity)]
    ring
  have hΔlow' : Real.exp (-(σ + η) * ((n₁ : ℝ) + Lm + 1) - (Real.log 2 + Real.log B)) ≤ Δ := by
    calc Real.exp (-(σ + η) * ((n₁ : ℝ) + Lm + 1) - (Real.log 2 + Real.log B))
        = Real.exp (-(σ + η) * ((n₁ : ℝ) + Lm + 1)) * (1 / (2 * B)) := by
          rw [h2B, ← Real.exp_add, sub_eq_add_neg]
      _ ≤ Real.exp (-(σ + η) * N) * (1 / (2 * B)) :=
          mul_le_mul_of_nonneg_right hexpN (by positivity)
      _ = Real.exp (-(σ + η) * N) / (2 * B) := by ring
      _ ≤ Δ := hΔlow
  have hκlog : Real.exp (-κ * Real.log B) ≤ Real.exp (-κ₁ * Real.log B) ∧
      Real.exp (-κ * Real.log B) ≤ Real.exp (-κ₂ * Real.log B) :=
    ⟨Real.exp_le_exp.2 (by nlinarith), Real.exp_le_exp.2 (by nlinarith)⟩
  rcases le_total L₂ L₁ with hcase | hcase
  · -- case Lm = L₁
    have hLmeq : Lm = L₁ := max_eq_left hcase
    have hkey : -(σ + η) * ((n₁ : ℝ) + L₁ + 1) - (Real.log 2 + Real.log B)
        = (-(σ + η) * (n₁ + 1) - κ₁ * Real.log 2) + (-κ₁ * Real.log B) := by
      rw [hL₁, hκ₁]; field_simp; ring
    calc min c₁ c₂ * Real.exp (-κ * Real.log B) ≤ c₁ * Real.exp (-κ₁ * Real.log B) :=
          mul_le_mul (min_le_left _ _) hκlog.1 (Real.exp_pos _).le hc₁pos.le
      _ = Real.exp (-(σ + η) * ((n₁ : ℝ) + L₁ + 1) - (Real.log 2 + Real.log B)) := by
          rw [hc₁, ← Real.exp_add, hkey]
      _ ≤ Δ := by rw [hLmeq] at hΔlow'; exact hΔlow'
  · -- case Lm = L₂
    have hLmeq : Lm = L₂ := max_eq_right hcase
    rw [hLmeq] at hΔlow'
    -- take logarithms
    have hlogΔ : -(σ + η) * ((n₁ : ℝ) + L₂ + 1) - (Real.log 2 + Real.log B) ≤ Real.log Δ := by
      have := Real.log_le_log (Real.exp_pos _) hΔlow'
      rwa [Real.log_exp] at this
    set β : ℝ := (σ + η) / (σ + τ - 2 * η) with hβ
    have hβlt : β < 1 := by rw [hβ, div_lt_one hστ]; linarith
    have hβpos : 0 < β := div_pos (by linarith) hστ
    have hL₂β : (σ + η) * L₂ = -β * Real.log Δ + (σ + η) := by
      rw [hL₂, hβ]; field_simp; try ring
    -- (1-β) log Δ ≥ -(σ+η)(n₁+2) - log 2 - log B
    have hlin : (1 - β) * Real.log Δ ≥ -(σ + η) * (n₁ + 2) - Real.log 2 - Real.log B := by
      nlinarith [hlogΔ, hL₂β]
    have hκ₂β : κ₂ * (1 - β) = 1 := by
      rw [hκ₂, hβ, one_sub_div hστ.ne',
        show σ + τ - 2 * η - (σ + η) = τ - 3 * η by ring, div_mul_div_comm,
        mul_comm (σ + τ - 2 * η) (τ - 3 * η), div_self (mul_ne_zero hτ3η.ne' hστ.ne')]
    have hlogΔ' : κ₂ * (-(σ + η) * (n₁ + 2) - Real.log 2) + (-κ₂ * Real.log B) ≤ Real.log Δ := by
      have := mul_le_mul_of_nonneg_left hlin hκ₂pos.le
      have h' : κ₂ * ((1 - β) * Real.log Δ) = Real.log Δ := by rw [← mul_assoc, hκ₂β, one_mul]
      nlinarith [h', this]
    calc min c₁ c₂ * Real.exp (-κ * Real.log B) ≤ c₂ * Real.exp (-κ₂ * Real.log B) :=
          mul_le_mul (min_le_right _ _) hκlog.2 (Real.exp_pos _).le hc₂pos.le
      _ = Real.exp (κ₂ * (-(σ + η) * (n₁ + 2) - Real.log 2) + (-κ₂ * Real.log B)) := by
          rw [hc₂, ← Real.exp_add]
      _ ≤ Real.exp (Real.log Δ) := Real.exp_le_exp.2 hlogΔ'
      _ = Δ := Real.exp_log hΔpos


/-- **Hata's measure lemma** (Acta Arith. 63 (1993), Remark 2.1): if integer sequences `q n, p n`
satisfy `|q n| = exp (σ n + o(n))` and `|q n θ - p n| ≤ exp (-τ n + o(n))`, then the irrationality
exponent of `θ` is at most `1 + σ/τ`. Only an upper bound on the small side is needed. -/
theorem exponent_le_of_forms (θ : ℝ) (hθ : Irrational θ) (q p : ℕ → ℤ) (σ τ : ℝ)
    (hσ : 0 < σ) (hτ : 0 < τ)
    (hq : ∀ η : ℝ, 0 < η → ∃ n₁ : ℕ, ∀ n, n₁ ≤ n →
      Real.exp ((σ - η) * n) ≤ |(q n : ℝ)| ∧ |(q n : ℝ)| ≤ Real.exp ((σ + η) * n))
    (he : ∀ η : ℝ, 0 < η → ∃ n₁ : ℕ, ∀ n, n₁ ≤ n →
      |(q n : ℝ) * θ - p n| ≤ Real.exp (-(τ - η) * n))
    (μ : ℝ) (hμ : 1 + σ / τ < μ) : ExponentLE θ μ := by
  -- choose η
  set δ : ℝ := μ - (1 + σ / τ) with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hμpos : 0 < μ := by
    have : 0 < σ / τ := div_pos hσ hτ
    linarith
  set η : ℝ := min (τ / 8) (τ * δ / (6 * μ)) with hη
  have hηpos : 0 < η := lt_min (by positivity) (by positivity)
  have hη1 : η ≤ τ / 8 := min_le_left _ _
  have hη2 : η ≤ τ * δ / (6 * μ) := min_le_right _ _
  have hητ : 4 * η < τ := by linarith
  have hτ3η : 0 < τ - 3 * η := by linarith
  -- the exponent κ = (σ+τ)/(τ-3η) dominates both exponents of `key_bound` and is < μ
  set κ : ℝ := (σ + τ) / (τ - 3 * η) with hκ
  have hκμ : κ < μ := by
    rw [hκ, div_lt_iff₀ hτ3η]
    have h3 : 3 * μ * η ≤ τ * δ / 2 := by
      have := mul_le_mul_of_nonneg_left hη2 (by positivity : (0:ℝ) ≤ 3 * μ)
      calc 3 * μ * η ≤ 3 * μ * (τ * δ / (6 * μ)) := this
        _ = τ * δ / 2 := by field_simp; ring
    have hδτ : τ * δ = μ * τ - σ - τ := by rw [hδ]; field_simp; ring
    nlinarith
  have hκpos : 0 < κ := div_pos (by linarith) hτ3η
  have hdom : max (1 + (σ + η) / (τ - η)) ((σ + τ - 2 * η) / (τ - 3 * η)) ≤ κ := by
    have hτη : 0 < τ - η := by linarith
    apply max_le
    · rw [hκ]
      have : 1 + (σ + η) / (τ - η) = (σ + τ) / (τ - η) := by field_simp; ring
      rw [this]
      apply div_le_div_of_nonneg_left (by linarith) hτ3η (by linarith)
    · rw [hκ]
      apply div_le_div_of_nonneg_right (by linarith) hτ3η.le
  -- get the bounds at this η
  obtain ⟨n₁, hq₁⟩ := hq η hηpos
  obtain ⟨n₂, he₂⟩ := he η hηpos
  obtain ⟨c, hcpos, hc1, hc⟩ := key_bound θ hθ q p σ τ η hσ hηpos hητ (max n₁ n₂)
    (fun n hn => hq₁ n (le_trans (le_max_left _ _) hn))
    (fun n hn => he₂ n (le_trans (le_max_right _ _) hn))
  -- threshold for b
  set b₀ : ℕ := ⌈Real.exp (Real.log (1 / c) / (μ - κ))⌉₊ + 1 with hb₀
  refine ⟨b₀, fun b hb a => ?_⟩
  have hb1 : 1 ≤ b := by
    have : 1 ≤ b₀ := by rw [hb₀]; omega
    omega
  have hB1 : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hBpos : (0 : ℝ) < b := by linarith
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hB1
  have hbound := hc b hb1 a
  -- c * exp(-κmax log b) ≥ c * exp(-κ log b)
  have h1 : c * Real.exp (-κ * Real.log b) ≤ |θ - a / b| := by
    refine le_trans ?_ hbound
    apply mul_le_mul_of_nonneg_left _ hcpos.le
    apply Real.exp_le_exp.2
    nlinarith [hdom, hlb]
  -- b^(-μ) < c * exp(-κ log b), because b > exp(log(1/c)/(μ-κ))
  have hμκ : 0 < μ - κ := by linarith
  have hbig : Real.exp (Real.log (1 / c) / (μ - κ)) < b := by
    have h1' : (⌈Real.exp (Real.log (1 / c) / (μ - κ))⌉₊ : ℝ) + 1 ≤ b := by
      have : b₀ ≤ b := hb
      rw [hb₀] at this
      exact_mod_cast this
    have := Nat.le_ceil (Real.exp (Real.log (1 / c) / (μ - κ)))
    linarith
  have hlogbig : Real.log (1 / c) / (μ - κ) < Real.log b := by
    have := Real.log_lt_log (Real.exp_pos _) hbig
    rwa [Real.log_exp] at this
  have h2 : (b : ℝ) ^ (-μ) < c * Real.exp (-κ * Real.log b) := by
    rw [Real.rpow_def_of_pos hBpos]
    have hc' : c = Real.exp (-Real.log (1 / c)) := by
      rw [Real.log_div one_ne_zero hcpos.ne', Real.log_one, zero_sub, neg_neg, Real.exp_log hcpos]
    rw [hc', ← Real.exp_add]
    apply Real.exp_lt_exp.2
    have := (div_lt_iff₀ hμκ).1 hlogbig
    nlinarith
  exact lt_of_lt_of_le h2 h1

end PiMeasure
