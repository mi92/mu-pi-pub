import MuPi.K2H.PInt

/-!
# The prime 2 (Proposition 5.7 of `K2H_PROOF.md`, triple `(5,3,4)`)

In the coordinate `w = iε(√2+z)/(√2−z)` the integrand `f(z)^n dz/z` becomes
`(128ε)^{-n}·2iε·k_n(w) dw` with

  `k_n(w) = (1+ε²w²)^{5n} (1−w²)^{3n} w^{-4n} (w²+ε²)^{-4n-1}`.

With `x = (1−w²)/c`, `y = 1 − x = (w²+ε²)/c` one has `1+ε²w² = c (y + 2εx)`, so `k_n` is an explicit
combination of the "atoms" `x^a w^{-4n}` and `y^{-k} w^{-4n}`, whose primitives are explicit and
2-adically controlled.  The result: a primitive `G` of `f^n/z − c/z` with
`2^{⌊log₂ 4n⌋}·(−i)(G(1+i) − G(1−i))` and `c` both 2-integral.
-/

namespace PiMeasure

open Complex Finset

/-! ## Combinatorial lemmas -/

/-- binary digit sum -/
def s₂ (a : ℕ) : ℕ := (Nat.digits 2 a).sum

lemma s₂_two_mul (q : ℕ) : s₂ (2 * q) = s₂ q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · unfold s₂
    rw [Nat.digits_def' (by norm_num) (by omega)]
    simp

lemma two_mul_s₂_le (q : ℕ) : 2 * s₂ q ≤ q + 1 := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp [s₂]
    · have hd : s₂ q = q % 2 + s₂ (q / 2) := by
        unfold s₂
        rw [Nat.digits_def' (by norm_num) hq]
        simp
      rcases Nat.eq_zero_or_pos (q / 2) with h0 | hpos
      · have : s₂ (q / 2) = 0 := by rw [h0]; simp [s₂]
        omega
      · have := ih (q / 2) (by omega)
        omega

lemma s₂_le_log (a : ℕ) : s₂ a ≤ Nat.log 2 a + 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [s₂]
  · unfold s₂
    have hlen := Nat.length_digits 2 a (by norm_num) (by omega)
    have h1 : (Nat.digits 2 a).sum ≤ (Nat.digits 2 a).length * 1 := by
      apply List.sum_le_card_nsmul
      intro d hd
      have := Nat.digits_lt_base (by norm_num : 1 < 2) hd
      omega
    omega

lemma padicValNat_centralBinom (q : ℕ) : padicValNat 2 (Nat.centralBinom q) = s₂ q := by
  have h := @sub_one_mul_padicValNat_choose_eq_sub_sum_digits' 2 q q ⟨Nat.prime_two⟩
  rw [Nat.centralBinom_eq_two_mul_choose, two_mul]
  have h2 : (Nat.digits 2 (q + q)).sum = s₂ q := by
    rw [← two_mul]
    exact s₂_two_mul q
  rw [h2] at h
  unfold s₂ at h ⊢
  omega

/-- `Σ_i (−1)^i C(a,i)/(2i+y) = 2^a a!/∏_{j≤a}(2j+y)`. -/
lemma alt_sum_choose_div (a : ℕ) : ∀ y : ℂ, (∀ j : ℕ, (2 : ℂ) * j + y ≠ 0) →
    ∑ i ∈ range (a + 1), (-1 : ℂ) ^ i * (a.choose i) / (2 * i + y)
      = 2 ^ a * a.factorial / ∏ j ∈ range (a + 1), ((2 : ℂ) * j + y) := by
  induction a with
  | zero =>
    intro y hy
    simp
  | succ a ih =>
    intro y hy
    have hy2 : ∀ j : ℕ, (2 : ℂ) * j + (y + 2) ≠ 0 := by
      intro j
      have := hy (j + 1)
      push_cast at this
      intro h
      apply this
      linear_combination h
    -- recurrence S(a+1,y) = S(a,y) − S(a,y+2)
    have hrec : ∑ i ∈ range (a + 1 + 1), (-1 : ℂ) ^ i * ((a + 1).choose i) / (2 * i + y)
        = ∑ i ∈ range (a + 1), (-1 : ℂ) ^ i * (a.choose i) / (2 * i + y)
          - ∑ i ∈ range (a + 1), (-1 : ℂ) ^ i * (a.choose i) / (2 * i + (y + 2)) := by
      rw [Finset.sum_range_succ' _ (a + 1)]
      have h1 : ∀ i ∈ range (a + 1),
          (-1 : ℂ) ^ (i + 1) * ((a + 1).choose (i + 1)) / (2 * ((i + 1 : ℕ) : ℂ) + y)
            = (-1 : ℂ) ^ (i + 1) * (a.choose (i + 1)) / (2 * ((i + 1 : ℕ) : ℂ) + y)
              - (-1 : ℂ) ^ i * (a.choose i) / (2 * i + (y + 2)) := by
        intro i _
        rw [Nat.choose_succ_succ]
        push_cast
        have e : (2 : ℂ) * (i + 1) + y = 2 * i + (y + 2) := by ring
        rw [e]
        ring
      rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]
      have h2 : ∑ i ∈ range (a + 1), (-1 : ℂ) ^ i * (a.choose i) / (2 * i + y)
          = ∑ i ∈ range (a + 1),
              (-1 : ℂ) ^ (i + 1) * (a.choose (i + 1)) / (2 * ((i + 1 : ℕ) : ℂ) + y)
            + (-1 : ℂ) ^ 0 * (a.choose 0) / (2 * ((0 : ℕ) : ℂ) + y) := by
        rw [← Finset.sum_range_succ' (fun i => (-1 : ℂ) ^ i * (a.choose i) / (2 * (i : ℂ) + y))
          (a + 1)]
        rw [Finset.sum_range_succ _ (a + 1)]
        simp
      rw [h2]
      simp
      ring
    rw [hrec, ih y hy, ih (y + 2) hy2]
    -- products
    have hP1 : ∏ j ∈ range (a + 1 + 1), ((2 : ℂ) * j + y)
        = (∏ j ∈ range (a + 1), ((2 : ℂ) * j + y)) * (2 * ((a + 1 : ℕ) : ℂ) + y) :=
      Finset.prod_range_succ _ _
    have hP2 : ∏ j ∈ range (a + 1 + 1), ((2 : ℂ) * j + y)
        = (∏ j ∈ range (a + 1), ((2 : ℂ) * j + (y + 2))) * y := by
      rw [Finset.prod_range_succ' _ (a + 1)]
      congr 1
      · apply Finset.prod_congr rfl
        intro j _
        push_cast
        ring
      · simp
    have hy0 : y ≠ 0 := by simpa using hy 0
    have hQ1 : ∏ j ∈ range (a + 1), ((2 : ℂ) * j + y) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => hy j
    have hQ2 : ∏ j ∈ range (a + 1), ((2 : ℂ) * j + (y + 2)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => hy2 j
    have hlast : (2 : ℂ) * ((a + 1 : ℕ) : ℂ) + y ≠ 0 := hy (a + 1)
    rw [hP1]
    have hrel : (∏ j ∈ range (a + 1), ((2 : ℂ) * j + (y + 2))) * y
        = (∏ j ∈ range (a + 1), ((2 : ℂ) * j + y)) * (2 * ((a + 1 : ℕ) : ℂ) + y) := by
      rw [← hP1, hP2]
    have hQ2' : ∏ j ∈ range (a + 1), ((2 : ℂ) * j + (y + 2))
        = (∏ j ∈ range (a + 1), ((2 : ℂ) * j + y)) * (2 * ((a + 1 : ℕ) : ℂ) + y) / y := by
      rw [← hrel]
      field_simp
    rw [hQ2', Nat.factorial_succ]
    push_cast at hlast ⊢
    field_simp
    ring

/-! ## Primitives in the `w`-coordinate -/

/-- `φ − V/(w²+ε²)` has the primitive `F` on `{w ≠ 0, w²+ε² ≠ 0}`, and `F 1 − F (−1) = U`. -/
def PrimW (φ : ℂ → ℂ) (U V : ℂ) : Prop :=
  ∃ F : ℂ → ℂ, (∀ w : ℂ, w ≠ 0 → w ^ 2 + eps ^ 2 ≠ 0 →
      HasDerivAt F (φ w - V / (w ^ 2 + eps ^ 2)) w) ∧ F 1 - F (-1) = U

namespace PrimW

lemma congr {φ ψ : ℂ → ℂ} {U V : ℂ} (h : PrimW φ U V)
    (hφ : ∀ w : ℂ, w ≠ 0 → w ^ 2 + eps ^ 2 ≠ 0 → φ w = ψ w) : PrimW ψ U V := by
  obtain ⟨F, hF, hU⟩ := h
  exact ⟨F, fun w h0 h1 => by rw [← hφ w h0 h1]; exact hF w h0 h1, hU⟩

lemma add {φ ψ : ℂ → ℂ} {U V U' V' : ℂ} (h : PrimW φ U V) (h' : PrimW ψ U' V') :
    PrimW (fun w => φ w + ψ w) (U + U') (V + V') := by
  obtain ⟨F, hF, hU⟩ := h
  obtain ⟨F', hF', hU'⟩ := h'
  refine ⟨fun w => F w + F' w, fun w h0 h1 => ?_, by rw [← hU, ← hU']; ring⟩
  have := (hF w h0 h1).add (hF' w h0 h1)
  convert this using 1
  ring

lemma const_mul {φ : ℂ → ℂ} {U V : ℂ} (a : ℂ) (h : PrimW φ U V) :
    PrimW (fun w => a * φ w) (a * U) (a * V) := by
  obtain ⟨F, hF, hU⟩ := h
  refine ⟨fun w => a * F w, fun w h0 h1 => ?_, by rw [← hU]; ring⟩
  have := (hF w h0 h1).const_mul a
  convert this using 1
  ring

lemma zero : PrimW (fun _ => 0) 0 0 :=
  ⟨fun _ => 0, fun w _ _ => by simpa using hasDerivAt_const w (0 : ℂ), by simp⟩

lemma sum {ι : Type*} (s : Finset ι) {φ : ι → ℂ → ℂ} {U V : ι → ℂ}
    (h : ∀ i ∈ s, PrimW (φ i) (U i) (V i)) :
    PrimW (fun w => ∑ i ∈ s, φ i w) (∑ i ∈ s, U i) (∑ i ∈ s, V i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simp only [Finset.sum_insert ha]
    exact h1.add h2

end PrimW

/-- `φ` has a primitive pair `(U, V)` with `U ∈ √2^a·O₂` and `V ∈ √2^b·O₂`. -/
def PrimV (φ : ℂ → ℂ) (a b : ℤ) : Prop := ∃ U V : ℂ, PrimW φ U V ∧ V2 a U ∧ V2 b V

namespace PrimV

lemma congr {φ ψ : ℂ → ℂ} {a b : ℤ} (h : PrimV φ a b)
    (hφ : ∀ w : ℂ, w ≠ 0 → w ^ 2 + eps ^ 2 ≠ 0 → φ w = ψ w) : PrimV ψ a b := by
  obtain ⟨U, V, hW, hU, hV⟩ := h
  exact ⟨U, V, hW.congr hφ, hU, hV⟩

lemma add {φ ψ : ℂ → ℂ} {a b : ℤ} (h : PrimV φ a b) (h' : PrimV ψ a b) :
    PrimV (fun w => φ w + ψ w) a b := by
  obtain ⟨U, V, hW, hU, hV⟩ := h
  obtain ⟨U', V', hW', hU', hV'⟩ := h'
  exact ⟨U + U', V + V', hW.add hW', hU.add hU', hV.add hV'⟩

lemma const_mul {φ : ℂ → ℂ} {a b j : ℤ} {κ : ℂ} (hκ : V2 j κ) (h : PrimV φ a b) :
    PrimV (fun w => κ * φ w) (j + a) (j + b) := by
  obtain ⟨U, V, hW, hU, hV⟩ := h
  exact ⟨κ * U, κ * V, hW.const_mul κ, hκ.mul hU, hκ.mul hV⟩

lemma mono {φ : ℂ → ℂ} {a b a' b' : ℤ} (h : PrimV φ a b) (ha : a' ≤ a) (hb : b' ≤ b) :
    PrimV φ a' b' := by
  obtain ⟨U, V, hW, hU, hV⟩ := h
  exact ⟨U, V, hW, hU.mono ha, hV.mono hb⟩

lemma zero (a b : ℤ) : PrimV (fun _ => 0) a b := ⟨0, 0, PrimW.zero, V2.zero a, V2.zero b⟩

lemma sum {ι : Type*} (s : Finset ι) {φ : ι → ℂ → ℂ} {a b : ℤ}
    (h : ∀ i ∈ s, PrimV (φ i) a b) : PrimV (fun w => ∑ i ∈ s, φ i w) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero a b
  | insert c s hc ih =>
    have h1 := h c (Finset.mem_insert_self c s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simp only [Finset.sum_insert hc]
    exact h1.add h2

end PrimV

/-! ### Atom 1: monomials -/

lemma primW_zpow (k : ℤ) (hk : k + 1 ≠ 0) :
    PrimW (fun w => w ^ k) ((1 - (-1 : ℂ) ^ (k + 1)) / (k + 1)) 0 := by
  have hk' : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast hk
  refine ⟨fun w => w ^ (k + 1) / ((k : ℂ) + 1), fun w h0 _ => ?_, ?_⟩
  · have h := (hasDerivAt_zpow (k + 1) w (Or.inl h0)).div_const ((k : ℂ) + 1)
    convert h using 1
    rw [zero_div, sub_zero, add_sub_cancel_right]
    push_cast
    field_simp
  · simp only [one_zpow]
    rw [sub_div]

/-- even exponents: `∫_{-1}^{1} w^{2i-2m} dw = 2/(2i-2m+1)` -/
lemma primW_even_zpow (i m : ℕ) :
    PrimW (fun w => w ^ (2 * (i : ℤ) - 2 * m)) (2 / (2 * (i : ℂ) + (1 - 2 * m))) 0 := by
  have hodd : Odd (2 * (i : ℤ) - 2 * m + 1) := ⟨(i : ℤ) - m, by ring⟩
  have hne : 2 * (i : ℤ) - 2 * m + 1 ≠ 0 := by
    intro h
    rw [h] at hodd
    simp at hodd
  have := primW_zpow (2 * (i : ℤ) - 2 * m) hne
  rw [hodd.neg_one_zpow] at this
  convert this using 2
  · norm_num
  · push_cast
    ring

/-! ### Atom 2: `x^a w^{-2m}` with `x = (1 − w²)/c` -/

/-- the value `∫_{-1}^{1} x^a w^{-2m} dw` -/
noncomputable def Batom (m a : ℕ) : ℂ :=
  cc⁻¹ ^ a * ∑ i ∈ range (a + 1), (-1 : ℂ) ^ i * (a.choose i) * (2 / (2 * (i : ℂ) + (1 - 2 * m)))

lemma primW_xatom (m a : ℕ) :
    PrimW (fun w => ((1 - w ^ 2) / cc) ^ a * (w ^ (2 * m))⁻¹) (Batom m a) 0 := by
  have h := PrimW.sum (range (a + 1))
    (φ := fun i w => (cc⁻¹ ^ a * ((-1 : ℂ) ^ i * (a.choose i))) * w ^ (2 * (i : ℤ) - 2 * m))
    (U := fun i => (cc⁻¹ ^ a * ((-1 : ℂ) ^ i * (a.choose i))) * (2 / (2 * (i : ℂ) + (1 - 2 * m))))
    (V := fun i => (cc⁻¹ ^ a * ((-1 : ℂ) ^ i * (a.choose i))) * 0)
    (fun i _ => (primW_even_zpow i m).const_mul _)
  have hU : ∑ i ∈ range (a + 1),
      (cc⁻¹ ^ a * ((-1 : ℂ) ^ i * (a.choose i))) * (2 / (2 * (i : ℂ) + (1 - 2 * m)))
      = Batom m a := by
    unfold Batom
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hU] at h
  simp only [mul_zero, Finset.sum_const_zero] at h
  refine h.congr fun w h0 _ => ?_
  have key : ∀ i : ℕ, w ^ (2 * (i : ℤ) - 2 * m) = w ^ (2 * i) * (w ^ (2 * m))⁻¹ := by
    intro i
    rw [zpow_sub₀ h0, div_eq_mul_inv]
    norm_cast
  have hexp : (1 - w ^ 2) ^ a = ∑ i ∈ range (a + 1), (-1 : ℂ) ^ i * w ^ (2 * i) * (a.choose i) := by
    rw [show (1 - w ^ 2) = (-(w ^ 2) + 1) by ring, add_pow]
    apply Finset.sum_congr rfl
    intro i _
    rw [one_pow, mul_one, neg_pow, ← pow_mul]
  rw [div_pow, hexp, div_eq_mul_inv, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [key, inv_pow]
  ring

lemma odd_prod_int (m a : ℕ) : Odd (∏ j ∈ range (a + 1), (2 * (j : ℤ) + (1 - 2 * m))) := by
  apply Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one
  intro j _
  exact ⟨(j : ℤ) - m, by ring⟩

lemma Batom_eq (m a : ℕ) :
    Batom m a = cc ^ (-(a : ℤ)) * (2 : ℂ) ^ (a + 1) * (a.factorial : ℂ) *
      (((∏ j ∈ range (a + 1), (2 * (j : ℤ) + (1 - 2 * m)) : ℤ)) : ℂ)⁻¹ := by
  have hy : ∀ j : ℕ, (2 : ℂ) * j + (1 - 2 * (m : ℂ)) ≠ 0 := by
    intro j
    have hodd : Odd (2 * (j : ℤ) + (1 - 2 * m)) := ⟨(j : ℤ) - m, by ring⟩
    have hne : (2 * (j : ℤ) + (1 - 2 * m)) ≠ 0 := by
      intro h
      rw [h] at hodd
      simp at hodd
    have : ((2 * (j : ℤ) + (1 - 2 * m) : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hne
    push_cast at this
    exact this
  have h := alt_sum_choose_div a (1 - 2 * (m : ℂ)) hy
  unfold Batom
  have hsum : ∑ i ∈ range (a + 1), (-1 : ℂ) ^ i * (a.choose i) * (2 / (2 * (i : ℂ) + (1 - 2 * m)))
      = 2 * ∑ i ∈ range (a + 1), (-1 : ℂ) ^ i * (a.choose i) / (2 * i + (1 - 2 * (m : ℂ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, h]
  push_cast
  rw [zpow_neg, zpow_natCast, inv_pow]
  ring

lemma Batom_val (m a : ℕ) : V2 ((a : ℤ) + 2 - 2 * (s₂ a : ℤ)) (Batom m a) := by
  rw [Batom_eq]
  have h1 := V2.cc_zpow (-(a : ℤ))
  have h2 := V2.two_pow (a + 1)
  have h3 := V2.factorial a
  have h4 := V2.inv_odd (odd_prod_int m a)
  have := ((h1.mul h2).mul h3).mul h4
  refine this.mono ?_
  unfold s₂
  push_cast
  omega

/-- every `x`-atom has `U ∈ √2·O₂` -/
lemma Batom_val_one (m a : ℕ) : V2 1 (Batom m a) := by
  refine (Batom_val m a).mono ?_
  have := two_mul_s₂_le a
  omega

/-! ### Atom 3: `(w²+ε²)^{-(j+1)}` -/

/-- `θ`-coefficient of `∫_{-1}^{1} (w²+ε²)^{-(j+1)} dw` -/
noncomputable def betaS : ℕ → ℂ
  | 0 => 1
  | j + 1 => (2 * j + 1) * betaS j / (2 * (j + 1) * eps ^ 2)

/-- rational part of `∫_{-1}^{1} (w²+ε²)^{-(j+1)} dw` -/
noncomputable def alphaS : ℕ → ℂ
  | 0 => 0
  | j + 1 => (2 * cc⁻¹ ^ (j + 1) + (2 * j + 1) * alphaS j) / (2 * (j + 1) * eps ^ 2)

lemma primW_yatom (j : ℕ) :
    PrimW (fun w => ((w ^ 2 + eps ^ 2) ^ (j + 1))⁻¹) (alphaS j) (betaS j) := by
  induction j with
  | zero =>
    refine ⟨fun _ => 0, fun w _ h1 => ?_, by simp [alphaS]⟩
    have := hasDerivAt_const w (0 : ℂ)
    convert this using 1
    simp [betaS]
  | succ j ih =>
    obtain ⟨F, hF, hU⟩ := ih
    have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have he := eps_ne_zero
    refine ⟨fun w => (w * ((w ^ 2 + eps ^ 2) ^ (j + 1))⁻¹ + (2 * j + 1) * F w) /
        (2 * (j + 1) * eps ^ 2), fun w h0 h1 => ?_, ?_⟩
    · have hq : HasDerivAt (fun w : ℂ => w ^ 2 + eps ^ 2) (2 * w) w := by
        simpa using ((hasDerivAt_id w).pow 2).add_const (eps ^ 2)
      have hp : HasDerivAt (fun w : ℂ => ((w ^ 2 + eps ^ 2) ^ (j + 1))⁻¹)
          (-(((j + 1 : ℕ) : ℂ) * (w ^ 2 + eps ^ 2) ^ (j + 1 - 1) * (2 * w)) /
            ((w ^ 2 + eps ^ 2) ^ (j + 1)) ^ 2) w :=
        (hq.pow (j + 1)).inv (pow_ne_zero _ h1)
      have hm : HasDerivAt (fun w : ℂ => w * ((w ^ 2 + eps ^ 2) ^ (j + 1))⁻¹)
          (1 * ((w ^ 2 + eps ^ 2) ^ (j + 1))⁻¹ + w *
            (-(((j + 1 : ℕ) : ℂ) * (w ^ 2 + eps ^ 2) ^ (j + 1 - 1) * (2 * w)) /
              ((w ^ 2 + eps ^ 2) ^ (j + 1)) ^ 2)) w :=
        (hasDerivAt_id' w).mul hp
      have h3 := (hm.add ((hF w h0 h1).const_mul (2 * (j : ℂ) + 1))).div_const
        (2 * ((j : ℂ) + 1) * eps ^ 2)
      refine h3.congr_deriv ?_
      simp only [betaS, Nat.add_sub_cancel]
      push_cast
      field_simp
      ring
    · simp only [alphaS, inv_pow]
      rw [← hU]
      have hc : (1 : ℂ) ^ 2 + eps ^ 2 = cc := by unfold cc; ring
      have hc' : (-1 : ℂ) ^ 2 + eps ^ 2 = cc := by unfold cc; ring
      rw [hc, hc']
      have hcc := cc_ne_zero
      push_cast
      field_simp
      ring

lemma four_eq_s2 : (4 : ℂ) = s2 ^ 4 := by
  rw [show s2 ^ 4 = (s2 ^ 2) ^ 2 by ring, s2_sq]
  norm_num

lemma centralBinom_cast_ne_zero (j : ℕ) : (Nat.centralBinom j : ℂ) ≠ 0 := by
  exact_mod_cast Nat.centralBinom_ne_zero j

lemma centralBinom_succ_cast (j : ℕ) :
    ((j : ℂ) + 1) * (Nat.centralBinom (j + 1) : ℂ) = 2 * (2 * j + 1) * (Nat.centralBinom j : ℂ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ j

lemma betaS_eq (j : ℕ) :
    betaS j = (eps ^ 2)⁻¹ ^ j * (Nat.centralBinom j : ℂ) * (4 : ℂ)⁻¹ ^ j := by
  induction j with
  | zero => simp [betaS]
  | succ j ih =>
    simp only [betaS]
    rw [ih]
    have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have he := eps_ne_zero
    have hC := centralBinom_succ_cast j
    have hC' : (Nat.centralBinom (j + 1) : ℂ) = 2 * (2 * j + 1) * (Nat.centralBinom j : ℂ) / (j + 1) := by
      rw [eq_div_iff hj, mul_comm]
      exact hC
    rw [hC']
    simp only [inv_pow]
    field_simp
    ring

lemma betaS_val (j : ℕ) : V2 (-(4 * (j : ℤ))) (betaS j) := by
  rw [betaS_eq]
  have h1 : V2 0 ((eps ^ 2)⁻¹ ^ j) := by
    have := V2.eps_zpow (-(2 * (j : ℤ)))
    convert this using 1
    rw [zpow_neg, zpow_mul, inv_pow]
    norm_cast
  have h2 : V2 0 (Nat.centralBinom j : ℂ) := V2.natCast _
  have h3 : V2 (-(4 * (j : ℤ))) ((4 : ℂ)⁻¹ ^ j) := by
    refine ⟨1, PInt.one Nat.prime_two, ?_⟩
    rw [mul_one, four_eq_s2, inv_pow, ← pow_mul, zpow_neg]
    norm_cast
  have := (h1.mul h2).mul h3
  simpa using this

/-- auxiliary sequence: `α'_j = C(2j,j)·4^{-j}·ε^{-2j}·A_j` -/
noncomputable def AS : ℕ → ℂ
  | 0 => 0
  | j + 1 => AS j + (s2 ^ 3)⁻¹ ^ (j + 1) * 4 ^ (j + 1) * eps ^ j * eps⁻¹ /
      ((j + 1) * (Nat.centralBinom (j + 1) : ℂ))

lemma alphaS_eq (j : ℕ) :
    alphaS j = (Nat.centralBinom j : ℂ) * (4 : ℂ)⁻¹ ^ j * (eps ^ 2)⁻¹ ^ j * AS j := by
  induction j with
  | zero => simp [alphaS, AS]
  | succ j ih =>
    simp only [alphaS, AS]
    rw [ih]
    have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have he := eps_ne_zero
    have hs := s2_ne_zero
    have hC0 := centralBinom_cast_ne_zero j
    have hC := centralBinom_succ_cast j
    have hC' : (Nat.centralBinom (j + 1) : ℂ) = 2 * (2 * j + 1) * (Nat.centralBinom j : ℂ) / (j + 1) := by
      rw [eq_div_iff hj, mul_comm]
      exact hC
    have h2j : (2 * (j : ℂ) + 1) ≠ 0 := by
      have : ((2 * j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * j)
      push_cast at this
      exact this
    rw [hC', cc_eq]
    simp only [inv_pow, mul_pow]
    field_simp
    ring

lemma AS_val (j : ℕ) : V2 (-2) (AS j) := by
  induction j with
  | zero => simpa [AS] using V2.zero (-2)
  | succ j ih =>
    simp only [AS]
    refine ih.add ?_
    -- the new term is s2^{j+1} ε^j ε⁻¹ / (2 (2j+1) C_j)
    have hC := centralBinom_succ_cast j
    rw [hC]
    have h1 : V2 ((j : ℤ) + 1) ((s2 ^ 3)⁻¹ ^ (j + 1) * 4 ^ (j + 1)) := by
      have := V2.s2_zpow ((j : ℤ) + 1)
      convert this using 1
      rw [four_eq_s2, inv_pow, ← pow_mul, ← pow_mul, inv_mul_eq_div,
        ← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ s2_ne_zero]
      congr 1
      push_cast
      ring
    have h2 : V2 0 (eps ^ j) := V2.of_PInt (PInt.pow Nat.prime_two V2.eps_PInt j)
    have h3 : V2 0 (eps⁻¹) := V2.of_PInt V2.eps_inv_PInt
    have h4 : V2 (-2) ((2 : ℂ)⁻¹) := by
      have := V2.two_zpow (-1)
      simpa using this
    have h5 : V2 0 ((2 * (j : ℂ) + 1)⁻¹) := by
      have := V2.inv_odd (m := 2 * (j : ℤ) + 1) ⟨j, rfl⟩
      convert this using 2
      push_cast
      ring
    have h6 : V2 (-(2 * (s₂ j : ℤ))) ((Nat.centralBinom j : ℂ)⁻¹) := by
      have := V2.inv_natCast_val (Nat.centralBinom_ne_zero j)
      rwa [padicValNat_centralBinom] at this
    have hall := ((((h1.mul h2).mul h3).mul h4).mul h5).mul h6
    have hle := two_mul_s₂_le j
    have hterm : (s2 ^ 3)⁻¹ ^ (j + 1) * 4 ^ (j + 1) * eps ^ j * eps⁻¹ /
          (2 * (2 * (j : ℂ) + 1) * (Nat.centralBinom j : ℂ))
        = (s2 ^ 3)⁻¹ ^ (j + 1) * 4 ^ (j + 1) * eps ^ j * eps⁻¹ * (2 : ℂ)⁻¹ * (2 * (j : ℂ) + 1)⁻¹ *
          (Nat.centralBinom j : ℂ)⁻¹ := by
      rw [div_eq_mul_inv, mul_inv, mul_inv]
      ring
    rw [hterm]
    exact hall.mono (by omega)

lemma four_inv_pow_val (j : ℕ) : V2 (-(4 * (j : ℤ))) ((4 : ℂ)⁻¹ ^ j) := by
  refine ⟨1, PInt.one Nat.prime_two, ?_⟩
  rw [mul_one, four_eq_s2, inv_pow, ← pow_mul, zpow_neg]
  norm_cast

lemma eps_sq_inv_pow_val (j : ℕ) : V2 0 ((eps ^ 2)⁻¹ ^ j) := by
  have := V2.eps_zpow (-(2 * (j : ℤ)))
  convert this using 1
  rw [zpow_neg, zpow_mul, inv_pow]
  norm_cast

lemma alphaS_val (j : ℕ) : V2 (-(4 * (j : ℤ))) (alphaS j) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simpa [alphaS] using V2.zero 0
  · rw [alphaS_eq]
    have h1 : V2 2 (Nat.centralBinom j : ℂ) := by
      obtain ⟨m, hm⟩ := Nat.two_dvd_centralBinom_of_one_le hj
      rw [hm]
      push_cast
      exact V2.mul_PInt V2.two (PInt.natCast Nat.prime_two m)
    have := ((h1.mul (four_inv_pow_val j)).mul (eps_sq_inv_pow_val j)).mul (AS_val j)
    exact this.mono (by omega)

/-! ### Atom 4: `w^{-2m} (w²+ε²)^{-k}` -/

/-- level of the atom `w^{-2m}(w²+ε²)^{-k}` -/
def bnd (k : ℕ) : ℤ := if k = 0 then 2 else 4 - 4 * (k : ℤ)

lemma bnd_zero : bnd 0 = 2 := by simp [bnd]

lemma bnd_succ (k : ℕ) : bnd (k + 1) = -(4 * (k : ℤ)) := by
  simp only [bnd, Nat.succ_ne_zero, if_false]
  push_cast
  ring

lemma bnd_succ_le (k : ℕ) : bnd (k + 1) ≤ bnd k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [bnd_succ, bnd_zero]
    norm_num
  · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [bnd_succ, bnd_succ]
    push_cast
    omega

lemma primV_inv_pow (m : ℕ) (b : ℤ) : PrimV (fun w => (w ^ (2 * m))⁻¹) 2 b := by
  have h := primW_even_zpow 0 m
  refine ⟨_, 0, h.congr ?_, ?_, V2.zero b⟩
  · intro w _ _
    have : (2 * ((0 : ℕ) : ℤ) - 2 * (m : ℤ)) = -((2 * m : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_neg, zpow_natCast]
  · have hodd : Odd (1 - 2 * (m : ℤ)) := ⟨-(m : ℤ), by ring⟩
    have := V2.two.mul (V2.inv_odd hodd)
    convert this using 1
    push_cast
    ring

lemma primV_watom (m : ℕ) :
    ∀ k : ℕ, PrimV (fun w => (w ^ (2 * m))⁻¹ * ((w ^ 2 + eps ^ 2) ^ k)⁻¹) (bnd k) (bnd k) := by
  induction m with
  | zero =>
    intro k
    cases k with
    | zero =>
      rw [bnd_zero]
      exact (primV_inv_pow 0 2).congr (fun w _ _ => by simp)
    | succ j =>
      refine ⟨alphaS j, betaS j, (primW_yatom j).congr (fun w _ _ => by simp), ?_, ?_⟩
      · rw [bnd_succ]
        exact alphaS_val j
      · rw [bnd_succ]
        exact betaS_val j
  | succ m ihm =>
    intro k
    induction k with
    | zero =>
      rw [bnd_zero]
      exact (primV_inv_pow (m + 1) 2).congr (fun w _ _ => by simp)
    | succ j ihk =>
      have h1 := ihk.mono (bnd_succ_le j) (bnd_succ_le j)
      have h2 := PrimV.const_mul (V2.intCast (-1)) (ihm (j + 1))
      rw [zero_add] at h2
      have h4 := PrimV.const_mul (V2.eps_zpow (-2)) (h1.add h2)
      rw [zero_add] at h4
      refine h4.congr ?_
      intro w h0 hw
      have he := eps_ne_zero
      rw [zpow_neg]
      push_cast
      field_simp
      ring

/-- the scaled atom `c^k w^{-2m} (w²+ε²)^{-k}`, `k ≥ 1` -/
lemma primV_cwatom (m k : ℕ) (hk : 1 ≤ k) :
    PrimV (fun w => cc ^ k * ((w ^ (2 * m))⁻¹ * ((w ^ 2 + eps ^ 2) ^ k)⁻¹))
      (4 - (k : ℤ)) (4 - (k : ℤ)) := by
  have hc : V2 (3 * (k : ℤ)) (cc ^ k) := by
    have := V2.cc_zpow (k : ℤ)
    rwa [zpow_natCast] at this
  have := PrimV.const_mul hc (primV_watom m k)
  refine this.mono ?_ ?_ <;>
  · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [bnd_succ]
    push_cast
    omega

/-! ## Assembly of the kernel `k_n` -/

/-- `x = (1 − w²)/c` -/
noncomputable def xw (w : ℂ) : ℂ := (1 - w ^ 2) / cc

/-- `y = 1 − x = (w² + ε²)/c` -/
noncomputable def yw (w : ℂ) : ℂ := (w ^ 2 + eps ^ 2) / cc

lemma xw_add_yw (w : ℂ) : xw w + yw w = 1 := by
  unfold xw yw
  rw [← add_div]
  have : (1 - w ^ 2 + (w ^ 2 + eps ^ 2)) = cc := by unfold cc; ring
  rw [this, div_self cc_ne_zero]

lemma yw_ne_zero {w : ℂ} (hw : w ^ 2 + eps ^ 2 ≠ 0) : yw w ≠ 0 := div_ne_zero hw cc_ne_zero

lemma eps_sq_add : eps ^ 2 + 2 * eps = 1 := by
  unfold eps
  linear_combination s2_sq

lemma primV_xatom (m a : ℕ) (B : ℤ) :
    PrimV (fun w => xw w ^ a * (w ^ (2 * m))⁻¹) ((a : ℤ) + 2 - 2 * (s₂ a : ℤ)) B :=
  ⟨Batom m a, 0, primW_xatom m a, Batom_val m a, V2.zero B⟩

lemma V2_choose_sign (N l : ℕ) : V2 0 ((N.choose l : ℂ) * (-1) ^ l) := by
  have := V2.intCast ((N.choose l : ℤ) * (-1) ^ l)
  push_cast at this
  exact this

/-- `x^{a₀} y^e w^{-2m}`: expand `y = 1 − x`. -/
lemma primV_xy (m a₀ e : ℕ) (lam B : ℤ)
    (hlam : ∀ a : ℕ, a₀ ≤ a → a ≤ a₀ + e → lam ≤ (a : ℤ) + 2 - 2 * (s₂ a : ℤ)) :
    PrimV (fun w => xw w ^ a₀ * yw w ^ e * (w ^ (2 * m))⁻¹) lam B := by
  have h := PrimV.sum (range (e + 1))
    (φ := fun b w => ((e.choose b : ℂ) * (-1) ^ b) * (xw w ^ (a₀ + b) * (w ^ (2 * m))⁻¹))
    (a := lam) (b := B) (fun b hb => by
      have hb' : b ≤ e := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
      have h1 := (primV_xatom m (a₀ + b) B).mono (hlam (a₀ + b) (by omega) (by omega)) (le_refl B)
      have := PrimV.const_mul (V2_choose_sign e b) h1
      rwa [zero_add, zero_add] at this)
  refine h.congr fun w _ _ => ?_
  have hy : yw w = -xw w + 1 := by
    have := xw_add_yw w
    linear_combination this
  rw [hy, add_pow, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [one_pow, mul_one, neg_pow]
  beta_reduce
  ring

/-- the terms with `i < n`: only `x`-atoms with exponent `≥ 3n`. -/
lemma primV_tau_small (n i : ℕ) (hn : 1 ≤ n) (hi : i < n) (B : ℤ) :
    PrimV (fun w => xw w ^ (3 * n + i) * yw w ^ (5 * n - i) * (yw w ^ (4 * n + 1))⁻¹ *
        (w ^ (2 * (2 * n)))⁻¹)
      (2 * (n : ℤ) + 1 - 2 * (Nat.log 2 (4 * n) : ℤ)) B := by
  have h := primV_xy (2 * n) (3 * n + i) (n - 1 - i)
    (2 * (n : ℤ) + 1 - 2 * (Nat.log 2 (4 * n) : ℤ)) B (by
      intro a ha1 ha2
      have hs := s₂_le_log a
      have hlog : Nat.log 2 a ≤ Nat.log 2 (4 * n) := Nat.log_mono_right (by omega)
      omega)
  refine h.congr fun w _ hw => ?_
  have hy := yw_ne_zero hw
  have he : 5 * n - i = (n - 1 - i) + (4 * n + 1) := by omega
  rw [he, pow_add]
  field_simp
  ring

/-- `y^l y^{-j} w^{-2m}` for `j ≥ 1`. -/
lemma primV_ylj (m l j : ℕ) (hj : 1 ≤ j) :
    PrimV (fun w => yw w ^ l * (yw w ^ j)⁻¹ * (w ^ (2 * m))⁻¹)
      (min 1 (4 - (j : ℤ))) (4 - (j : ℤ)) := by
  rcases Nat.lt_or_ge l j with hlt | hge
  · obtain ⟨k, rfl⟩ : ∃ k, j = l + k := ⟨j - l, by omega⟩
    have hk : 1 ≤ k := by omega
    have h := (primV_cwatom m k hk).mono
      (a' := min 1 (4 - ((l + k : ℕ) : ℤ))) (b' := 4 - ((l + k : ℕ) : ℤ))
      (le_trans (min_le_right _ _) (by push_cast; omega)) (by push_cast; omega)
    refine h.congr fun w h0 hw => ?_
    have hy := yw_ne_zero hw
    have hcc := cc_ne_zero
    have hyk : yw w ^ k = (w ^ 2 + eps ^ 2) ^ k / cc ^ k := by
      unfold yw
      rw [div_pow]
    rw [pow_add, hyk]
    field_simp
  · obtain ⟨d, rfl⟩ : ∃ d, l = j + d := ⟨l - j, by omega⟩
    have h := primV_xy m 0 d 1 (4 - (j : ℤ)) (by
      intro a _ _
      have := two_mul_s₂_le a
      omega)
    refine (h.mono (min_le_left _ _) (le_refl _)).congr fun w _ hw => ?_
    have hy := yw_ne_zero hw
    rw [pow_add]
    field_simp

/-- the terms with `i ≥ n`. -/
lemma primV_tau_large (n i : ℕ) (hi : n ≤ i) (hi5 : i ≤ 5 * n) :
    PrimV (fun w => xw w ^ (3 * n + i) * yw w ^ (5 * n - i) * (yw w ^ (4 * n + 1))⁻¹ *
        (w ^ (2 * (2 * n)))⁻¹)
      (min 1 (4 - ((i - n + 1 : ℕ) : ℤ))) (4 - ((i - n + 1 : ℕ) : ℤ)) := by
  have h := PrimV.sum (range (3 * n + i + 1))
    (φ := fun l w => (((3 * n + i).choose l : ℂ) * (-1) ^ l) *
      (yw w ^ l * (yw w ^ (i - n + 1))⁻¹ * (w ^ (2 * (2 * n)))⁻¹))
    (a := min 1 (4 - ((i - n + 1 : ℕ) : ℤ))) (b := 4 - ((i - n + 1 : ℕ) : ℤ)) (fun l _ => by
      have := PrimV.const_mul (V2_choose_sign (3 * n + i) l)
        (primV_ylj (2 * n) l (i - n + 1) (by omega))
      rwa [zero_add, zero_add] at this)
  refine h.congr fun w _ hw => ?_
  have hy := yw_ne_zero hw
  have hx : xw w = -yw w + 1 := by
    have := xw_add_yw w
    linear_combination this
  have hexp : xw w ^ (3 * n + i)
      = ∑ l ∈ range (3 * n + i + 1), ((3 * n + i).choose l : ℂ) * (-1) ^ l * yw w ^ l := by
    rw [hx, add_pow]
    apply Finset.sum_congr rfl
    intro l _
    rw [one_pow, mul_one, neg_pow]
    ring
  have hpow : yw w ^ (5 * n - i) * (yw w ^ (4 * n + 1))⁻¹ = (yw w ^ (i - n + 1))⁻¹ := by
    have he : 4 * n + 1 = (5 * n - i) + (i - n + 1) := by omega
    rw [he, pow_add]
    field_simp
  rw [mul_assoc (xw w ^ (3 * n + i)), hpow, hexp, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- the kernel in the `w`-frame -/
noncomputable def kw (n : ℕ) (w : ℂ) : ℂ :=
  (1 + eps ^ 2 * w ^ 2) ^ (5 * n) * (1 - w ^ 2) ^ (3 * n) * (w ^ (2 * (2 * n)))⁻¹ *
    ((w ^ 2 + eps ^ 2) ^ (4 * n + 1))⁻¹

lemma primV_kw (n : ℕ) (hn : 1 ≤ n) :
    PrimV (kw n) (14 * (n : ℤ) - 2 - 2 * (Nat.log 2 (4 * n) : ℤ)) (14 * (n : ℤ)) := by
  have hsum := PrimV.sum (range (5 * n + 1))
    (φ := fun i w => (((5 * n).choose i : ℂ) * (2 * eps) ^ i) *
      (xw w ^ (3 * n + i) * yw w ^ (5 * n - i) * (yw w ^ (4 * n + 1))⁻¹ * (w ^ (2 * (2 * n)))⁻¹))
    (a := 2 * (n : ℤ) + 1 - 2 * (Nat.log 2 (4 * n) : ℤ)) (b := 2 * (n : ℤ) + 3) (fun i hi => by
      have hi5 : i ≤ 5 * n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hκ : V2 (2 * (i : ℤ)) (((5 * n).choose i : ℂ) * (2 * eps) ^ i) := by
        rw [mul_pow]
        have h2 : V2 0 (eps ^ i) := V2.of_PInt (PInt.pow Nat.prime_two V2.eps_PInt i)
        have := (V2.natCast ((5 * n).choose i)).mul ((V2.two_pow i).mul h2)
        rwa [zero_add, add_zero] at this
      rcases Nat.lt_or_ge i n with hlt | hge
      · have := PrimV.const_mul hκ (primV_tau_small n i hn hlt (2 * (n : ℤ) + 3))
        exact this.mono (by omega) (by omega)
      · have := PrimV.const_mul hκ (primV_tau_large n i hge hi5)
        refine this.mono ?_ ?_
        · rcases le_total (1 : ℤ) (4 - ((i - n + 1 : ℕ) : ℤ)) with h | h
          · rw [min_eq_left h]
            omega
          · rw [min_eq_right h]
            push_cast [Nat.cast_sub hge]
            omega
        · push_cast [Nat.cast_sub hge]
          omega)
  have hc : V2 (12 * (n : ℤ) - 3) (cc ^ (4 * n - 1)) := by
    have := V2.cc_zpow ((4 * n - 1 : ℕ) : ℤ)
    rw [zpow_natCast] at this
    convert this using 1
    omega
  have := PrimV.const_mul hc hsum
  refine (this.mono (by omega) (by omega)).congr fun w _ hw => ?_
  -- the function identity
  have hcc := cc_ne_zero
  have h1 : 1 + eps ^ 2 * w ^ 2 = cc * (2 * eps * xw w + yw w) := by
    unfold xw yw
    field_simp
    linear_combination (w ^ 2 - 1) * eps_sq_add
  have h2 : 1 - w ^ 2 = cc * xw w := by
    unfold xw
    field_simp
  have h3 : w ^ 2 + eps ^ 2 = cc * yw w := by
    unfold yw
    field_simp
  have hpre : cc ^ (5 * n) * cc ^ (3 * n) * (cc ^ (4 * n + 1))⁻¹ = cc ^ (4 * n - 1) := by
    have hcc' : cc ^ (5 * n) * cc ^ (3 * n) = cc ^ (4 * n - 1) * cc ^ (4 * n + 1) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [hcc', mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hcc), mul_one]
  unfold kw
  rw [h1, h2, h3, mul_pow, mul_pow, mul_pow, mul_inv, add_pow, ← hpre]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ## Back to the coordinate `z` -/

/-- the coordinate `w(z) = iε(√2+z)/(√2−z)` -/
noncomputable def wOf (z : ℂ) : ℂ := Complex.I * eps * (s2 + z) / (s2 - z)

lemma wOf_sq (z : ℂ) : wOf z ^ 2 = -(eps ^ 2 * (s2 + z) ^ 2) / (s2 - z) ^ 2 := by
  unfold wOf
  rw [div_pow, mul_pow, mul_pow, Complex.I_sq]
  ring

lemma wOf_sq_add {z : ℂ} (hz : z ≠ s2) :
    wOf z ^ 2 + eps ^ 2 = -(4 * s2 * eps ^ 2 * z) / (s2 - z) ^ 2 := by
  have hq : s2 - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  rw [wOf_sq]
  field_simp
  ring

lemma one_add_wOf {z : ℂ} (hz : z ≠ s2) :
    1 + eps ^ 2 * wOf z ^ 2 = 4 * s2 * eps ^ 2 * ((z - 1) * (z - 2)) / (s2 - z) ^ 2 := by
  have hq : s2 - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  rw [wOf_sq]
  unfold eps
  field_simp
  linear_combination
    (-s2 ^ 4 + s2 ^ 3 * (4 - 2 * z) + s2 ^ 2 * (-z ^ 2 + 8 * z - 8) + s2 * (4 - 4 * z)) * s2_sq

lemma one_sub_wOf {z : ℂ} (hz : z ≠ s2) :
    1 - wOf z ^ 2 = 2 * s2 * eps * (z ^ 2 - 2 * z + 2) / (s2 - z) ^ 2 := by
  have hq : s2 - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  rw [wOf_sq]
  unfold eps
  field_simp
  linear_combination (s2 ^ 2 + s2 * (2 * z - 2) - z ^ 2) * s2_sq

lemma f534_eq_wOf {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ s2) (hz2 : z ≠ -s2) :
    f534 z = (128 * eps)⁻¹ * ((1 + eps ^ 2 * wOf z ^ 2) ^ 5 * (1 - wOf z ^ 2) ^ 3 *
      (wOf z ^ 4)⁻¹ * ((wOf z ^ 2 + eps ^ 2) ^ 4)⁻¹) := by
  have hq : s2 - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz1)
  have hp : s2 + z ≠ 0 := by
    intro h
    apply hz2
    linear_combination h
  have he := eps_ne_zero
  have hs := s2_ne_zero
  have hzz : z ^ 2 - 2 = -((s2 - z) * (s2 + z)) := by linear_combination s2_sq
  have hw4 : wOf z ^ 4 = eps ^ 4 * (s2 + z) ^ 4 / (s2 - z) ^ 4 := by
    unfold wOf
    rw [div_pow, mul_pow, mul_pow, Complex.I_pow_four]
    ring
  rw [one_add_wOf hz1, one_sub_wOf hz1, wOf_sq_add hz1, hw4]
  unfold f534
  rw [hzz]
  have hconst : (4 * s2 * eps ^ 2) * (2 * s2 * eps) ^ 3 = 128 * eps * eps ^ 4 := by
    linear_combination (32 * eps ^ 5 * (s2 ^ 2 + 2)) * s2_sq
  have hne : 128 * eps * eps ^ 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) he) (pow_ne_zero _ he)
  have key : (128 * eps)⁻¹ * ((4 * s2 * eps ^ 2 * ((z - 1) * (z - 2)) / (s2 - z) ^ 2) ^ 5 *
        (2 * s2 * eps * (z ^ 2 - 2 * z + 2) / (s2 - z) ^ 2) ^ 3 *
        (eps ^ 4 * (s2 + z) ^ 4 / (s2 - z) ^ 4)⁻¹ *
        ((-(4 * s2 * eps ^ 2 * z) / (s2 - z) ^ 2) ^ 4)⁻¹)
      = ((4 * s2 * eps ^ 2) * (2 * s2 * eps) ^ 3 / (128 * eps * eps ^ 4)) *
        (((z - 1) * (z - 2)) ^ 5 * (z ^ 2 - 2 * z + 2) ^ 3 /
          (z ^ 4 * (-((s2 - z) * (s2 + z))) ^ 4)) := by
    field_simp
  rw [key, hconst, div_self hne, one_mul]

lemma hasDerivAt_wOf {z : ℂ} (hz : z ≠ s2) :
    HasDerivAt wOf (Complex.I * eps * (2 * s2) / (s2 - z) ^ 2) z := by
  have hq : s2 - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  have h1 : HasDerivAt (fun z : ℂ => Complex.I * eps * (s2 + z)) (Complex.I * eps * 1) z :=
    ((hasDerivAt_id' z).const_add s2).const_mul (Complex.I * eps)
  have h2 : HasDerivAt (fun z : ℂ => s2 - z) (-1) z := (hasDerivAt_id' z).const_sub s2
  have := h1.div h2 hq
  refine this.congr_deriv ?_
  field_simp
  ring

lemma wOf_one_add_I : wOf (1 + Complex.I) = -1 := by
  have hne : s2 - (1 + Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [s2] at this
  unfold wOf
  rw [div_eq_iff hne]
  have heps : eps = s2 - 1 := rfl
  linear_combination Complex.I * eps_mul + eps * Complex.I_sq - heps

lemma wOf_one_sub_I : wOf (1 - Complex.I) = 1 := by
  have hne : s2 - (1 - Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [s2] at this
  unfold wOf
  rw [div_eq_iff hne]
  have heps : eps = s2 - 1 := rfl
  linear_combination Complex.I * eps_mul - eps * Complex.I_sq + heps

lemma V2_128 (n : ℕ) : V2 (-(14 * (n : ℤ))) ((128 * eps)⁻¹ ^ n) := by
  have h1 : V2 (2 * (-(7 * (n : ℤ)))) ((2 : ℂ) ^ (-(7 * (n : ℤ)))) := V2.two_zpow _
  have h2 : V2 0 (eps⁻¹ ^ n) := V2.of_PInt (PInt.pow Nat.prime_two V2.eps_inv_PInt n)
  have h := h1.mul h2
  have e : (128 * eps)⁻¹ ^ n = (2 : ℂ) ^ (-(7 * (n : ℤ))) * eps⁻¹ ^ n := by
    have h2 : (2 : ℂ) ^ (-(7 * (n : ℤ))) = (128 : ℂ)⁻¹ ^ n := by
      rw [zpow_neg, zpow_mul, inv_pow, zpow_natCast]
      norm_num
    rw [h2, mul_inv, mul_pow]
  rw [e]
  exact h.mono (by omega)

/-- **Proposition 5.7 for the triple `(5,3,4)`.** There is a primitive `G` of `f^n/z − c/z` on
`ℂ ∖ {0, ±√2}` such that `c` and `2^{⌊log₂ 4n⌋}·(−i)(G(1+i) − G(1−i))` are 2-integral. -/
theorem twoAdic_primitive (n : ℕ) (hn : 1 ≤ n) :
    ∃ (G : ℂ → ℂ) (c : ℂ),
      (∀ z : ℂ, z ≠ 0 → z ≠ s2 → z ≠ -s2 → HasDerivAt G (f534 z ^ n / z - c / z) z) ∧
      PInt 2 c ∧
      PInt 2 ((2 : ℂ) ^ (Nat.log 2 (4 * n)) *
        (-Complex.I * (G (1 + Complex.I) - G (1 - Complex.I)))) := by
  obtain ⟨U, V, ⟨F, hF, hFU⟩, hU, hV⟩ := primV_kw n hn
  have he := eps_ne_zero
  have hs := s2_ne_zero
  refine ⟨fun z => (128 * eps)⁻¹ ^ n * (2 * Complex.I * eps) * F (wOf z),
    (128 * eps)⁻¹ ^ n * V, ?_, ?_, ?_⟩
  · intro z hz0 hz1 hz2
    have hq : s2 - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz1)
    have hp : s2 + z ≠ 0 := by
      intro h
      apply hz2
      linear_combination h
    have hw0 : wOf z ≠ 0 := by
      unfold wOf
      exact div_ne_zero (mul_ne_zero (mul_ne_zero Complex.I_ne_zero he) hp) hq
    have hD : wOf z ^ 2 + eps ^ 2 ≠ 0 := by
      rw [wOf_sq_add hz1]
      exact div_ne_zero (neg_ne_zero.2 (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (by norm_num) hs) (pow_ne_zero _ he)) hz0)) (pow_ne_zero _ hq)
    have hcomp := (hF (wOf z) hw0 hD).comp z (hasDerivAt_wOf hz1)
    have hG := hcomp.const_mul ((128 * eps)⁻¹ ^ n * (2 * Complex.I * eps))
    refine hG.congr_deriv ?_
    have hA : 2 * Complex.I * eps * (Complex.I * eps * (2 * s2) / (s2 - z) ^ 2)
        = (wOf z ^ 2 + eps ^ 2) / z := by
      rw [wOf_sq_add hz1]
      field_simp
      linear_combination 4 * Complex.I_sq
    have hX : ((1 + eps ^ 2 * wOf z ^ 2) ^ 5 * (1 - wOf z ^ 2) ^ 3 *
        (wOf z ^ 4)⁻¹ * ((wOf z ^ 2 + eps ^ 2) ^ 4)⁻¹) ^ n
        = kw n (wOf z) * (wOf z ^ 2 + eps ^ 2) := by
      unfold kw
      rw [mul_pow, mul_pow, mul_pow, inv_pow, inv_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul,
        pow_succ (wOf z ^ 2 + eps ^ 2) (4 * n)]
      field_simp
      ring
    have hfn : f534 z ^ n = (128 * eps)⁻¹ ^ n * (kw n (wOf z) * (wOf z ^ 2 + eps ^ 2)) := by
      rw [f534_eq_wOf hz0 hz1 hz2, mul_pow, hX]
    calc (128 * eps)⁻¹ ^ n * (2 * Complex.I * eps) *
          ((kw n (wOf z) - V / (wOf z ^ 2 + eps ^ 2)) *
            (Complex.I * eps * (2 * s2) / (s2 - z) ^ 2))
        = (128 * eps)⁻¹ ^ n * ((kw n (wOf z) - V / (wOf z ^ 2 + eps ^ 2)) *
            (2 * Complex.I * eps * (Complex.I * eps * (2 * s2) / (s2 - z) ^ 2))) := by ring
      _ = (128 * eps)⁻¹ ^ n * ((kw n (wOf z) - V / (wOf z ^ 2 + eps ^ 2)) *
            ((wOf z ^ 2 + eps ^ 2) / z)) := by rw [hA]
      _ = f534 z ^ n / z - (128 * eps)⁻¹ ^ n * V / z := by
          rw [hfn]
          field_simp
  · have := (V2_128 n).mul hV
    exact V2.to_PInt (this.mono (by omega))
  · have hval : -Complex.I * ((128 * eps)⁻¹ ^ n * (2 * Complex.I * eps) * F (wOf (1 + Complex.I))
        - (128 * eps)⁻¹ ^ n * (2 * Complex.I * eps) * F (wOf (1 - Complex.I)))
        = 2 * (eps * ((128 * eps)⁻¹ ^ n * (-U))) := by
      rw [wOf_one_add_I, wOf_one_sub_I, ← hFU]
      linear_combination
        (-2 * eps * (128 * eps)⁻¹ ^ n * (F (-1) - F 1)) * Complex.I_sq
    show PInt 2 ((2 : ℂ) ^ (Nat.log 2 (4 * n)) *
      (-Complex.I * ((128 * eps)⁻¹ ^ n * (2 * Complex.I * eps) * F (wOf (1 + Complex.I))
        - (128 * eps)⁻¹ ^ n * (2 * Complex.I * eps) * F (wOf (1 - Complex.I)))))
    rw [hval]
    have h := V2.two.mul ((V2.of_PInt V2.eps_PInt).mul ((V2_128 n).mul hU.neg))
    exact V2.PInt_two_pow_mul (h.mono (by omega))

end PiMeasure
