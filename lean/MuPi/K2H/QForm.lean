import MuPi.K2H.PInt

/-!
# K2H, triple `(5,3,4)`: the primitive of `f(z)^n dz/z` in the variables `W`, `Y`

With `W = z + 2/z`, `Y = z - 2/z` (so `W² - Y² = 8`, `z·dW/dz = Y`, `z·dY/dz = W`) every function
`P(W) Y^{-2m} / z` (`P` a polynomial) is `c/z + G'`, where `G` is a combination of the functions
`z^l` (`l ≠ 0`) and `W^j Y^{-(2m'+1)}`.  The only denominators that occur are the integers `l` with
`1 ≤ l ≤ deg P`, the number `2`, and the odd numbers `2k - 1` with `1 ≤ k ≤ m`.

* `exists_primitive_WY` : the statement over an arbitrary subring `R ⊆ ℂ` and an arbitrary class of
  admissible primitives (`PrimClass R`);
* `f534_eq_WY` : `f534 z = (W-3)^5 (W-2)^3 / Y^4`;
* `exists_rational_primPair` : for `f534 ^ n`, with `R = ℚ` and the class of the functions `G` with
  `G (1+i) - G (1-i) ∈ i·ℚ`.
-/

namespace PiMeasure

open Complex Polynomial

/-- `W = z + 2/z` -/
noncomputable def Wf (z : ℂ) : ℂ := z + 2 / z
/-- `Y = z − 2/z` -/
noncomputable def Yf (z : ℂ) : ℂ := z - 2 / z

/-- A class of admissible primitives over a subring `R` of `ℂ`. -/
structure PrimClass (R : Subring ℂ) where
  mem : (ℂ → ℂ) → Prop
  mem_zero : mem (fun _ => 0)
  mem_add : ∀ {F G : ℂ → ℂ}, mem F → mem G → mem (fun z => F z + G z)
  mem_smul : ∀ {r : ℂ} {F : ℂ → ℂ}, r ∈ R → mem F → mem (fun z => r * F z)
  mem_zpow : ∀ l : ℤ, l ≠ 0 → mem (fun z => z ^ l)
  mem_WY : ∀ j m : ℕ, mem (fun z => Wf z ^ j * (Yf z ^ (2 * m + 1))⁻¹)

/-! ## Elementary facts on `W` and `Y` -/

/-- `W² = Y² + 8` -/
lemma Wf_sq {z : ℂ} (hz0 : z ≠ 0) : Wf z ^ 2 = Yf z ^ 2 + 8 := by
  unfold Wf Yf
  field_simp
  ring

/-- on the domain `z ≠ 0, ±√2` the function `Y` does not vanish -/
lemma Yf_ne_zero {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ s2) (hz2 : z ≠ -s2) : Yf z ≠ 0 := by
  have h : Yf z = (z - s2) * (z + s2) / z := by
    unfold Yf
    field_simp
    linear_combination s2_sq
  rw [h]
  refine div_ne_zero (mul_ne_zero (sub_ne_zero.2 hz1) ?_) hz0
  intro h'
  exact hz2 (eq_neg_of_add_eq_zero_left h')

/-- `z · dW/dz = Y` -/
lemma hasDerivAt_Wf {z : ℂ} (hz0 : z ≠ 0) : HasDerivAt Wf (Yf z / z) z := by
  have h := (hasDerivAt_id' z).fun_add ((hasDerivAt_const z (2 : ℂ)).fun_div (hasDerivAt_id' z) hz0)
  refine HasDerivAt.congr_deriv (f := Wf) h ?_
  unfold Yf
  field_simp
  ring

/-- `z · dY/dz = W` -/
lemma hasDerivAt_Yf {z : ℂ} (hz0 : z ≠ 0) : HasDerivAt Yf (Wf z / z) z := by
  have h := (hasDerivAt_id' z).fun_sub ((hasDerivAt_const z (2 : ℂ)).fun_div (hasDerivAt_id' z) hz0)
  refine HasDerivAt.congr_deriv (f := Yf) h ?_
  unfold Wf
  field_simp
  ring

/-- the pure algebra behind `hasDerivAt_WY` -/
private lemma WY_deriv_algebra (j m : ℕ) {W Y z : ℂ} (hz0 : z ≠ 0) (hY : Y ≠ 0)
    (hWY : W ^ 2 = Y ^ 2 + 8) :
    ((j + 1 : ℕ) : ℂ) * W ^ j * (Y / z) * (Y ^ (2 * m + 1))⁻¹
        + W ^ (j + 1) * (-(((2 * m + 1 : ℕ) : ℂ) * Y ^ (2 * m) * (W / z)) / (Y ^ (2 * m + 1)) ^ 2)
      = ((j : ℂ) - 2 * m) * (W ^ j * (Y ^ (2 * m))⁻¹ / z)
        - 8 * (2 * (m : ℂ) + 1) * (W ^ j * (Y ^ (2 * (m + 1)))⁻¹ / z) := by
  have key : ((j + 1 : ℕ) : ℂ) * W ^ j * (Y / z) * (Y ^ (2 * m + 1))⁻¹
        + W ^ (j + 1) * (-(((2 * m + 1 : ℕ) : ℂ) * Y ^ (2 * m) * (W / z)) / (Y ^ (2 * m + 1)) ^ 2)
      = ((j : ℂ) - 2 * m) * (W ^ j * (Y ^ (2 * m))⁻¹ / z)
        - 8 * (2 * (m : ℂ) + 1) * (W ^ j * (Y ^ (2 * (m + 1)))⁻¹ / z)
        + (2 * (m : ℂ) + 1) * W ^ j * (Y ^ (2 * (m + 1)))⁻¹ / z * (Y ^ 2 + 8 - W ^ 2) := by
    push_cast
    field_simp
    ring
  rw [key, hWY]
  ring

/-- `d/dz (W^{j+1} Y^{-(2m+1)}) = (j - 2m) W^j Y^{-2m}/z - 8 (2m+1) W^j Y^{-2(m+1)}/z` -/
lemma hasDerivAt_WY (j m : ℕ) {z : ℂ} (hz0 : z ≠ 0) (hY : Yf z ≠ 0) :
    HasDerivAt (fun z => Wf z ^ (j + 1) * (Yf z ^ (2 * m + 1))⁻¹)
      (((j : ℂ) - 2 * m) * (Wf z ^ j * (Yf z ^ (2 * m))⁻¹ / z)
        - 8 * (2 * (m : ℂ) + 1) * (Wf z ^ j * (Yf z ^ (2 * (m + 1)))⁻¹ / z)) z := by
  have h1 := (hasDerivAt_Wf hz0).fun_pow (j + 1)
  have h2 := ((hasDerivAt_Yf hz0).fun_pow (2 * m + 1)).fun_inv (pow_ne_zero _ hY)
  have h3 := h1.fun_mul h2
  refine h3.congr_deriv ?_
  simp only [Nat.add_sub_cancel]
  exact WY_deriv_algebra j m hz0 hY (Wf_sq hz0)

/-! ## Functions with a primitive in the class, up to a multiple of `1/z` -/

/-- `g = c/z + G'` on the domain `z ≠ 0, ±√2`, with `c ∈ R` and `G` in the class `𝒢`. -/
def HasPrim (R : Subring ℂ) (𝒢 : PrimClass R) (g : ℂ → ℂ) : Prop :=
  ∃ (c : ℂ) (G : ℂ → ℂ), c ∈ R ∧ 𝒢.mem G ∧
    ∀ z : ℂ, z ≠ 0 → z ≠ s2 → z ≠ -s2 → HasDerivAt G (g z - c / z) z

namespace HasPrim

variable {R : Subring ℂ} {𝒢 : PrimClass R}

lemma zero : HasPrim R 𝒢 (fun _ => 0) :=
  ⟨0, fun _ => 0, R.zero_mem, 𝒢.mem_zero, fun z _ _ _ => by
    simpa using hasDerivAt_const z (0 : ℂ)⟩

lemma add {g₁ g₂ : ℂ → ℂ} (h₁ : HasPrim R 𝒢 g₁) (h₂ : HasPrim R 𝒢 g₂) :
    HasPrim R 𝒢 (fun z => g₁ z + g₂ z) := by
  obtain ⟨c₁, G₁, hc₁, hG₁, hd₁⟩ := h₁
  obtain ⟨c₂, G₂, hc₂, hG₂, hd₂⟩ := h₂
  refine ⟨c₁ + c₂, fun z => G₁ z + G₂ z, R.add_mem hc₁ hc₂, 𝒢.mem_add hG₁ hG₂,
    fun z hz0 hz1 hz2 => ?_⟩
  refine ((hd₁ z hz0 hz1 hz2).fun_add (hd₂ z hz0 hz1 hz2)).congr_deriv ?_
  ring

lemma smul {r : ℂ} {g : ℂ → ℂ} (hr : r ∈ R) (h : HasPrim R 𝒢 g) :
    HasPrim R 𝒢 (fun z => r * g z) := by
  obtain ⟨c, G, hc, hG, hd⟩ := h
  refine ⟨r * c, fun z => r * G z, R.mul_mem hr hc, 𝒢.mem_smul hr hG, fun z hz0 hz1 hz2 => ?_⟩
  refine ((hd z hz0 hz1 hz2).const_mul r).congr_deriv ?_
  ring

lemma congr {g₁ g₂ : ℂ → ℂ} (h : HasPrim R 𝒢 g₁)
    (he : ∀ z : ℂ, z ≠ 0 → z ≠ s2 → z ≠ -s2 → g₁ z = g₂ z) : HasPrim R 𝒢 g₂ := by
  obtain ⟨c, G, hc, hG, hd⟩ := h
  exact ⟨c, G, hc, hG, fun z hz0 hz1 hz2 => by
    rw [← he z hz0 hz1 hz2]; exact hd z hz0 hz1 hz2⟩

lemma sum {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℂ) (h : ∀ i ∈ s, HasPrim R 𝒢 (g i)) :
    HasPrim R 𝒢 (fun z => ∑ i ∈ s, g i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : HasPrim R 𝒢 _)
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine (add h1 h2).congr (fun z _ _ _ => ?_)
    rw [Finset.sum_insert ha]

/-- `1/z` itself: `c = 1`, `G = 0` -/
lemma inv : HasPrim R 𝒢 (fun z => z⁻¹) :=
  ⟨1, fun _ => 0, R.one_mem, 𝒢.mem_zero, fun z _ _ _ => by
    have h : z⁻¹ - 1 / z = 0 := by rw [one_div]; ring
    rw [h]
    exact hasDerivAt_const z (0 : ℂ)⟩

/-- `z^{l-1}`, `l ≠ 0`: `c = 0`, `G = z^l / l` -/
lemma zpow {l : ℤ} (hl0 : l ≠ 0) (hl : ((l : ℂ))⁻¹ ∈ R) :
    HasPrim R 𝒢 (fun z => z ^ (l - 1)) := by
  refine ⟨0, fun z => (l : ℂ)⁻¹ * z ^ l, R.zero_mem, 𝒢.mem_smul hl (𝒢.mem_zpow l hl0),
    fun z hz0 _ _ => ?_⟩
  refine ((hasDerivAt_zpow l z (Or.inl hz0)).const_mul ((l : ℂ)⁻¹)).congr_deriv ?_
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl0
  field_simp
  ring

/-- the derivative of a member of the class: `c = 0` -/
lemma of_mem {F g : ℂ → ℂ} (hF : 𝒢.mem F)
    (hd : ∀ z : ℂ, z ≠ 0 → z ≠ s2 → z ≠ -s2 → HasDerivAt F (g z) z) : HasPrim R 𝒢 g :=
  ⟨0, F, R.zero_mem, hF, fun z hz0 hz1 hz2 => by simpa using hd z hz0 hz1 hz2⟩

end HasPrim

/-! ## The monomials `W^j Y^{-2m} / z` -/

section monomial

variable {R : Subring ℂ} {𝒢 : PrimClass R}

/-- inverses of the nonzero integers of absolute value `≤ j` -/
private lemma int_inv_mem {j : ℕ} (hl : ∀ l : ℕ, 1 ≤ l → l ≤ j → ((l : ℂ))⁻¹ ∈ R) {l : ℤ}
    (h0 : l ≠ 0) (h1 : -(j : ℤ) ≤ l) (h2 : l ≤ j) : ((l : ℂ))⁻¹ ∈ R := by
  obtain ⟨n, rfl | rfl⟩ := l.eq_nat_or_neg
  · rw [Int.cast_natCast]
    exact hl n (by omega) (by omega)
  · rw [Int.cast_neg, Int.cast_natCast, inv_neg]
    exact R.neg_mem (hl n (by omega) (by omega))

/-- the binomial expansion of `(z + 2/z)^j / z` -/
lemma Wf_pow_div (j : ℕ) {z : ℂ} (hz0 : z ≠ 0) :
    Wf z ^ j / z = ∑ k ∈ Finset.range (j + 1),
      ((j.choose k : ℂ) * 2 ^ (j - k)) * z ^ ((2 * (k : ℤ) - j) - 1) := by
  unfold Wf
  rw [add_pow, Finset.sum_div]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ j := by have := Finset.mem_range.1 hk; omega
  have e : (2 * (k : ℤ) - j) - 1 = (k : ℤ) - ((j - k : ℕ) : ℤ) - 1 := by
    rw [Nat.cast_sub hk']; ring
  rw [e, zpow_sub₀ hz0, zpow_sub₀ hz0, zpow_natCast, zpow_natCast, zpow_one, div_pow]
  field_simp

/-- the case `m = 0`: `W^j / z` -/
lemma hasPrim_W_pow (j : ℕ) (hl : ∀ l : ℕ, 1 ≤ l → l ≤ j → ((l : ℂ))⁻¹ ∈ R) :
    HasPrim R 𝒢 (fun z => Wf z ^ j / z) := by
  have key : HasPrim R 𝒢 (fun z => ∑ k ∈ Finset.range (j + 1),
      ((j.choose k : ℂ) * 2 ^ (j - k)) * z ^ ((2 * (k : ℤ) - j) - 1)) := by
    refine HasPrim.sum _ _ (fun k hk => HasPrim.smul ?_ ?_)
    · exact R.mul_mem (natCast_mem R _) (R.pow_mem (ofNat_mem R 2) _)
    · have hk' : k ≤ j := by have := Finset.mem_range.1 hk; omega
      by_cases h : 2 * (k : ℤ) - j = 0
      · rw [h]
        refine HasPrim.inv.congr (fun z _ _ _ => ?_)
        simp
      · exact HasPrim.zpow h (int_inv_mem hl h (by omega) (by omega))
  exact key.congr (fun z hz0 _ _ => (Wf_pow_div j hz0).symm)

/-- every monomial `W^j Y^{-2m} / z` has a primitive in the class, up to a multiple of `1/z` -/
lemma hasPrim_monomial (h2 : (2 : ℂ)⁻¹ ∈ R) :
    ∀ (m j : ℕ), (∀ l : ℕ, 1 ≤ l → l ≤ j → ((l : ℂ))⁻¹ ∈ R) →
      (∀ k : ℕ, 1 ≤ k → k ≤ m → ((2 * (k : ℂ) - 1))⁻¹ ∈ R) →
      HasPrim R 𝒢 (fun z => Wf z ^ j * (Yf z ^ (2 * m))⁻¹ / z) := by
  intro m
  induction m with
  | zero =>
    intro j hl _
    refine (hasPrim_W_pow j hl).congr (fun z _ _ _ => ?_)
    simp
  | succ m ih =>
    intro j hl hm
    have ih' : HasPrim R 𝒢 (fun z => Wf z ^ j * (Yf z ^ (2 * m))⁻¹ / z) :=
      ih j hl (fun k hk1 hk2 => hm k hk1 (by omega))
    have hk : ((2 * (m : ℂ) + 1))⁻¹ ∈ R := by
      have := hm (m + 1) (by omega) le_rfl
      have e : 2 * ((m + 1 : ℕ) : ℂ) - 1 = 2 * (m : ℂ) + 1 := by push_cast; ring
      rwa [e] at this
    have hne : 2 * (m : ℂ) + 1 ≠ 0 := by
      have : ((2 * m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      simpa using this
    have h8 : ((2 : ℂ)⁻¹) ^ 3 ∈ R := R.pow_mem h2 3
    have hD : HasPrim R 𝒢 (fun z => ((j : ℂ) - 2 * m) * (Wf z ^ j * (Yf z ^ (2 * m))⁻¹ / z)
        - 8 * (2 * (m : ℂ) + 1) * (Wf z ^ j * (Yf z ^ (2 * (m + 1)))⁻¹ / z)) :=
      HasPrim.of_mem (𝒢.mem_WY (j + 1) m)
        (fun z hz0 hz1 hz2 => hasDerivAt_WY j m hz0 (Yf_ne_zero hz0 hz1 hz2))
    have hr1 : -(((2 : ℂ)⁻¹) ^ 3 * (2 * (m : ℂ) + 1)⁻¹) ∈ R := R.neg_mem (R.mul_mem h8 hk)
    have hr2 : ((2 : ℂ)⁻¹) ^ 3 * (2 * (m : ℂ) + 1)⁻¹ * ((j : ℂ) - 2 * m) ∈ R :=
      R.mul_mem (R.mul_mem h8 hk)
        (R.sub_mem (natCast_mem R j) (R.mul_mem (ofNat_mem R 2) (natCast_mem R m)))
    refine ((HasPrim.smul hr1 hD).add (HasPrim.smul hr2 ih')).congr (fun z _ _ _ => ?_)
    field_simp
    ring

end monomial

/-- `P(W) Y^{-2m} / z = c/z + G'` with `c ∈ R` and `G` in the class, provided the listed numbers are
invertible in `R`. -/
theorem exists_primitive_WY (R : Subring ℂ) (𝒢 : PrimClass R) (P : ℂ[X]) (hP : ∀ j, P.coeff j ∈ R)
    (m : ℕ)
    (h2 : (2 : ℂ)⁻¹ ∈ R)
    (hl : ∀ l : ℕ, 1 ≤ l → l ≤ P.natDegree → ((l : ℂ))⁻¹ ∈ R)
    (hm : ∀ k : ℕ, 1 ≤ k → k ≤ m → ((2 * (k : ℂ) - 1))⁻¹ ∈ R) :
    ∃ (c : ℂ) (G : ℂ → ℂ), c ∈ R ∧ 𝒢.mem G ∧
      ∀ z : ℂ, z ≠ 0 → z ≠ s2 → z ≠ -s2 →
        HasDerivAt G (P.eval (Wf z) * (Yf z ^ (2 * m))⁻¹ / z - c / z) z := by
  have key : HasPrim R 𝒢 (fun z => ∑ j ∈ Finset.range (P.natDegree + 1),
      P.coeff j * (Wf z ^ j * (Yf z ^ (2 * m))⁻¹ / z)) := by
    refine HasPrim.sum _ _ (fun j hj => HasPrim.smul (hP j) ?_)
    have hj' : j ≤ P.natDegree := by have := Finset.mem_range.1 hj; omega
    exact hasPrim_monomial h2 m j (fun l h1 h2 => hl l h1 (h2.trans hj')) hm
  have key' : HasPrim R 𝒢 (fun z => P.eval (Wf z) * (Yf z ^ (2 * m))⁻¹ / z) := by
    refine key.congr (fun z _ _ _ => ?_)
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  exact key'

/-- on the domain, `f534 z = (W−3)^5 (W−2)^3 / Y^4` -/
theorem f534_eq_WY {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ s2) (hz2 : z ≠ -s2) :
    f534 z = (Wf z - 3) ^ 5 * (Wf z - 2) ^ 3 * (Yf z ^ 4)⁻¹ := by
  have hY := Yf_ne_zero hz0 hz1 hz2
  have hz : z ^ 2 - 2 ≠ 0 := by
    intro h
    apply hY
    unfold Yf
    field_simp
    linear_combination h
  unfold f534
  unfold Yf at hY ⊢
  unfold Wf
  field_simp
  ring

/-! ## The rational case: `R = ℚ`, values at `1 ± i` -/

/-- pairs `(x, y) = (a + b i, a - b i)` with `a`, `b` rational -/
def ConjPair (x y : ℂ) : Prop := ∃ a b : ℚ, x = a + b * I ∧ y = a - b * I

namespace ConjPair

lemma one : ConjPair 1 1 := ⟨1, 0, by simp, by simp⟩

lemma mul {x y x' y' : ℂ} (h : ConjPair x y) (h' : ConjPair x' y') :
    ConjPair (x * x') (y * y') := by
  obtain ⟨a, b, rfl, rfl⟩ := h
  obtain ⟨a', b', rfl, rfl⟩ := h'
  refine ⟨a * a' - b * b', a * b' + a' * b, ?_, ?_⟩
  · push_cast
    linear_combination ((b : ℂ) * b') * I_sq
  · push_cast
    linear_combination ((b : ℂ) * b') * I_sq

lemma pow {x y : ℂ} (h : ConjPair x y) (n : ℕ) : ConjPair (x ^ n) (y ^ n) := by
  induction n with
  | zero => simpa using one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

lemma base : ConjPair (1 + I) (1 - I) := ⟨1, 1, by simp, by simp⟩

lemma base_inv : ConjPair (1 + I)⁻¹ (1 - I)⁻¹ := by
  refine ⟨1 / 2, -1 / 2, ?_, ?_⟩
  · refine inv_eq_of_mul_eq_one_right ?_
    push_cast
    linear_combination (-1 / 2 : ℂ) * I_sq
  · refine inv_eq_of_mul_eq_one_right ?_
    push_cast
    linear_combination (-1 / 2 : ℂ) * I_sq

lemma zpow (l : ℤ) : ConjPair ((1 + I) ^ l) ((1 - I) ^ l) := by
  obtain ⟨n, rfl | rfl⟩ := l.eq_nat_or_neg
  · rw [zpow_natCast, zpow_natCast]
    exact base.pow n
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow, ← inv_pow]
    exact base_inv.pow n

end ConjPair

private lemma two_div_one_add_I : (2 : ℂ) / (1 + I) = 1 - I := by
  have h : (1 + I : ℂ) ≠ 0 := by
    intro h
    have h2 : (1 + I) * (1 - I) = 2 := by linear_combination -I_sq
    rw [h, zero_mul] at h2
    norm_num at h2
  rw [div_eq_iff h]
  linear_combination I_sq

private lemma two_div_one_sub_I : (2 : ℂ) / (1 - I) = 1 + I := by
  have h : (1 - I : ℂ) ≠ 0 := by
    intro h
    have h2 : (1 - I) * (1 + I) = 2 := by linear_combination -I_sq
    rw [h, zero_mul] at h2
    norm_num at h2
  rw [div_eq_iff h]
  linear_combination I_sq

lemma Wf_one_add_I : Wf (1 + I) = 2 := by
  unfold Wf; rw [two_div_one_add_I]; ring

lemma Wf_one_sub_I : Wf (1 - I) = 2 := by
  unfold Wf; rw [two_div_one_sub_I]; ring

lemma Yf_one_add_I : Yf (1 + I) = 2 * I := by
  unfold Yf; rw [two_div_one_add_I]; ring

lemma Yf_one_sub_I : Yf (1 - I) = -(2 * I) := by
  unfold Yf; rw [two_div_one_sub_I]; ring

/-- the class of the functions `G` with `G (1+i) - G (1-i) ∈ i·ℚ` -/
noncomputable def ratPrimClass : PrimClass (algebraMap ℚ ℂ).range where
  mem G := ∃ u : ℚ, G (1 + I) - G (1 - I) = I * (u : ℂ)
  mem_zero := ⟨0, by simp⟩
  mem_add := by
    rintro F G ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨u + v, by push_cast; linear_combination hu + hv⟩
  mem_smul := by
    rintro r F ⟨q, rfl⟩ ⟨u, hu⟩
    refine ⟨q * u, ?_⟩
    rw [eq_ratCast]
    push_cast
    linear_combination (q : ℂ) * hu
  mem_zpow := by
    intro l _
    obtain ⟨a, b, h1, h2⟩ := ConjPair.zpow l
    refine ⟨2 * b, ?_⟩
    change (1 + I) ^ l - (1 - I) ^ l = I * ((2 * b : ℚ) : ℂ)
    rw [h1, h2]
    push_cast
    ring
  mem_WY := by
    intro j m
    refine ⟨-(2 ^ (j + 1) * (2 ^ (2 * m + 1) * (-1) ^ m)⁻¹), ?_⟩
    have e : (2 * I) ^ (2 * m + 1) = 2 ^ (2 * m + 1) * (-1) ^ m * I := by
      rw [mul_pow, pow_succ I, pow_mul, I_sq]
      ring
    change Wf (1 + I) ^ j * (Yf (1 + I) ^ (2 * m + 1))⁻¹
        - Wf (1 - I) ^ j * (Yf (1 - I) ^ (2 * m + 1))⁻¹ = _
    rw [Wf_one_add_I, Wf_one_sub_I, Yf_one_add_I, Yf_one_sub_I, Odd.neg_pow ⟨m, rfl⟩, inv_neg, e,
      mul_inv _ I, inv_I]
    push_cast
    ring

/-- **Theorem A(i), algebraic part.** A primitive pair with rational data. -/
theorem exists_rational_primPair (n : ℕ) :
    ∃ (c u : ℚ) (G : ℂ → ℂ),
      (∀ z : ℂ, z ≠ 0 → z ≠ s2 → z ≠ -s2 → HasDerivAt G (f534 z ^ n / z - (c : ℂ) / z) z) ∧
      G (1 + I) - G (1 - I) = I * (u : ℂ) := by
  obtain ⟨c, G, ⟨c', rfl⟩, ⟨u, hu⟩, hd⟩ :=
    exists_primitive_WY (algebraMap ℚ ℂ).range ratPrimClass
      ((((X - C 3) ^ 5 * (X - C 2) ^ 3) ^ n : ℚ[X]).map (algebraMap ℚ ℂ))
      (fun j => ⟨_, (Polynomial.coeff_map _ _).symm⟩) (2 * n)
      ⟨2⁻¹, by simp⟩ (fun l _ _ => ⟨(l : ℚ)⁻¹, by simp⟩)
      (fun k _ _ => ⟨(2 * (k : ℚ) - 1)⁻¹, by simp⟩)
  refine ⟨c', u, G, fun z hz0 hz1 hz2 => ?_, hu⟩
  refine (hd z hz0 hz1 hz2).congr_deriv ?_
  have e1 : (Yf z ^ (2 * (2 * n)))⁻¹ = ((Yf z ^ 4)⁻¹) ^ n := by
    rw [← inv_pow, ← inv_pow, ← pow_mul]
    congr 1
    ring
  have e2 : eval (Wf z) ((((X - C 3) ^ 5 * (X - C 2) ^ 3) ^ n : ℚ[X]).map (algebraMap ℚ ℂ))
      = ((Wf z - 3) ^ 5 * (Wf z - 2) ^ 3) ^ n := by
    simp only [Polynomial.eval_map_algebraMap, map_pow, map_mul, map_sub, aeval_X, aeval_C,
      eq_ratCast, Rat.cast_ofNat]
  have e3 : f534 z ^ n = ((Wf z - 3) ^ 5 * (Wf z - 2) ^ 3) ^ n * ((Yf z ^ 4)⁻¹) ^ n := by
    rw [f534_eq_WY hz0 hz1 hz2, mul_pow]
  rw [e1, e2, e3, eq_ratCast (algebraMap ℚ ℂ) c']

end PiMeasure

#print axioms PiMeasure.exists_primitive_WY
#print axioms PiMeasure.exists_rational_primPair
