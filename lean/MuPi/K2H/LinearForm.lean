import MuPi.K2H.PInt

/-!
# K2H, triple `(5,3,4)`: `J_n` as a linear form in `1` and `π`

A *primitive pair* `(G, c)` for `f^n/z` is a function `G` holomorphic on `ℂ ∖ {0, ±√2}` with
`G' = f^n/z − c/z` there.  We prove:

* `primPair_unique` : the constant `c` and the endpoint difference `G(1+i) − G(1−i)` do not depend
  on the choice of the pair (the circle `|z| = 1/2` forces `c₁ = c₂`; the strip
  `1/2 < Re z < 5/4` gives `G₁ − G₂` constant);
* `segment_integral_of_primPair` : the fundamental theorem of calculus along a segment in the right
  half-plane avoiding `√2`, with primitive `G + c·log`;
* `J534_eq_of_primPair` : `J_n = −i (G(1+i) − G(1−i)) + c·π/2`.
-/

namespace PiMeasure

open Complex

/-! ### Elementary facts about `√2` -/

private lemma s2_re : s2.re = Real.sqrt 2 := by simp [s2]

private lemma norm_s2 : ‖s2‖ = Real.sqrt 2 := by
  simp [s2, Real.sqrt_nonneg]

private lemma five_fourths_lt_sqrt_two : (5 / 4 : ℝ) < Real.sqrt 2 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

/-- a point of the open right half-plane is not `0` -/
private lemma ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  rintro rfl
  simp at hz

/-- a point of the open right half-plane is not `−√2` -/
private lemma ne_neg_s2_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ -s2 := by
  rintro rfl
  rw [neg_re, s2_re] at hz
  linarith [Real.sqrt_nonneg 2]

/-- on the right half-plane minus `√2`, `z² − 2 ≠ 0` -/
private lemma sq_sub_two_ne_zero {z : ℂ} (hz : 0 < z.re) (hz2 : z ≠ s2) : z ^ 2 - 2 ≠ 0 := by
  have hfac : z ^ 2 - 2 = (z - s2) * (z - -s2) := by linear_combination s2_sq
  rw [hfac]
  exact mul_ne_zero (sub_ne_zero.mpr hz2) (sub_ne_zero.mpr (ne_neg_s2_of_re_pos hz))

/-! ### Primitive pairs -/

/-- `(G, c)` is a primitive pair for `f^n/z`: `G' = f^n/z − c/z` on `ℂ ∖ {0, ±√2}`. -/
def IsPrimPair (n : ℕ) (G : ℂ → ℂ) (c : ℂ) : Prop :=
  ∀ z : ℂ, z ≠ 0 → z ≠ s2 → z ≠ -s2 → HasDerivAt G (f534 z ^ n / z - c / z) z

/-- two primitive pairs have the same `c` and the same endpoint difference -/
theorem primPair_unique {n : ℕ} {G₁ G₂ : ℂ → ℂ} {c₁ c₂ : ℂ}
    (h₁ : IsPrimPair n G₁ c₁) (h₂ : IsPrimPair n G₂ c₂) :
    c₁ = c₂ ∧ G₁ (1 + I) - G₁ (1 - I) = G₂ (1 + I) - G₂ (1 - I) := by
  set D : ℂ → ℂ := fun z => G₁ z - G₂ z with hD
  have hDderiv : ∀ z : ℂ, z ≠ 0 → z ≠ s2 → z ≠ -s2 →
      HasDerivAt D ((c₂ - c₁) * (z - 0)⁻¹) z := by
    intro z h0 hp hm
    have := (h₁ z h0 hp hm).sub (h₂ z h0 hp hm)
    convert this using 1
    rw [sub_zero]
    field_simp
    ring
  -- (a) the circle `|z| = 1/2` forces `c₁ = c₂`
  have hc : c₁ = c₂ := by
    have hcirc : (∮ z in C(0, 1 / 2), (c₂ - c₁) * (z - 0)⁻¹) = 0 := by
      refine circleIntegral.integral_eq_zero_of_hasDerivWithinAt (f := D) (by norm_num) ?_
      intro z hz
      have hz' : ‖z‖ = 1 / 2 := by simpa using hz
      have hs : (1 / 2 : ℝ) < Real.sqrt 2 := by linarith [five_fourths_lt_sqrt_two]
      refine (hDderiv z ?_ ?_ ?_).hasDerivWithinAt
      · rintro rfl
        norm_num at hz'
      · rintro rfl
        rw [norm_s2] at hz'
        linarith
      · rintro rfl
        rw [norm_neg, norm_s2] at hz'
        linarith
    rw [circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_center_inv _ (by norm_num)] at hcirc
    have hne : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have := (mul_eq_zero.mp hcirc).resolve_right hne
    linear_combination -this
  subst hc
  refine ⟨rfl, ?_⟩
  -- (b) on the strip `1/2 < Re z < 5/4` the difference `G₁ − G₂` is constant
  set S : Set ℂ := {z : ℂ | 1 / 2 < z.re ∧ z.re < 5 / 4}
  have hSopen : IsOpen S :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hSconv : Convex ℝ S := (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)
  have hDS : ∀ z ∈ S, HasDerivAt D 0 z := by
    intro z hz
    have hre : 0 < z.re := by linarith [hz.1]
    have hp : z ≠ s2 := by
      rintro rfl
      have := hz.2
      rw [s2_re] at this
      linarith [five_fourths_lt_sqrt_two]
    have := hDderiv z (ne_zero_of_re_pos hre) hp (ne_neg_s2_of_re_pos hre)
    simpa using this
  have hmem₁ : (1 + I : ℂ) ∈ S := by
    constructor <;> norm_num
  have hmem₂ : (1 - I : ℂ) ∈ S := by
    constructor <;> norm_num
  have hconst : D (1 + I) = D (1 - I) :=
    hSopen.is_const_of_deriv_eq_zero hSconv.isPreconnected
      (fun z hz => (hDS z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hDS z hz).deriv) hmem₁ hmem₂
  simp only [hD] at hconst
  linear_combination hconst

/-- `G + c·log` is a primitive of `f^n/z` on the right half-plane minus `√2` -/
lemma IsPrimPair.hasDerivAt_primitive {n : ℕ} {G : ℂ → ℂ} {c : ℂ} (h : IsPrimPair n G c) {z : ℂ}
    (hre : 0 < z.re) (hz : z ≠ s2) :
    HasDerivAt (fun w => G w + c * Complex.log w) (f534 z ^ n / z) z := by
  have hG := h z (ne_zero_of_re_pos hre) hz (ne_neg_s2_of_re_pos hre)
  have hL : HasDerivAt Complex.log z⁻¹ z :=
    Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl hre))
  have := hG.add (hL.const_mul c)
  convert this using 1
  ring

/-- `f^n/z` is continuous at every point with `z ≠ 0`, `z² ≠ 2` -/
private lemma continuousAt_integrand (n : ℕ) {z : ℂ} (hz : z ≠ 0) (hz2 : z ^ 2 - 2 ≠ 0) :
    ContinuousAt (fun w : ℂ => f534 w ^ n / w) z := by
  unfold f534
  refine ContinuousAt.div ?_ continuousAt_id hz
  refine ContinuousAt.pow ?_ n
  refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
  exact mul_ne_zero (pow_ne_zero _ hz) (pow_ne_zero _ hz2)

/-- FTC along the affine path `t ↦ p + t q`, `t ∈ [t₀, t₁]` -/
lemma IsPrimPair.path_integral {n : ℕ} {G : ℂ → ℂ} {c : ℂ} (h : IsPrimPair n G c)
    (p q : ℂ) (t₀ t₁ : ℝ)
    (hseg : ∀ t ∈ Set.uIcc t₀ t₁, 0 < (p + t * q).re ∧ p + t * q ≠ s2) :
    ∫ t in t₀..t₁, f534 (p + t * q) ^ n / (p + t * q) * q
      = (G (p + t₁ * q) + c * Complex.log (p + t₁ * q))
        - (G (p + t₀ * q) + c * Complex.log (p + t₀ * q)) := by
  have hderiv : ∀ t ∈ Set.uIcc t₀ t₁,
      HasDerivAt (fun s : ℝ => G (p + s * q) + c * Complex.log (p + s * q))
        (f534 (p + t * q) ^ n / (p + t * q) * q) t := by
    intro t ht
    obtain ⟨hre, hne⟩ := hseg t ht
    have hF := h.hasDerivAt_primitive hre hne
    have hγ : HasDerivAt (fun w : ℂ => p + w * q) q (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const q).const_add p
    exact (hF.comp_of_eq (t : ℂ) hγ rfl).comp_ofReal
  have hint : IntervalIntegrable (fun t : ℝ => f534 (p + t * q) ^ n / (p + t * q) * q)
      MeasureTheory.volume t₀ t₁ := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    apply ContinuousAt.continuousWithinAt
    obtain ⟨hre, hne⟩ := hseg t ht
    have hc := continuousAt_integrand n (ne_zero_of_re_pos hre) (sq_sub_two_ne_zero hre hne)
    have hγ : ContinuousAt (fun s : ℝ => p + (s : ℂ) * q) t := by fun_prop
    exact (hc.comp_of_eq hγ rfl).mul continuousAt_const
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- fundamental theorem of calculus along a segment in the right half-plane that avoids `√2` -/
theorem segment_integral_of_primPair {n : ℕ} {G : ℂ → ℂ} {c : ℂ} (h : IsPrimPair n G c) (a b : ℂ)
    (hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 < (a + t * (b - a)).re ∧ a + t * (b - a) ≠ s2) :
    ∫ t in (0 : ℝ)..1, f534 (a + t * (b - a)) ^ n / (a + t * (b - a)) * (b - a)
      = (G b + c * Complex.log b) - (G a + c * Complex.log a) := by
  have hseg' : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      0 < (a + t * (b - a)).re ∧ a + t * (b - a) ≠ s2 := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact hseg t ht.1 ht.2
  rw [h.path_integral a (b - a) 0 1 hseg']
  have e1 : a + ((1 : ℝ) : ℂ) * (b - a) = b := by push_cast; ring
  have e0 : a + ((0 : ℝ) : ℂ) * (b - a) = a := by push_cast; ring
  rw [e1, e0]

/-! ### The constant `log(1+i) − log(1−i) = iπ/2` -/

private lemma arg_one_add_I : Complex.arg (1 + I) = Real.pi / 4 := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := s2_sq
  have h : (1 + I : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) *
      (Complex.cos ((Real.pi / 4 : ℝ) : ℂ) + Complex.sin ((Real.pi / 4 : ℝ) : ℂ) * I) := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast
    linear_combination (-(1 + I) / 2) * hs
  rw [h, Complex.arg_mul_cos_add_sin_mul_I (by positivity)]
  constructor <;> linarith [Real.pi_pos]

private lemma arg_one_sub_I : Complex.arg (1 - I) = -(Real.pi / 4) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := s2_sq
  have h : (1 - I : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) *
      (Complex.cos ((-(Real.pi / 4) : ℝ) : ℂ) + Complex.sin ((-(Real.pi / 4) : ℝ) : ℂ) * I) := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast
    linear_combination (-(1 - I) / 2) * hs
  rw [h, Complex.arg_mul_cos_add_sin_mul_I (by positivity)]
  constructor <;> linarith [Real.pi_pos]

lemma log_one_add_I_sub_log_one_sub_I :
    Complex.log (1 + I) - Complex.log (1 - I) = I * ((Real.pi : ℂ) / 2) := by
  have hn : ‖(1 + I : ℂ)‖ = ‖(1 - I : ℂ)‖ := by
    have : (1 - I : ℂ) = (starRingEnd ℂ) (1 + I) := by
      rw [map_add, map_one, Complex.conj_I, sub_eq_add_neg]
    rw [this, Complex.norm_conj]
  rw [Complex.log, Complex.log, hn, arg_one_add_I, arg_one_sub_I]
  push_cast
  ring

/-- the linear form: `J_n = −i (G(1+i) − G(1−i)) + c·π/2` -/
theorem J534_eq_of_primPair {n : ℕ} {G : ℂ → ℂ} {c : ℂ} (h : IsPrimPair n G c) :
    J534 n = -I * (G (1 + I) - G (1 - I)) + c * (Real.pi / 2) := by
  have hseg : ∀ t ∈ Set.uIcc (-1 : ℝ) 1, 0 < ((1 : ℂ) + t * I).re ∧ (1 : ℂ) + t * I ≠ s2 := by
    intro t _
    refine ⟨by simp, ?_⟩
    intro heq
    have hre := congrArg Complex.re heq
    simp only [add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, s2_re] at hre
    linarith [five_fourths_lt_sqrt_two]
  have hI := h.path_integral 1 I (-1) 1 hseg
  unfold J534
  rw [hI]
  have e1 : (1 : ℂ) + ((1 : ℝ) : ℂ) * I = 1 + I := by push_cast; ring
  have e2 : (1 : ℂ) + ((-1 : ℝ) : ℂ) * I = 1 - I := by push_cast; ring
  rw [e1, e2]
  have hlog := log_one_add_I_sub_log_one_sub_I
  linear_combination (-I * c) * hlog - (c * (Real.pi : ℂ) / 2) * Complex.I_sq

end PiMeasure

#print axioms PiMeasure.primPair_unique
#print axioms PiMeasure.segment_integral_of_primPair
#print axioms PiMeasure.J534_eq_of_primPair
