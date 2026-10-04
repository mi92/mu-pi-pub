import MuPi.K2H.PInt

/-!
# Partial-fraction representations on `ℂ ∖ {0, ±√2}`

A `Rep` is a polynomial part `P` and three principal parts `Q i` (polynomials in `1/(z − pole i)`
without constant term).  We prove: uniqueness of the representation of a function, the action of
`d/dz`, an explicit primitive (up to the residue terms), existence of a representation with
coefficients in a subring `R` for every function `N(z)/∏(z − pole i)^{e i}` with `N ∈ R[z]`
(Mathlib's partial fractions), and closure properties of this class of functions.
-/

namespace PiMeasure

open Polynomial Complex Filter Topology

/-- the three finite poles `0, √2, −√2` -/
noncomputable def pole : Fin 3 → ℂ := ![0, s2, -s2]

lemma pole_zero : pole 0 = 0 := rfl

lemma pole_one : pole 1 = s2 := rfl

lemma pole_two : pole 2 = -s2 := rfl

lemma s2_ne_neg : s2 ≠ -s2 := by
  intro h
  have h2 : (2 : ℂ) * s2 = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h | h
  · norm_num at h
  · exact s2_ne_zero h

lemma pole_ne {i j : Fin 3} (hij : i ≠ j) : pole i ≠ pole j := by
  have h01 : (0 : ℂ) ≠ s2 := fun h => s2_ne_zero h.symm
  have h02 : (0 : ℂ) ≠ -s2 := fun h => s2_ne_zero (neg_eq_zero.1 h.symm)
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | exact h01
    | exact h02
    | exact s2_ne_neg
    | exact h01.symm
    | exact h02.symm
    | exact s2_ne_neg.symm

/-- the domain `ℂ ∖ {0, ±√2}` -/
def Udom : Set ℂ := {z | ∀ i, z ≠ pole i}

lemma mem_Udom {z : ℂ} : z ∈ Udom ↔ z ≠ 0 ∧ z ≠ s2 ∧ z ≠ -s2 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

lemma Udom_eq : Udom = (Set.range pole)ᶜ := by
  ext z
  simp only [Udom, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
  exact ⟨fun h i hi => h i hi.symm, fun h i hi => h i hi.symm⟩

lemma isOpen_Udom : IsOpen Udom := by
  rw [Udom_eq]
  exact (Set.finite_range pole).isClosed.isOpen_compl

lemma Udom_infinite : Udom.Infinite := by
  rw [Udom_eq]
  exact (Set.finite_range pole).infinite_compl

/-- a partial-fraction representation -/
structure Rep where
  /-- polynomial part -/
  P : ℂ[X]
  /-- principal parts, as polynomials in `1/(z − pole i)` -/
  Q : Fin 3 → ℂ[X]

namespace Rep

lemma ext' {r₁ r₂ : Rep} (hP : r₁.P = r₂.P) (hQ : ∀ i, r₁.Q i = r₂.Q i) : r₁ = r₂ := by
  cases r₁
  cases r₂
  simp only [mk.injEq]
  exact ⟨hP, funext hQ⟩

/-- principal parts have no constant term -/
def Proper (r : Rep) : Prop := ∀ i, (r.Q i).coeff 0 = 0

/-- the function represented by `r` -/
noncomputable def eval (r : Rep) (z : ℂ) : ℂ :=
  r.P.eval z + ∑ i, (r.Q i).eval ((z - pole i)⁻¹)

/-- difference of representations -/
noncomputable def sub (r₁ r₂ : Rep) : Rep := ⟨r₁.P - r₂.P, fun i => r₁.Q i - r₂.Q i⟩

/-- scalar multiple -/
noncomputable def smul (c : ℂ) (r : Rep) : Rep := ⟨C c * r.P, fun i => C c * r.Q i⟩

lemma eval_sub (r₁ r₂ : Rep) (z : ℂ) : (r₁.sub r₂).eval z = r₁.eval z - r₂.eval z := by
  simp only [eval, sub, Polynomial.eval_sub, Finset.sum_sub_distrib]
  ring

lemma eval_smul (c : ℂ) (r : Rep) (z : ℂ) : (r.smul c).eval z = c * r.eval z := by
  simp only [eval, smul, Polynomial.eval_mul, Polynomial.eval_C]
  rw [mul_add, Finset.mul_sum]

lemma Proper.sub {r₁ r₂ : Rep} (h₁ : r₁.Proper) (h₂ : r₂.Proper) : (r₁.sub r₂).Proper := by
  intro i
  simp [Rep.sub, h₁ i, h₂ i]

lemma Proper.smul {r : Rep} (h : r.Proper) (c : ℂ) : (r.smul c).Proper := by
  intro i
  simp [Rep.smul, h i]

/-- sum of representations -/
noncomputable def add (r₁ r₂ : Rep) : Rep := ⟨r₁.P + r₂.P, fun i => r₁.Q i + r₂.Q i⟩

lemma eval_add (r₁ r₂ : Rep) (z : ℂ) : (r₁.add r₂).eval z = r₁.eval z + r₂.eval z := by
  simp only [eval, add, Polynomial.eval_add, Finset.sum_add_distrib]
  ring

lemma Proper.add {r₁ r₂ : Rep} (h₁ : r₁.Proper) (h₂ : r₂.Proper) : (r₁.add r₂).Proper := by
  intro i
  simp [Rep.add, h₁ i, h₂ i]

/-- the representation of `Σ c i/(z − pole i)` -/
noncomputable def resRep (c : Fin 3 → ℂ) : Rep := ⟨0, fun i => C (c i) * X⟩

lemma eval_resRep (c : Fin 3 → ℂ) (z : ℂ) : (resRep c).eval z = ∑ i, c i * (z - pole i)⁻¹ := by
  simp [eval, resRep]

lemma resRep_proper (c : Fin 3 → ℂ) : (resRep c).Proper := by
  intro i
  simp [resRep]

/-- derivative of a representation -/
noncomputable def deriv (r : Rep) : Rep :=
  ⟨derivative r.P, fun i => -(X ^ 2 * derivative (r.Q i))⟩

lemma deriv_proper (r : Rep) : r.deriv.Proper := by
  intro i
  simp [deriv, Polynomial.mul_coeff_zero]

lemma hasDerivAt_inv_sub {z : ℂ} (i : Fin 3) (hz : z ∈ Udom) :
    HasDerivAt (fun z : ℂ => (z - pole i)⁻¹) (-1 / (z - pole i) ^ 2) z :=
  ((hasDerivAt_id' z).sub_const (pole i)).inv (sub_ne_zero.2 (hz i))

lemma hasDerivAt_eval (r : Rep) {z : ℂ} (hz : z ∈ Udom) :
    HasDerivAt r.eval (r.deriv.eval z) z := by
  have hP : HasDerivAt (fun z => r.P.eval z) ((derivative r.P).eval z) z := r.P.hasDerivAt z
  have hQ : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      HasDerivAt (fun z => (r.Q i).eval ((z - pole i)⁻¹))
        ((-(X ^ 2 * derivative (r.Q i))).eval ((z - pole i)⁻¹)) z := by
    intro i _
    have hcomp := ((r.Q i).hasDerivAt ((z - pole i)⁻¹)).comp z (hasDerivAt_inv_sub i hz)
    refine hcomp.congr_deriv ?_
    have hne : z - pole i ≠ 0 := sub_ne_zero.2 (hz i)
    simp only [eval_neg, eval_mul, eval_pow, eval_X]
    field_simp
  exact hP.add (HasDerivAt.fun_sum hQ)

/-- **Uniqueness.** A proper representation of the zero function is zero. -/
theorem eq_zero_of_eval_eq_zero (r : Rep) (hr : r.Proper) (h : ∀ z ∈ Udom, r.eval z = 0) :
    r.P = 0 ∧ ∀ i, r.Q i = 0 := by
  have hQ : ∀ i, r.Q i = 0 := by
    intro i
    by_contra hne
    have hdeg : 0 < (r.Q i).degree := by
      by_contra hd
      have h0 := eq_C_of_degree_le_zero (not_lt.1 hd)
      rw [hr i] at h0
      exact hne (by rw [h0]; simp)
    have h0 : Tendsto (fun z : ℂ => z - pole i) (𝓝[≠] (pole i)) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have : Tendsto (fun z : ℂ => z - pole i) (𝓝 (pole i)) (𝓝 (pole i - pole i)) :=
          (continuous_id.sub continuous_const).tendsto _
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact sub_ne_zero.2 hz
    have hT1 : Tendsto (fun z : ℂ => ‖(r.Q i).eval ((z - pole i)⁻¹)‖) (𝓝[≠] (pole i)) atTop :=
      (r.Q i).tendsto_norm_atTop hdeg (tendsto_norm_inv_nhdsNE_zero_atTop.comp h0)
    let g : ℂ → ℂ := fun z =>
      r.P.eval z + ∑ j ∈ Finset.univ.erase i, (r.Q j).eval ((z - pole j)⁻¹)
    have hg : ContinuousAt g (pole i) := by
      refine (r.P.continuous.continuousAt).add (tendsto_finsetSum _ fun j hj => ?_)
      have hji : pole i - pole j ≠ 0 := sub_ne_zero.2 (pole_ne (Finset.ne_of_mem_erase hj).symm)
      exact (r.Q j).continuous.continuousAt.comp
        ((continuousAt_id.sub continuousAt_const).inv₀ hji)
    have hT2 : Tendsto (fun z => ‖g z‖) (𝓝[≠] (pole i)) (𝓝 ‖g (pole i)‖) :=
      (hg.norm.tendsto).mono_left nhdsWithin_le_nhds
    have hU : ∀ᶠ z in 𝓝[≠] (pole i), z ∈ Udom := by
      have hV : ∀ᶠ z in 𝓝 (pole i), ∀ j : Fin 3, j ≠ i → z ≠ pole j := by
        rw [Filter.eventually_all]
        intro j
        by_cases hji : j = i
        · exact Filter.Eventually.of_forall fun z h => absurd hji h
        · have := eventually_ne_nhds (pole_ne (Ne.symm hji))
          exact this.mono fun z hz _ => hz
      filter_upwards [nhdsWithin_le_nhds hV, self_mem_nhdsWithin] with z h1 h2
      intro j
      by_cases hji : j = i
      · rw [hji]
        exact h2
      · exact h1 j hji
    have hev : ∀ᶠ z in 𝓝[≠] (pole i), ‖g z‖ = ‖(r.Q i).eval ((z - pole i)⁻¹)‖ := by
      filter_upwards [hU] with z hz
      have hz0 := h z hz
      have hsplit : r.eval z = (r.Q i).eval ((z - pole i)⁻¹) + g z := by
        simp only [eval, g]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        ring
      rw [hsplit] at hz0
      have : (r.Q i).eval ((z - pole i)⁻¹) = -g z := by linear_combination hz0
      rw [this, norm_neg]
    exact not_tendsto_atTop_of_tendsto_nhds (hT2.congr' hev) hT1
  refine ⟨?_, hQ⟩
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Udom_infinite.mono fun z hz => ?_
  have hz0 := h z hz
  simp only [eval, hQ, Polynomial.eval_zero, Finset.sum_const_zero, add_zero] at hz0
  exact hz0

theorem ext_of_eval {r₁ r₂ : Rep} (h₁ : r₁.Proper) (h₂ : r₂.Proper)
    (h : ∀ z ∈ Udom, r₁.eval z = r₂.eval z) : r₁ = r₂ := by
  have := eq_zero_of_eval_eq_zero (r₁.sub r₂) (h₁.sub h₂)
    (fun z hz => by rw [eval_sub, h z hz, sub_self])
  exact Rep.ext' (sub_eq_zero.1 this.1) (fun i => sub_eq_zero.1 (this.2 i))

/-! ### Coefficients of the derivative -/

lemma deriv_P_coeff (r : Rep) (j : ℕ) : r.deriv.P.coeff j = r.P.coeff (j + 1) * ((j : ℂ) + 1) := by
  simp [deriv, coeff_derivative]

lemma deriv_Q_coeff_succ_succ (r : Rep) (i : Fin 3) (k : ℕ) :
    (r.deriv.Q i).coeff (k + 2) = -((r.Q i).coeff (k + 1) * ((k : ℂ) + 1)) := by
  simp [deriv, coeff_X_pow_mul, coeff_derivative]

lemma deriv_Q_coeff_one (r : Rep) (i : Fin 3) : (r.deriv.Q i).coeff 1 = 0 := by
  simp [deriv, coeff_X_pow_mul']

/-! ### The standard primitive -/

/-- the standard primitive of `r` without its residue terms -/
noncomputable def primFun (r : Rep) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (r.P.natDegree + 1), r.P.coeff j / ((j : ℂ) + 1) * z ^ (j + 1)
  + ∑ i, ∑ k ∈ Finset.range (r.Q i).natDegree,
      -((r.Q i).coeff (k + 2)) / ((k : ℂ) + 1) * ((z - pole i)⁻¹) ^ (k + 1)

lemma hasDerivAt_primFun (r : Rep) (hr : r.Proper) {z : ℂ} (hz : z ∈ Udom) :
    HasDerivAt r.primFun (r.eval z - ∑ i, (r.Q i).coeff 1 * (z - pole i)⁻¹) z := by
  have hP : HasDerivAt (fun z : ℂ => ∑ j ∈ Finset.range (r.P.natDegree + 1),
      r.P.coeff j / ((j : ℂ) + 1) * z ^ (j + 1)) (r.P.eval z) z := by
    have hterm : ∀ j ∈ Finset.range (r.P.natDegree + 1),
        HasDerivAt (fun z : ℂ => r.P.coeff j / ((j : ℂ) + 1) * z ^ (j + 1))
          (r.P.coeff j * z ^ j) z := by
      intro j _
      have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      have := ((hasDerivAt_id' z).pow (j + 1)).const_mul (r.P.coeff j / ((j : ℂ) + 1))
      refine this.congr_deriv ?_
      simp only [Nat.add_sub_cancel]
      push_cast
      field_simp
    have h := HasDerivAt.fun_sum hterm
    rw [eval_eq_sum_range]
    exact h
  have hQ : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      HasDerivAt (fun z : ℂ => ∑ k ∈ Finset.range (r.Q i).natDegree,
        -((r.Q i).coeff (k + 2)) / ((k : ℂ) + 1) * ((z - pole i)⁻¹) ^ (k + 1))
        ((r.Q i).eval ((z - pole i)⁻¹) - (r.Q i).coeff 1 * (z - pole i)⁻¹) z := by
    intro i _
    have hne : z - pole i ≠ 0 := sub_ne_zero.2 (hz i)
    have hterm : ∀ k ∈ Finset.range (r.Q i).natDegree,
        HasDerivAt (fun z : ℂ => -((r.Q i).coeff (k + 2)) / ((k : ℂ) + 1) *
          ((z - pole i)⁻¹) ^ (k + 1))
          ((r.Q i).coeff (k + 2) * ((z - pole i)⁻¹) ^ (k + 2)) z := by
      intro k _
      have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      have := ((hasDerivAt_inv_sub i hz).pow (k + 1)).const_mul
        (-((r.Q i).coeff (k + 2)) / ((k : ℂ) + 1))
      refine this.congr_deriv ?_
      simp only [Nat.add_sub_cancel]
      rw [show (-1 : ℂ) / (z - pole i) ^ 2 = -((z - pole i)⁻¹ ^ 2) by rw [inv_pow]; ring]
      generalize (z - pole i)⁻¹ = u
      push_cast
      field_simp
      ring
    have h := HasDerivAt.fun_sum hterm
    refine h.congr_deriv ?_
    rw [eval_eq_sum_range' (Nat.lt_add_of_pos_right (by norm_num) :
      (r.Q i).natDegree < (r.Q i).natDegree + 2), Finset.sum_range_succ', Finset.sum_range_succ', hr i]
    simp
  have := hP.add (HasDerivAt.fun_sum hQ)
  refine this.congr_deriv ?_
  simp only [eval]
  rw [Finset.sum_sub_distrib]
  ring

end Rep

/-! ## Polynomials with coefficients in a subring -/

/-- `N ∈ ℂ[X]` is the image of a polynomial over the subring `R` -/
def CoeffIn (R : Subring ℂ) (N : ℂ[X]) : Prop := ∃ q : (↥R)[X], q.map R.subtype = N

namespace CoeffIn

variable {R : Subring ℂ}

lemma coeff_mem {N : ℂ[X]} (h : CoeffIn R N) (j : ℕ) : N.coeff j ∈ R := by
  obtain ⟨q, rfl⟩ := h
  rw [coeff_map]
  exact (q.coeff j).2

lemma of_coeff_mem {N : ℂ[X]} (h : ∀ j, N.coeff j ∈ R) : CoeffIn R N := by
  have : N ∈ Polynomial.lifts R.subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨N.coeff n, h n⟩, rfl⟩
  exact (Polynomial.mem_lifts _).1 this

lemma C_mem {a : ℂ} (ha : a ∈ R) : CoeffIn R (C a) := ⟨C ⟨a, ha⟩, by simp⟩

lemma X_mem : CoeffIn R (X : ℂ[X]) := ⟨X, by simp⟩

lemma one : CoeffIn R (1 : ℂ[X]) := ⟨1, by simp⟩

lemma zero : CoeffIn R (0 : ℂ[X]) := ⟨0, by simp⟩

lemma add {N M : ℂ[X]} (hN : CoeffIn R N) (hM : CoeffIn R M) : CoeffIn R (N + M) := by
  obtain ⟨q, rfl⟩ := hN
  obtain ⟨q', rfl⟩ := hM
  exact ⟨q + q', by simp⟩

lemma mul {N M : ℂ[X]} (hN : CoeffIn R N) (hM : CoeffIn R M) : CoeffIn R (N * M) := by
  obtain ⟨q, rfl⟩ := hN
  obtain ⟨q', rfl⟩ := hM
  exact ⟨q * q', by simp⟩

lemma neg {N : ℂ[X]} (hN : CoeffIn R N) : CoeffIn R (-N) := by
  obtain ⟨q, rfl⟩ := hN
  exact ⟨-q, by simp⟩

lemma sub {N M : ℂ[X]} (hN : CoeffIn R N) (hM : CoeffIn R M) : CoeffIn R (N - M) := by
  obtain ⟨q, rfl⟩ := hN
  obtain ⟨q', rfl⟩ := hM
  exact ⟨q - q', by simp⟩

lemma pow {N : ℂ[X]} (hN : CoeffIn R N) (k : ℕ) : CoeffIn R (N ^ k) := by
  obtain ⟨q, rfl⟩ := hN
  exact ⟨q ^ k, by simp⟩

lemma derivative {N : ℂ[X]} (hN : CoeffIn R N) : CoeffIn R (derivative N) := by
  obtain ⟨q, rfl⟩ := hN
  exact ⟨Polynomial.derivative q, by rw [Polynomial.derivative_map]⟩

lemma prod {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) (h : ∀ i ∈ s, CoeffIn R (f i)) :
    CoeffIn R (∏ i ∈ s, f i) :=
  Finset.prod_induction f (CoeffIn R) (fun _ _ => mul) one h

lemma sum {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) (h : ∀ i ∈ s, CoeffIn R (f i)) :
    CoeffIn R (∑ i ∈ s, f i) :=
  Finset.sum_induction f (CoeffIn R) (fun _ _ => add) zero h

end CoeffIn

/-- the denominator `∏ (X − pole i)^{e i}` -/
noncomputable def denPoly (e : Fin 3 → ℕ) : ℂ[X] := ∏ i, (X - C (pole i)) ^ e i

lemma eval_denPoly (e : Fin 3 → ℕ) (z : ℂ) : (denPoly e).eval z = ∏ i, (z - pole i) ^ e i := by
  simp [denPoly, eval_prod]

lemma eval_denPoly_ne_zero (e : Fin 3 → ℕ) {z : ℂ} (hz : z ∈ Udom) : (denPoly e).eval z ≠ 0 := by
  rw [eval_denPoly]
  exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (sub_ne_zero.2 (hz i))

lemma denPoly_add (e₁ e₂ : Fin 3 → ℕ) : denPoly (e₁ + e₂) = denPoly e₁ * denPoly e₂ := by
  simp [denPoly, pow_add, Finset.prod_mul_distrib]

lemma denPoly_zero : denPoly 0 = 1 := by simp [denPoly]

lemma monic_denPoly (e : Fin 3 → ℕ) : (denPoly e).Monic :=
  monic_prod_of_monic _ _ fun i _ => (monic_X_sub_C _).pow _

lemma natDegree_denPoly (e : Fin 3 → ℕ) : (denPoly e).natDegree = ∑ i, e i := by
  unfold denPoly
  rw [natDegree_prod_of_monic _ _ fun i _ => (monic_X_sub_C _).pow _]
  apply Finset.sum_congr rfl
  intro i _
  rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]

lemma coeffIn_denPoly {R : Subring ℂ} (hpole : ∀ i, pole i ∈ R) (e : Fin 3 → ℕ) :
    CoeffIn R (denPoly e) :=
  CoeffIn.prod _ _ fun i _ => (CoeffIn.X_mem.sub (CoeffIn.C_mem (hpole i))).pow (e i)

/-! ## The class of functions `N(z)/∏(z − pole i)^{e i}` with `N ∈ R[z]` -/

/-- `φ = N/∏(z − pole i)^{e i}` on `Udom` with `N` a polynomial over `R` -/
def InA (R : Subring ℂ) (φ : ℂ → ℂ) : Prop :=
  ∃ (N : ℂ[X]) (e : Fin 3 → ℕ), CoeffIn R N ∧ ∀ z ∈ Udom, φ z = N.eval z / (denPoly e).eval z

namespace InA

variable {R : Subring ℂ} {φ ψ : ℂ → ℂ}

lemma congr (h : InA R φ) (hφ : ∀ z ∈ Udom, ψ z = φ z) : InA R ψ := by
  obtain ⟨N, e, hN, h⟩ := h
  exact ⟨N, e, hN, fun z hz => by rw [hφ z hz, h z hz]⟩

lemma of_poly {N : ℂ[X]} (hN : CoeffIn R N) : InA R (fun z => N.eval z) :=
  ⟨N, 0, hN, fun z _ => by rw [denPoly_zero]; simp⟩

lemma const {c : ℂ} (hc : c ∈ R) : InA R (fun _ => c) :=
  (of_poly (CoeffIn.C_mem hc)).congr (by simp)

lemma id : InA R (fun z => z) := (of_poly CoeffIn.X_mem).congr (by simp)

lemma mul (h : InA R φ) (h' : InA R ψ) : InA R (fun z => φ z * ψ z) := by
  obtain ⟨N, e, hN, hφ⟩ := h
  obtain ⟨N', e', hN', hψ⟩ := h'
  refine ⟨N * N', e + e', hN.mul hN', fun z hz => ?_⟩
  beta_reduce
  rw [hφ z hz, hψ z hz, denPoly_add, eval_mul, eval_mul, div_mul_div_comm]

lemma add (hpole : ∀ i, pole i ∈ R) (h : InA R φ) (h' : InA R ψ) :
    InA R (fun z => φ z + ψ z) := by
  obtain ⟨N, e, hN, hφ⟩ := h
  obtain ⟨N', e', hN', hψ⟩ := h'
  refine ⟨N * denPoly e' + N' * denPoly e, e + e',
    (hN.mul (coeffIn_denPoly hpole e')).add (hN'.mul (coeffIn_denPoly hpole e)), fun z hz => ?_⟩
  beta_reduce
  rw [hφ z hz, hψ z hz, denPoly_add]
  simp only [eval_add, eval_mul]
  rw [div_add_div _ _ (eval_denPoly_ne_zero e hz) (eval_denPoly_ne_zero e' hz)]
  ring

lemma smul {c : ℂ} (hc : c ∈ R) (h : InA R φ) : InA R (fun z => c * φ z) := (const hc).mul h

lemma neg (h : InA R φ) : InA R (fun z => -φ z) :=
  (smul (R.neg_mem R.one_mem) h).congr (by simp)

lemma sub (hpole : ∀ i, pole i ∈ R) (h : InA R φ) (h' : InA R ψ) :
    InA R (fun z => φ z - ψ z) :=
  (add hpole h h'.neg).congr (fun z _ => by ring)

lemma pow (h : InA R φ) (k : ℕ) : InA R (fun z => φ z ^ k) := by
  induction k with
  | zero => exact (const R.one_mem).congr (by simp)
  | succ k ih => exact (ih.mul h).congr (fun z _ => by rw [pow_succ])

lemma sum (hpole : ∀ i, pole i ∈ R) {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (h : ∀ i ∈ s, InA R (f i)) : InA R (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (const R.zero_mem).congr (by simp)
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact (add hpole h1 h2).congr (fun z _ => by rw [Finset.sum_insert ha])

lemma inv_sub_pole (i : Fin 3) : InA R (fun z => (z - pole i)⁻¹) := by
  refine ⟨1, Pi.single i 1, CoeffIn.one, fun z _ => ?_⟩
  have : ∏ j, (z - pole j) ^ (Pi.single i 1 : Fin 3 → ℕ) j = z - pole i := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  rw [eval_denPoly, this]
  simp

/-- the derivative of a function of the class is in the class -/
lemma exists_deriv (hpole : ∀ i, pole i ∈ R) (h : InA R φ) :
    ∃ φ' : ℂ → ℂ, InA R φ' ∧ ∀ z ∈ Udom, HasDerivAt φ (φ' z) z := by
  obtain ⟨N, e, hN, hφ⟩ := h
  refine ⟨fun z => ((Polynomial.derivative N).eval z * (denPoly e).eval z -
      N.eval z * (Polynomial.derivative (denPoly e)).eval z) / ((denPoly e).eval z) ^ 2, ?_, ?_⟩
  · refine ⟨Polynomial.derivative N * denPoly e - N * Polynomial.derivative (denPoly e), e + e,
      (hN.derivative.mul (coeffIn_denPoly hpole e)).sub
        (hN.mul (coeffIn_denPoly hpole e).derivative), fun z _ => ?_⟩
    rw [denPoly_add]
    simp only [eval_sub, eval_mul]
    rw [sq]
  · intro z hz
    have hd := (N.hasDerivAt z).div ((denPoly e).hasDerivAt z) (eval_denPoly_ne_zero e hz)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Udom.mem_nhds hz] with w hw
    exact hφ w hw

end InA

/-- **Existence.** A function `N/∏(z − pole i)^{e i}` with `N ∈ R[z]` has a representation with
coefficients in `R`, provided the differences of the poles are units of `R`. -/
theorem exists_rep (R : Subring ℂ) (hpole : ∀ i, pole i ∈ R)
    (hunit : ∀ i j : Fin 3, i ≠ j → (pole i - pole j)⁻¹ ∈ R)
    {N : ℂ[X]} (hN : CoeffIn R N) (e : Fin 3 → ℕ) :
    ∃ r : Rep, r.Proper ∧ CoeffIn R r.P ∧ (∀ i, CoeffIn R (r.Q i)) ∧
      (∀ i, (r.Q i).natDegree ≤ e i) ∧
      (0 < ∑ i, e i → r.P = 0 ∨ r.P.natDegree + ∑ i, e i ≤ N.natDegree) ∧
      ∀ z ∈ Udom, r.eval z = N.eval z / (denPoly e).eval z := by
  classical
  obtain ⟨N', rfl⟩ := hN
  let a : Fin 3 → ↥R := fun i => ⟨pole i, hpole i⟩
  let g : Fin 3 → (↥R)[X] := fun i => X - C (a i)
  have hg : ∀ i ∈ (Finset.univ : Finset (Fin 3)), (g i).Monic := fun i _ => monic_X_sub_C (a i)
  have hgg : Set.Pairwise (↑(Finset.univ : Finset (Fin 3))) fun i j => IsCoprime (g i) (g j) := by
    intro i _ j _ hij
    apply isCoprime_X_sub_C_of_isUnit_sub
    refine isUnit_iff_exists_inv.2 ⟨⟨(pole i - pole j)⁻¹, hunit i j hij⟩, ?_⟩
    apply Subtype.ext
    show (pole i - pole j) * (pole i - pole j)⁻¹ = 1
    exact mul_inv_cancel₀ (sub_ne_zero.2 (pole_ne hij))
  obtain ⟨q, r, hr, hf⟩ := eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow N' hg hgg e
  have hrc : ∀ (i : Fin 3) (j : Fin (e i)), r i j = C ((r i j).coeff 0) := by
    intro i j
    apply eq_C_of_degree_le_zero
    have h1 := hr i (Finset.mem_univ i) j
    rw [show (g i).degree = 1 from degree_X_sub_C (a i)] at h1
    exact Nat.WithBot.lt_one_iff_le_zero.1 h1
  let c : (i : Fin 3) → Fin (e i) → ℂ := fun i j => (((r i j).coeff 0 : ↥R) : ℂ)
  have hgmap : ∀ i, (g i).map R.subtype = X - C (pole i) := by
    intro i
    simp [g, a]
  have hmap : N'.map R.subtype = q.map R.subtype * denPoly e
      + ∑ i, ∑ j : Fin (e i), C (c i j) * (X - C (pole i)) ^ j.1 *
          ∏ k ∈ Finset.univ.erase i, (X - C (pole k)) ^ e k := by
    conv_lhs => rw [hf]
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sum]
    congr 1
    · congr 1
      unfold denPoly
      apply Finset.prod_congr rfl
      intro i _
      rw [Polynomial.map_pow, hgmap]
    · apply Finset.sum_congr rfl
      intro i _
      rw [Polynomial.map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_pow, hgmap]
      congr 1
      · congr 1
        conv_lhs => rw [hrc i j]
        simp [c]
      · apply Finset.prod_congr rfl
        intro k _
        rw [Polynomial.map_pow, hgmap]
  refine ⟨⟨q.map R.subtype, fun i => ∑ j : Fin (e i), C (c i j) * X ^ (e i - j.1)⟩,
    ?_, ⟨q, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro i
    show (∑ j : Fin (e i), C (c i j) * X ^ (e i - j.1)).coeff 0 = 0
    rw [finset_sum_coeff]
    apply Finset.sum_eq_zero
    intro j _
    rw [coeff_C_mul_X_pow, if_neg]
    have := j.2
    omega
  · intro i
    show CoeffIn R (∑ j : Fin (e i), C (c i j) * X ^ (e i - j.1))
    exact CoeffIn.sum _ _ fun j _ => (CoeffIn.C_mem ((r i j).coeff 0).2).mul (CoeffIn.X_mem.pow _)
  · intro i
    show (∑ j : Fin (e i), C (c i j) * X ^ (e i - j.1)).natDegree ≤ e i
    apply natDegree_sum_le_of_forall_le
    intro j _
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)
  · intro hE
    show q.map R.subtype = 0 ∨
      (q.map R.subtype).natDegree + ∑ i, e i ≤ (N'.map R.subtype).natDegree
    by_cases hq : q.map R.subtype = 0
    · exact Or.inl hq
    · right
      have hT : ∀ (i : Fin 3) (j : Fin (e i)),
          (C (c i j) * (X - C (pole i)) ^ j.1 *
            ∏ k ∈ Finset.univ.erase i, (X - C (pole k)) ^ e k).natDegree ≤ ∑ i, e i - 1 := by
        intro i j
        have h1 : (C (c i j) * (X - C (pole i)) ^ j.1).natDegree ≤ j.1 := by
          refine (natDegree_C_mul_le _ _).trans ?_
          refine (natDegree_pow_le).trans ?_
          rw [natDegree_X_sub_C, mul_one]
        have h2 : (∏ k ∈ Finset.univ.erase i, (X - C (pole k)) ^ e k).natDegree
            ≤ ∑ k ∈ Finset.univ.erase i, e k := by
          refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          refine (natDegree_pow_le).trans ?_
          rw [natDegree_X_sub_C, mul_one]
        have h3 : e i + ∑ k ∈ Finset.univ.erase i, e k = ∑ k, e k :=
          Finset.add_sum_erase _ _ (Finset.mem_univ i)
        have := j.2
        refine (natDegree_mul_le).trans ?_
        omega
      have hS : (∑ i, ∑ j : Fin (e i), C (c i j) * (X - C (pole i)) ^ j.1 *
          ∏ k ∈ Finset.univ.erase i, (X - C (pole k)) ^ e k).natDegree ≤ ∑ i, e i - 1 :=
        natDegree_sum_le_of_forall_le _ _ fun i _ =>
          natDegree_sum_le_of_forall_le _ _ fun j _ => hT i j
      have hqD : (q.map R.subtype * denPoly e).natDegree
          = (q.map R.subtype).natDegree + ∑ i, e i := by
        rw [natDegree_mul hq (monic_denPoly e).ne_zero, natDegree_denPoly]
      rw [hmap, natDegree_add_eq_left_of_natDegree_lt (by rw [hqD]; omega), hqD]
  · intro z hz
    have hD := eval_denPoly_ne_zero e hz
    rw [eq_div_iff hD, hmap]
    simp only [Rep.eval, eval_add, eval_mul, eval_finset_sum, eval_prod, eval_pow, eval_sub,
      eval_X, eval_C]
    rw [add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    have hne : z - pole i ≠ 0 := sub_ne_zero.2 (hz i)
    have hDi : (denPoly e).eval z
        = (z - pole i) ^ e i * ∏ k ∈ Finset.univ.erase i, (z - pole k) ^ e k := by
      rw [eval_denPoly]
      exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    have hpow : ((z - pole i)⁻¹) ^ (e i - j.1) * (z - pole i) ^ e i = (z - pole i) ^ j.1 := by
      have hj : (e i - j.1) + j.1 = e i := by
        have := j.2
        omega
      have hx : (z - pole i) ^ e i = (z - pole i) ^ (e i - j.1) * (z - pole i) ^ j.1 := by
        rw [← pow_add, hj]
      rw [hx, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hne, one_pow, one_mul]
    rw [hDi]
    calc c i j * (z - pole i)⁻¹ ^ (e i - j.1) *
          ((z - pole i) ^ e i * ∏ k ∈ Finset.univ.erase i, (z - pole k) ^ e k)
        = c i j * ((z - pole i)⁻¹ ^ (e i - j.1) * (z - pole i) ^ e i) *
          ∏ k ∈ Finset.univ.erase i, (z - pole k) ^ e k := by ring
      _ = c i j * (z - pole i) ^ j.1 * ∏ k ∈ Finset.univ.erase i, (z - pole k) ^ e k := by
          rw [hpow]

end PiMeasure
