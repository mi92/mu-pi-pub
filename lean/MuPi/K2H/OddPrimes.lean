import MuPi.K2H.PF
import MuPi.K2H.QForm
import MuPi.K2H.LinearForm

/-!
# Odd primes (Lemmas 3.1 and 4.1 of `K2H_PROOF.md`, triple `(5,3,4)`)

For an odd prime `p` the function `f^n/z` has a partial-fraction representation with `p`-integral
coefficients; integrating term by term gives `p^{⌊log_p 4n⌋}·u_n` `p`-integral (Lemma 3.1).
For a removable prime the identity `f^n/z = (g^p G_red)' − p·g^{p-1} g' G_red` shows that every
coefficient whose integration index is divisible by `p` lies in `p·R_p`, hence `u_n` itself is
`p`-integral (Lemma 4.1).
-/

namespace PiMeasure

open Polynomial Complex

/-- the subring of `p`-integers of `ℂ` -/
def Rp (p : ℕ) (hp : p.Prime) : Subring ℂ where
  carrier := {x | PInt p x}
  mul_mem' := fun ha hb => PInt.mul hp ha hb
  one_mem' := PInt.one hp
  add_mem' := fun ha hb => PInt.add hp ha hb
  zero_mem' := PInt.zero hp
  neg_mem' := fun ha => PInt.neg ha

lemma mem_Rp {p : ℕ} {hp : p.Prime} {x : ℂ} : x ∈ Rp p hp ↔ PInt p x := Iff.rfl

section odd

lemma not_dvd_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)

lemma two_inv_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ℂ)⁻¹ ∈ Rp p hp := by
  have := PInt.inv_natCast (p := p) (N := 2) (not_dvd_two hp hp2)
  simpa using this

lemma four_inv_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (4 : ℂ)⁻¹ ∈ Rp p hp := by
  have h := (Rp p hp).mul_mem (two_inv_mem hp hp2) (two_inv_mem hp hp2)
  have e : (4 : ℂ)⁻¹ = (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ := by norm_num
  rw [e]
  exact h

lemma s2_mem {p : ℕ} (hp : p.Prime) : s2 ∈ Rp p hp := PInt.of_isIntegral hp s2_isIntegral

lemma I_mem {p : ℕ} (hp : p.Prime) : Complex.I ∈ Rp p hp := PInt.of_isIntegral hp I_isIntegral

lemma s2_inv_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : s2⁻¹ ∈ Rp p hp := by
  have e : s2⁻¹ = s2 * (2 : ℂ)⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, ← sq, s2_sq]
    norm_num
  rw [e]
  exact (Rp p hp).mul_mem (s2_mem hp) (two_inv_mem hp hp2)

lemma pole_mem {p : ℕ} (hp : p.Prime) (i : Fin 3) : pole i ∈ Rp p hp := by
  fin_cases i
  · exact (Rp p hp).zero_mem
  · exact s2_mem hp
  · exact (Rp p hp).neg_mem (s2_mem hp)

lemma pole_sub_inv_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i j : Fin 3) (hij : i ≠ j) : (pole i - pole j)⁻¹ ∈ Rp p hp := by
  have h1 := s2_inv_mem hp hp2
  have h2 : (2 * s2)⁻¹ ∈ Rp p hp := by
    rw [mul_inv]
    exact (Rp p hp).mul_mem (two_inv_mem hp hp2) h1
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · show ((0 : ℂ) - s2)⁻¹ ∈ Rp p hp
    rw [zero_sub, inv_neg]
    exact (Rp p hp).neg_mem h1
  · show ((0 : ℂ) - -s2)⁻¹ ∈ Rp p hp
    rw [zero_sub, neg_neg]
    exact h1
  · show (s2 - 0)⁻¹ ∈ Rp p hp
    rw [sub_zero]
    exact h1
  · exact absurd rfl hij
  · show (s2 - -s2)⁻¹ ∈ Rp p hp
    rw [sub_neg_eq_add, ← two_mul]
    exact h2
  · show (-s2 - 0)⁻¹ ∈ Rp p hp
    rw [sub_zero, inv_neg]
    exact (Rp p hp).neg_mem h1
  · show (-s2 - s2)⁻¹ ∈ Rp p hp
    rw [show -s2 - s2 = -(2 * s2) by ring, inv_neg]
    exact (Rp p hp).neg_mem h2
  · exact absurd rfl hij

/-- the end points `1 ± i` are units distance from the poles -/
lemma endpoint_inv_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i : Fin 3) :
    (1 + I - pole i)⁻¹ ∈ Rp p hp ∧ (1 - I - pole i)⁻¹ ∈ Rp p hp := by
  have h2 := two_inv_mem hp hp2
  have h4 := four_inv_mem hp hp2
  have hI := I_mem hp
  have hs := s2_mem hp
  have h1 := (Rp p hp).one_mem
  have hP : (1 + I - s2) * (1 + I + s2) * (-1 - I) = 4 := by
    linear_combination (-3 - I) * Complex.I_sq + (1 + I) * s2_sq
  have hM : (1 - I - s2) * (1 - I + s2) * (-1 + I) = 4 := by
    linear_combination (-3 + I) * Complex.I_sq + (1 - I) * s2_sq
  have e1 : (1 + I : ℂ)⁻¹ = (1 - I) * (2 : ℂ)⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    linear_combination (-1 : ℂ) * Complex.I_sq
  have e2 : (1 - I : ℂ)⁻¹ = (1 + I) * (2 : ℂ)⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    linear_combination (-1 : ℂ) * Complex.I_sq
  have e3 : (1 + I - s2)⁻¹ = (1 + I + s2) * (-1 - I) * (4 : ℂ)⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    linear_combination hP
  have e4 : (1 + I + s2)⁻¹ = (1 + I - s2) * (-1 - I) * (4 : ℂ)⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    linear_combination hP
  have e5 : (1 - I - s2)⁻¹ = (1 - I + s2) * (-1 + I) * (4 : ℂ)⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    linear_combination hM
  have e6 : (1 - I + s2)⁻¹ = (1 - I - s2) * (-1 + I) * (4 : ℂ)⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    linear_combination hM
  have a1 : (1 + I : ℂ) ∈ Rp p hp := (Rp p hp).add_mem h1 hI
  have a0 : (1 - I : ℂ) ∈ Rp p hp := (Rp p hp).sub_mem h1 hI
  have m1 : (-1 - I : ℂ) ∈ Rp p hp := (Rp p hp).sub_mem ((Rp p hp).neg_mem h1) hI
  have m0 : (-1 + I : ℂ) ∈ Rp p hp := (Rp p hp).add_mem ((Rp p hp).neg_mem h1) hI
  fin_cases i
  · constructor
    · show (1 + I - 0)⁻¹ ∈ Rp p hp
      rw [sub_zero, e1]
      exact (Rp p hp).mul_mem a0 h2
    · show (1 - I - 0)⁻¹ ∈ Rp p hp
      rw [sub_zero, e2]
      exact (Rp p hp).mul_mem a1 h2
  · constructor
    · show (1 + I - s2)⁻¹ ∈ Rp p hp
      rw [e3]
      exact (Rp p hp).mul_mem ((Rp p hp).mul_mem ((Rp p hp).add_mem a1 hs) m1) h4
    · show (1 - I - s2)⁻¹ ∈ Rp p hp
      rw [e5]
      exact (Rp p hp).mul_mem ((Rp p hp).mul_mem ((Rp p hp).add_mem a0 hs) m0) h4
  · constructor
    · show (1 + I - -s2)⁻¹ ∈ Rp p hp
      rw [sub_neg_eq_add, e4]
      exact (Rp p hp).mul_mem ((Rp p hp).mul_mem ((Rp p hp).sub_mem a1 hs) m1) h4
    · show (1 - I - -s2)⁻¹ ∈ Rp p hp
      rw [sub_neg_eq_add, e6]
      exact (Rp p hp).mul_mem ((Rp p hp).mul_mem ((Rp p hp).sub_mem a0 hs) m0) h4

/-- **Term-by-term integration.** If `L·(coefficient)/(index)` is `p`-integral for every term of
the standard primitive, then `L·(F(1+i) − F(1−i))` is `p`-integral. -/
lemma PInt_delta_primFun {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (r : Rep) (L : ℂ)
    (h1 : ∀ j, PInt p (L * (r.P.coeff j / ((j : ℂ) + 1))))
    (h2 : ∀ i k, PInt p (L * ((r.Q i).coeff (k + 2) / ((k : ℂ) + 1)))) :
    PInt p (L * (r.primFun (1 + I) - r.primFun (1 - I))) := by
  have hI : PInt p I := I_mem hp
  have a1 : PInt p (1 + I) := PInt.add hp (PInt.one hp) hI
  have a0 : PInt p (1 - I) := PInt.sub hp (PInt.one hp) hI
  have hA : PInt p (L * (∑ j ∈ Finset.range (r.P.natDegree + 1),
        r.P.coeff j / ((j : ℂ) + 1) * (1 + I) ^ (j + 1))
      - L * (∑ j ∈ Finset.range (r.P.natDegree + 1),
        r.P.coeff j / ((j : ℂ) + 1) * (1 - I) ^ (j + 1))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine PInt.sum hp _ _ fun j _ => ?_
    have e : L * (r.P.coeff j / ((j : ℂ) + 1) * (1 + I) ^ (j + 1))
        - L * (r.P.coeff j / ((j : ℂ) + 1) * (1 - I) ^ (j + 1))
        = L * (r.P.coeff j / ((j : ℂ) + 1)) * ((1 + I) ^ (j + 1) - (1 - I) ^ (j + 1)) := by ring
    rw [e]
    exact PInt.mul hp (h1 j) (PInt.sub hp (PInt.pow hp a1 _) (PInt.pow hp a0 _))
  have hB : PInt p (L * (∑ i, ∑ k ∈ Finset.range (r.Q i).natDegree,
        -((r.Q i).coeff (k + 2)) / ((k : ℂ) + 1) * ((1 + I - pole i)⁻¹) ^ (k + 1))
      - L * (∑ i, ∑ k ∈ Finset.range (r.Q i).natDegree,
        -((r.Q i).coeff (k + 2)) / ((k : ℂ) + 1) * ((1 - I - pole i)⁻¹) ^ (k + 1))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine PInt.sum hp _ _ fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine PInt.sum hp _ _ fun k _ => ?_
    have e : L * (-((r.Q i).coeff (k + 2)) / ((k : ℂ) + 1) * ((1 + I - pole i)⁻¹) ^ (k + 1))
        - L * (-((r.Q i).coeff (k + 2)) / ((k : ℂ) + 1) * ((1 - I - pole i)⁻¹) ^ (k + 1))
        = -(L * ((r.Q i).coeff (k + 2) / ((k : ℂ) + 1))) *
          (((1 + I - pole i)⁻¹) ^ (k + 1) - ((1 - I - pole i)⁻¹) ^ (k + 1)) := by ring
    rw [e]
    obtain ⟨u1, u0⟩ := endpoint_inv_mem hp hp2 i
    exact PInt.mul hp (h2 i k).neg (PInt.sub hp (PInt.pow hp u1 _) (PInt.pow hp u0 _))
  have := PInt.add hp hA hB
  convert this using 1
  unfold Rep.primFun
  ring

end odd

/-- `p^{⌊log_p M⌋}/m` is `p`-integral for `1 ≤ m ≤ M`. -/
lemma PInt_pow_log_div {p : ℕ} (hp : p.Prime) {M m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ M) :
    PInt p ((p : ℂ) ^ (Nat.log p M) / (m : ℂ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hm0 : m ≠ 0 := by omega
  set v := padicValNat p m with hv
  have hvle : v ≤ Nat.log p M := (padicValNat_le_nat_log m).trans (Nat.log_mono_right hmM)
  have hodd : ¬ p ∣ m / p ^ v := by
    have := Nat.not_dvd_ordCompl hp hm0
    rwa [Nat.factorization_def m hp] at this
  have hmul : p ^ v * (m / p ^ v) = m := Nat.mul_div_cancel' pow_padicValNat_dvd
  have hm' : (m : ℂ) = (p : ℂ) ^ v * ((m / p ^ v : ℕ) : ℂ) := by exact_mod_cast hmul.symm
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : ((m / p ^ v : ℕ) : ℂ) ≠ 0 := by
    intro h
    apply hodd
    have : m / p ^ v = 0 := by exact_mod_cast h
    rw [this]
    exact dvd_zero p
  have e : (p : ℂ) ^ (Nat.log p M) / (m : ℂ)
      = (p : ℂ) ^ (Nat.log p M - v) * ((m / p ^ v : ℕ) : ℂ)⁻¹ := by
    rw [hm']
    have hpow : (p : ℂ) ^ (Nat.log p M) = (p : ℂ) ^ (Nat.log p M - v) * (p : ℂ) ^ v := by
      rw [← pow_add, Nat.sub_add_cancel hvle]
    rw [hpow]
    field_simp
  rw [e]
  exact PInt.mul hp (PInt.pow hp (PInt.natCast hp p) _) (PInt.inv_natCast hodd)

/-- `p/m` is `p`-integral for `1 ≤ m < p²`. -/
lemma PInt_p_div {p : ℕ} (hp : p.Prime) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < p ^ 2) :
    PInt p ((p : ℂ) / (m : ℂ)) := by
  by_cases hd : p ∣ m
  · obtain ⟨m', rfl⟩ := hd
    have hm'pos : 1 ≤ m' := by
      rcases Nat.eq_zero_or_pos m' with h | h
      · rw [h] at hm1
        simp at hm1
      · exact h
    have hm'lt : m' < p := by
      have hp0 := hp.pos
      by_contra hge
      have : p * p ≤ p * m' := Nat.mul_le_mul_left p (not_lt.1 hge)
      nlinarith
    have hnd : ¬ p ∣ m' := fun h => by
      have := Nat.le_of_dvd hm'pos h
      omega
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have e : (p : ℂ) / ((p * m' : ℕ) : ℂ) = ((m' : ℕ) : ℂ)⁻¹ := by
      push_cast
      field_simp
    rw [e]
    exact PInt.inv_natCast hnd
  · rw [div_eq_mul_inv]
    exact PInt.mul hp (PInt.natCast hp p) (PInt.inv_natCast hd)

/-! ## `f^n/z` as a quotient of polynomials -/

/-- the numerator `((X−1)(X−2))^5 (X²−2X+2)^3` over `ℂ` -/
noncomputable def NC : ℂ[X] := ((X - C 1) * (X - C 2)) ^ 5 * (X ^ 2 - C 2 * X + C 2) ^ 3

/-- exponents of the denominator of `f^n/z` -/
def eH (n : ℕ) : Fin 3 → ℕ := ![4 * n + 1, 4 * n, 4 * n]

lemma eH_zero (n : ℕ) : eH n 0 = 4 * n + 1 := rfl

lemma eH_one (n : ℕ) : eH n 1 = 4 * n := rfl

lemma eH_two (n : ℕ) : eH n 2 = 4 * n := rfl

lemma sum_eH (n : ℕ) : ∑ i, eH n i = 12 * n + 1 := by
  rw [Fin.sum_univ_three, eH_zero, eH_one, eH_two]
  ring

lemma two_mem (R : Subring ℂ) : (2 : ℂ) ∈ R := by
  have := R.add_mem R.one_mem R.one_mem
  rwa [one_add_one_eq_two] at this

lemma coeffIn_NC (R : Subring ℂ) : CoeffIn R NC := by
  unfold NC
  have h1 : CoeffIn R (C (1 : ℂ)) := CoeffIn.C_mem R.one_mem
  have h2 : CoeffIn R (C (2 : ℂ)) := CoeffIn.C_mem (two_mem R)
  have hX : CoeffIn R (X : ℂ[X]) := CoeffIn.X_mem
  exact (((hX.sub h1).mul (hX.sub h2)).pow 5).mul ((((hX.pow 2).sub (h2.mul hX)).add h2).pow 3)

lemma natDegree_NC_pow (n : ℕ) : (NC ^ n).natDegree ≤ 16 * n := by
  have h : NC.natDegree ≤ 16 := by
    unfold NC
    compute_degree
  calc (NC ^ n).natDegree ≤ n * NC.natDegree := natDegree_pow_le
    _ ≤ n * 16 := Nat.mul_le_mul_left n h
    _ = 16 * n := by ring

lemma eval_NC (z : ℂ) : NC.eval z = ((z - 1) * (z - 2)) ^ 5 * (z ^ 2 - 2 * z + 2) ^ 3 := by
  simp [NC]

lemma sq_sub_two (z : ℂ) : z ^ 2 - 2 = (z - s2) * (z + s2) := by
  linear_combination s2_sq

lemma hfun_eq (n : ℕ) {z : ℂ} (hz : z ∈ Udom) :
    f534 z ^ n / z = (NC ^ n).eval z / (denPoly (eH n)).eval z := by
  obtain ⟨hz0, hz1, hz2⟩ := mem_Udom.1 hz
  have hm : z - s2 ≠ 0 := sub_ne_zero.2 hz1
  have hp : z + s2 ≠ 0 := by
    intro h
    apply hz2
    linear_combination h
  rw [eval_denPoly, Fin.prod_univ_three, eH_zero, eH_one, eH_two, pole_zero, pole_one, pole_two,
    eval_pow, eval_NC]
  unfold f534
  have hden : (z ^ 4 * ((z - s2) * (z + s2)) ^ 4) ^ n * z
      = z ^ (4 * n + 1) * (z - s2) ^ (4 * n) * (z + s2) ^ (4 * n) := by
    rw [mul_pow (z - s2) (z + s2) 4, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, pow_succ]
    ring
  rw [sq_sub_two, sub_zero, sub_neg_eq_add, div_pow, div_div, hden]

/-! ## The class `InA R` as a class of admissible primitives -/

lemma Wf_eq {z : ℂ} (hz0 : z ≠ 0) : Wf z = (z ^ 2 + 2) * z⁻¹ := by
  unfold Wf
  field_simp

lemma Yf_inv_eq {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ s2) (hz2 : z ≠ -s2) :
    (Yf z)⁻¹ = z * (z - s2)⁻¹ * (z + s2)⁻¹ := by
  have hm : z - s2 ≠ 0 := sub_ne_zero.2 hz1
  have hp : z + s2 ≠ 0 := by
    intro h
    apply hz2
    linear_combination h
  have hY : Yf z = (z - s2) * (z + s2) / z := by
    unfold Yf
    field_simp
    linear_combination s2_sq
  rw [hY, inv_div]
  field_simp

lemma InA.Wf_mem {R : Subring ℂ} : InA R (fun z => Wf z) := by
  have h1 : InA R (fun z => (X ^ 2 + C 2 : ℂ[X]).eval z) :=
    InA.of_poly ((CoeffIn.X_mem.pow 2).add (CoeffIn.C_mem (two_mem R)))
  refine (h1.mul (InA.inv_sub_pole 0)).congr fun z hz => ?_
  rw [Wf_eq (mem_Udom.1 hz).1, pole_zero, sub_zero]
  simp

lemma InA.Yf_inv_mem {R : Subring ℂ} : InA R (fun z => (Yf z)⁻¹) := by
  refine ((InA.id.mul (InA.inv_sub_pole 1)).mul (InA.inv_sub_pole 2)).congr fun z hz => ?_
  obtain ⟨hz0, hz1, hz2⟩ := mem_Udom.1 hz
  rw [Yf_inv_eq hz0 hz1 hz2, pole_one, pole_two, sub_neg_eq_add]

/-- `InA R` is a class of admissible primitives in the sense of `QForm` -/
noncomputable def primClassInA (R : Subring ℂ) (hpole : ∀ i, pole i ∈ R) : PrimClass R where
  mem := InA R
  mem_zero := InA.const R.zero_mem
  mem_add := fun hF hG => InA.add hpole hF hG
  mem_smul := fun hr hF => InA.smul hr hF
  mem_zpow := by
    intro l _
    rcases Int.le_total 0 l with hl | hl
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hl
      exact (InA.id.pow k).congr fun z _ => by rw [zpow_natCast]
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hl)
      have hl' : l = -(k : ℤ) := by omega
      exact ((InA.inv_sub_pole 0).pow k).congr fun z _ => by
        rw [hl', zpow_neg, zpow_natCast, pole_zero, sub_zero, inv_pow]
  mem_WY := by
    intro j m
    exact ((InA.Wf_mem.pow j).mul (InA.Yf_inv_mem.pow (2 * m + 1))).congr fun z _ => by
      rw [inv_pow]

/-- a function of the class has a representation over `R` -/
lemma InA.exists_rep' {R : Subring ℂ} (hpole : ∀ i, pole i ∈ R)
    (hunit : ∀ i j : Fin 3, i ≠ j → (pole i - pole j)⁻¹ ∈ R) {φ : ℂ → ℂ} (h : InA R φ) :
    ∃ r : Rep, r.Proper ∧ CoeffIn R r.P ∧ (∀ i, CoeffIn R (r.Q i)) ∧
      ∀ z ∈ Udom, r.eval z = φ z := by
  obtain ⟨N, e, hN, hφ⟩ := h
  obtain ⟨r, hr, hP, hQ, -, -, hev⟩ := exists_rep R hpole hunit hN e
  exact ⟨r, hr, hP, hQ, fun z hz => by rw [hev z hz, hφ z hz]⟩

lemma InA.mono {R : Subring ℂ} {φ : ℂ → ℂ} (h : InA R φ) : InA ⊤ φ := by
  obtain ⟨N, e, _, hφ⟩ := h
  exact ⟨N, e, CoeffIn.of_coeff_mem fun _ => Subring.mem_top _, hφ⟩

/-- if `r` represents `G' + c/z` with `G` in the class, then the residues of `r` are `c, 0, 0` -/
lemma residue_of_primitive (r : Rep) (hr : r.Proper) {G : ℂ → ℂ} (hG : InA ⊤ G) (c : ℂ)
    (h : ∀ z ∈ Udom, HasDerivAt G (r.eval z - c / z) z) :
    (r.Q 0).coeff 1 = c ∧ (r.Q 1).coeff 1 = 0 ∧ (r.Q 2).coeff 1 = 0 := by
  obtain ⟨rG, hGp, -, -, hGev⟩ := InA.exists_rep' (R := ⊤) (fun _ => Subring.mem_top _)
    (fun _ _ _ => Subring.mem_top _) hG
  have hkey : ∀ z ∈ Udom, r.eval z = (rG.deriv.add (Rep.resRep ![c, 0, 0])).eval z := by
    intro z hz
    have h1 : HasDerivAt G (rG.deriv.eval z) z := by
      refine (rG.hasDerivAt_eval hz).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Udom.mem_nhds hz] with w hw
      exact (hGev w hw).symm
    have h2 := (h z hz).unique h1
    rw [Rep.eval_add, Rep.eval_resRep, Fin.sum_univ_three, ← h2, pole_zero, sub_zero]
    simp
    ring
  have heq := Rep.ext_of_eval hr (rG.deriv_proper.add (Rep.resRep_proper _)) hkey
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    simp [Rep.add, Rep.resRep, Rep.deriv_Q_coeff_one]
  · rw [heq]
    simp [Rep.add, Rep.resRep, Rep.deriv_Q_coeff_one]
  · rw [heq]
    simp [Rep.add, Rep.resRep, Rep.deriv_Q_coeff_one]

/-! ## The representation of `f^n/z` over the `p`-integers -/

/-- `((X−3)^5 (X−2)^3)^n`: `f^n = P(W)·Y^{-4n}` -/
noncomputable def PW (n : ℕ) : ℂ[X] := ((X - C 3) ^ 5 * (X - C 2) ^ 3) ^ n

lemma hfun_eq_WY (n : ℕ) {z : ℂ} (hz : z ∈ Udom) :
    f534 z ^ n / z = (PW n).eval (Wf z) * (Yf z ^ (2 * (2 * n)))⁻¹ / z := by
  obtain ⟨hz0, hz1, hz2⟩ := mem_Udom.1 hz
  rw [f534_eq_WY hz0 hz1 hz2]
  have hP : (PW n).eval (Wf z) = ((Wf z - 3) ^ 5 * (Wf z - 2) ^ 3) ^ n := by simp [PW]
  rw [hP, mul_pow ((Wf z - 3) ^ 5 * (Wf z - 2) ^ 3), inv_pow, ← pow_mul]
  congr 3
  ring

/-- The representation of `f^n/z` with `p`-integral coefficients (`p` odd), its degree bounds, the
vanishing of the residues at `±√2`, and the resulting primitive pair. -/
lemma exists_rep_h (n p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ r : Rep, r.Proper ∧ CoeffIn (Rp p hp) r.P ∧ (∀ i, CoeffIn (Rp p hp) (r.Q i)) ∧
      (∀ j, 4 * n ≤ j → r.P.coeff j = 0) ∧ (∀ i k, 4 * n + 1 < k → (r.Q i).coeff k = 0) ∧
      (∀ z ∈ Udom, r.eval z = f534 z ^ n / z) ∧
      IsPrimPair n r.primFun ((r.Q 0).coeff 1) := by
  obtain ⟨r, hr, hP, hQ, hdeg, hPdeg, hev⟩ := exists_rep (Rp p hp) (pole_mem hp)
    (pole_sub_inv_mem hp hp2) ((coeffIn_NC (Rp p hp)).pow n) (eH n)
  have hφ : ∀ z ∈ Udom, r.eval z = f534 z ^ n / z := fun z hz => by
    rw [hev z hz, hfun_eq n hz]
  refine ⟨r, hr, hP, hQ, ?_, ?_, hφ, ?_⟩
  · intro j hj
    rcases hPdeg (by rw [sum_eH]; omega) with h0 | hle
    · rw [h0]
      simp
    · apply coeff_eq_zero_of_natDegree_lt
      have := natDegree_NC_pow n
      rw [sum_eH] at hle
      omega
  · intro i k hk
    apply coeff_eq_zero_of_natDegree_lt
    have h1 := hdeg i
    have h2 : eH n i ≤ 4 * n + 1 := by
      fin_cases i
      · exact le_of_eq (eH_zero n)
      · exact (le_of_eq (eH_one n)).trans (Nat.le_succ _)
      · exact (le_of_eq (eH_two n)).trans (Nat.le_succ _)
    omega
  · -- residues at ±√2 vanish: compare with the primitive from the W,Y-recursion
    obtain ⟨c, G, -, hG, hd⟩ := exists_primitive_WY ⊤
      (primClassInA ⊤ (fun _ => Subring.mem_top _)) (PW n) (fun _ => Subring.mem_top _) (2 * n)
      (Subring.mem_top _) (fun _ _ _ => Subring.mem_top _) (fun _ _ _ => Subring.mem_top _)
    have hG' : InA ⊤ G := hG
    have hres := residue_of_primitive r hr hG' c (fun z hz => by
      obtain ⟨hz0, hz1, hz2⟩ := mem_Udom.1 hz
      have := hd z hz0 hz1 hz2
      rwa [← hfun_eq_WY n hz, ← hφ z hz] at this)
    intro z hz0 hz1 hz2
    have hz : z ∈ Udom := mem_Udom.2 ⟨hz0, hz1, hz2⟩
    refine (r.hasDerivAt_primFun hr hz).congr_deriv ?_
    rw [Fin.sum_univ_three, hres.2.1, hres.2.2, hφ z hz, pole_zero, sub_zero]
    ring

/-- **Lemma 3.1 (trivial denominators).** For an odd prime `p` there is a primitive pair `(G, c)`
with `c` and `p^{⌊log_p 4n⌋}·(G(1+i) − G(1−i))` `p`-integral. -/
theorem oddPrime_trivial (n p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ (G : ℂ → ℂ) (c : ℂ), IsPrimPair n G c ∧ PInt p c ∧
      PInt p ((p : ℂ) ^ (Nat.log p (4 * n)) * (G (1 + I) - G (1 - I))) := by
  obtain ⟨r, hr, hP, hQ, hPz, hQz, -, hpair⟩ := exists_rep_h n p hp hp2
  refine ⟨r.primFun, (r.Q 0).coeff 1, hpair, (hQ 0).coeff_mem 1, ?_⟩
  apply PInt_delta_primFun hp hp2
  · intro j
    by_cases hj : j < 4 * n
    · have h1 := PInt_pow_log_div hp (M := 4 * n) (m := j + 1) (by omega) (by omega)
      have h2 : PInt p (r.P.coeff j) := hP.coeff_mem j
      have e : (p : ℂ) ^ (Nat.log p (4 * n)) * (r.P.coeff j / ((j : ℂ) + 1))
          = r.P.coeff j * ((p : ℂ) ^ (Nat.log p (4 * n)) / ((j + 1 : ℕ) : ℂ)) := by
        push_cast
        ring
      rw [e]
      exact PInt.mul hp h2 h1
    · rw [hPz j (by omega)]
      simpa using PInt.zero hp
  · intro i k
    by_cases hk : k < 4 * n
    · have h1 := PInt_pow_log_div hp (M := 4 * n) (m := k + 1) (by omega) (by omega)
      have h2 : PInt p ((r.Q i).coeff (k + 2)) := (hQ i).coeff_mem (k + 2)
      have e : (p : ℂ) ^ (Nat.log p (4 * n)) * ((r.Q i).coeff (k + 2) / ((k : ℂ) + 1))
          = (r.Q i).coeff (k + 2) * ((p : ℂ) ^ (Nat.log p (4 * n)) / ((k + 1 : ℕ) : ℂ)) := by
        push_cast
        ring
      rw [e]
      exact PInt.mul hp h2 h1
    · rw [hQz i (k + 2) (by omega)]
      simpa using PInt.zero hp

/-! ## Removable primes (Lemma 4.1) -/

lemma three_mem (R : Subring ℂ) : (3 : ℂ) ∈ R := by
  have := R.add_mem (two_mem R) R.one_mem
  rwa [two_add_one_eq_three] at this

/-- **Lemma 4.1, key identity.** For a removable prime `p`, the representation `r` of `f^n/z` is
`(rep of H)' − p·(rep of η)`, where `H = g^p G_red` and `η = g^{p-1} g' G_red` have representations
with `p`-integral coefficients. -/
theorem removable_decomp (n p : ℕ) (hrem : RemovablePrime n p) (hp2 : p ≠ 2)
    (r : Rep) (hr : r.Proper) (hφ : ∀ z ∈ Udom, r.eval z = f534 z ^ n / z) :
    ∃ rH rη : Rep, CoeffIn (Rp p hrem.1) rH.P ∧ (∀ i, CoeffIn (Rp p hrem.1) (rH.Q i)) ∧
      CoeffIn (Rp p hrem.1) rη.P ∧ (∀ i, CoeffIn (Rp p hrem.1) (rη.Q i)) ∧
      r = rH.deriv.sub (rη.smul (p : ℂ)) := by
  obtain ⟨hp, hp2n, hev, hlt⟩ := hrem
  have hpole : ∀ i, pole i ∈ Rp p hp := pole_mem hp
  have hunit := pole_sub_inv_mem hp hp2
  -- numerology
  obtain ⟨q1, α1, hq1, hα1⟩ : ∃ q1 α1, q1 = 5 * n / p ∧ α1 = 5 * n % p := ⟨_, _, rfl, rfl⟩
  obtain ⟨q2, α2, hq2, hα2⟩ : ∃ q2 α2, q2 = 3 * n / p ∧ α2 = 3 * n % p := ⟨_, _, rfl, rfl⟩
  obtain ⟨K, δ, hK, hδ⟩ : ∃ K δ, K = 4 * n / p ∧ δ = 4 * n % p := ⟨_, _, rfl, rfl⟩
  rw [← hα1, ← hα2, ← hδ] at hlt
  rw [← hK] at hev
  have h5 : q1 * p + α1 = 5 * n := by rw [hq1, hα1]; exact Nat.div_add_mod' _ _
  have h3 : q2 * p + α2 = 3 * n := by rw [hq2, hα2]; exact Nat.div_add_mod' _ _
  have h4 : K * p + δ = 4 * n := by rw [hK, hδ]; exact Nat.div_add_mod' _ _
  have hδp : δ < p := by rw [hδ]; exact Nat.mod_lt _ hp.pos
  obtain ⟨md, hmd⟩ : ∃ md, δ = 2 * md := by
    obtain ⟨k, hk⟩ := hev
    have hKp : K * p = 2 * (k * p) := by rw [hk]; ring
    exact ⟨δ / 2, by omega⟩
  -- the functions
  let g : ℂ → ℂ := fun z => (Wf z - 3) ^ q1 * (Wf z - 2) ^ q2 * ((Yf z)⁻¹) ^ K
  let ωred : ℂ → ℂ := fun z => (Wf z - 3) ^ α1 * (Wf z - 2) ^ α2 * (Yf z ^ δ)⁻¹ / z
  have hfac : ∀ z ∈ Udom, f534 z ^ n / z = g z ^ p * ωred z := by
    intro z hz
    obtain ⟨hz0, hz1, hz2⟩ := mem_Udom.1 hz
    rw [f534_eq_WY hz0 hz1 hz2]
    simp only [g, ωred]
    generalize Wf z - 3 = A
    generalize Wf z - 2 = B
    generalize Yf z = Y
    have eA : A ^ (5 * n) = (A ^ q1) ^ p * A ^ α1 := by rw [← pow_mul, ← pow_add, h5]
    have eB : B ^ (3 * n) = (B ^ q2) ^ p * B ^ α2 := by rw [← pow_mul, ← pow_add, h3]
    have eY : (Y ^ (4 * n))⁻¹ = ((Y⁻¹) ^ K) ^ p * (Y ^ δ)⁻¹ := by
      rw [← pow_mul, ← h4, pow_add, mul_inv, inv_pow]
    calc (A ^ 5 * B ^ 3 * (Y ^ 4)⁻¹) ^ n / z
        = A ^ (5 * n) * B ^ (3 * n) * (Y ^ (4 * n))⁻¹ / z := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, inv_pow, ← pow_mul]
      _ = (A ^ q1 * B ^ q2 * (Y⁻¹) ^ K) ^ p * (A ^ α1 * B ^ α2 * (Y ^ δ)⁻¹ / z) := by
          rw [eA, eB, eY]
          ring
  have hW3 : InA (Rp p hp) (fun z => Wf z - 3) :=
    InA.sub hpole InA.Wf_mem (InA.const (three_mem _))
  have hW2 : InA (Rp p hp) (fun z => Wf z - 2) :=
    InA.sub hpole InA.Wf_mem (InA.const (two_mem _))
  have hg : InA (Rp p hp) g := ((hW3.pow q1).mul (hW2.pow q2)).mul (InA.Yf_inv_mem.pow K)
  -- the primitive of ω_red over the p-integers
  let Pred : ℂ[X] := (X - C 3) ^ α1 * (X - C 2) ^ α2
  have hPredC : CoeffIn (Rp p hp) Pred :=
    ((CoeffIn.X_mem.sub (CoeffIn.C_mem (three_mem _))).pow α1).mul
      ((CoeffIn.X_mem.sub (CoeffIn.C_mem (two_mem _))).pow α2)
  have hPdeg : Pred.natDegree ≤ α1 + α2 := by
    refine natDegree_mul_le.trans (add_le_add ?_ ?_)
    · refine natDegree_pow_le.trans ?_
      rw [natDegree_X_sub_C, mul_one]
    · refine natDegree_pow_le.trans ?_
      rw [natDegree_X_sub_C, mul_one]
  obtain ⟨cred, Gred, -, hGred, hd⟩ := exists_primitive_WY (Rp p hp)
    (primClassInA (Rp p hp) hpole) Pred (fun j => hPredC.coeff_mem j) md (two_inv_mem hp hp2)
    (fun l hl1 hl2 => PInt.inv_natCast (fun hdvd => by
      have := Nat.le_of_dvd (by omega) hdvd
      omega))
    (fun k hk1 hk2 => by
      have hnd : ¬ p ∣ (2 * k - 1) := fun hdvd => by
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      have h := PInt.inv_natCast hnd
      have e : ((2 * k - 1 : ℕ) : ℂ) = 2 * (k : ℂ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
        push_cast
        ring
      rw [e] at h
      exact h)
  have hGredA : InA (Rp p hp) Gred := hGred
  have hωP : ∀ z : ℂ, Pred.eval (Wf z) * (Yf z ^ (2 * md))⁻¹ / z = ωred z := by
    intro z
    simp [ωred, Pred, hmd]
  -- ω_red has no pole at 0, so the constant c_red vanishes
  let Nred : ℂ[X] := ((X - C 1) * (X - C 2)) ^ α1 * (X ^ 2 - C 2 * X + C 2) ^ α2 *
    X ^ (δ - α1 - α2 - 1)
  have hNredC : CoeffIn (Rp p hp) Nred := by
    have h1 : CoeffIn (Rp p hp) (C (1 : ℂ)) := CoeffIn.C_mem (Rp p hp).one_mem
    have h2 : CoeffIn (Rp p hp) (C (2 : ℂ)) := CoeffIn.C_mem (two_mem _)
    have hX : CoeffIn (Rp p hp) (X : ℂ[X]) := CoeffIn.X_mem
    exact ((((hX.sub h1).mul (hX.sub h2)).pow α1).mul
      ((((hX.pow 2).sub (h2.mul hX)).add h2).pow α2)).mul (hX.pow _)
  have hωeq : ∀ z ∈ Udom, ωred z = Nred.eval z / (denPoly ![0, δ, δ]).eval z := by
    intro z hz
    obtain ⟨hz0, hz1, hz2⟩ := mem_Udom.1 hz
    have hm : z - s2 ≠ 0 := sub_ne_zero.2 hz1
    have hpl : z + s2 ≠ 0 := by
      intro h
      apply hz2
      linear_combination h
    have hA : Wf z - 3 = (z - 1) * (z - 2) / z := by
      unfold Wf
      field_simp
      ring
    have hB : Wf z - 2 = (z ^ 2 - 2 * z + 2) / z := by
      unfold Wf
      field_simp
      ring
    have hY : Yf z = (z - s2) * (z + s2) / z := by
      unfold Yf
      field_simp
      linear_combination s2_sq
    have hzδ : z ^ δ = z ^ α1 * z ^ α2 * z ^ (δ - α1 - α2 - 1) * z := by
      rw [← pow_add, ← pow_add, ← pow_succ]
      congr 1
      omega
    have hN : Nred.eval z = ((z - 1) * (z - 2)) ^ α1 * (z ^ 2 - 2 * z + 2) ^ α2 *
        z ^ (δ - α1 - α2 - 1) := by
      simp [Nred]
    rw [eval_denPoly, Fin.prod_univ_three, hN]
    show ωred z = _ / ((z - pole 0) ^ 0 * (z - pole 1) ^ δ * (z - pole 2) ^ δ)
    rw [pole_one, pole_two, pow_zero, one_mul, sub_neg_eq_add]
    simp only [ωred]
    rw [hA, hB, hY, div_pow, div_pow, div_pow, mul_pow (z - s2) (z + s2) δ, hzδ]
    field_simp
  obtain ⟨rred, hredp, -, -, hreddeg, -, hredev⟩ :=
    exists_rep (Rp p hp) hpole hunit hNredC ![0, δ, δ]
  have hred0 : rred.Q 0 = 0 := by
    have h1 : (rred.Q 0).natDegree ≤ 0 := hreddeg 0
    rw [eq_C_of_natDegree_le_zero h1, hredp 0]
    simp
  have hres := residue_of_primitive rred hredp hGredA.mono cred (fun z hz => by
    obtain ⟨hz0, hz1, hz2⟩ := mem_Udom.1 hz
    have h := hd z hz0 hz1 hz2
    rwa [hωP z, hωeq z hz, ← hredev z hz] at h)
  have hcred0 : cred = 0 := by
    rw [← hres.1, hred0]
    simp
  -- H and η
  obtain ⟨g', hg', hgd⟩ := InA.exists_deriv hpole hg
  let H : ℂ → ℂ := fun z => g z ^ p * Gred z
  let η : ℂ → ℂ := fun z => g z ^ (p - 1) * g' z * Gred z
  have hH : InA (Rp p hp) H := (hg.pow p).mul hGredA
  have hη : InA (Rp p hp) η := ((hg.pow (p - 1)).mul hg').mul hGredA
  obtain ⟨rH, -, hHP, hHQ, hHev⟩ := InA.exists_rep' hpole hunit hH
  obtain ⟨rη, hηp, hηP, hηQ, hηev⟩ := InA.exists_rep' hpole hunit hη
  refine ⟨rH, rη, hHP, hHQ, hηP, hηQ, ?_⟩
  apply Rep.ext_of_eval hr (rH.deriv_proper.sub (hηp.smul _))
  intro z hz
  obtain ⟨hz0, hz1, hz2⟩ := mem_Udom.1 hz
  have hd1 : HasDerivAt H (rH.deriv.eval z) z := by
    refine (rH.hasDerivAt_eval hz).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Udom.mem_nhds hz] with w hw
    exact (hHev w hw).symm
  have hGz : HasDerivAt Gred (ωred z) z := by
    have h := hd z hz0 hz1 hz2
    rw [hωP z, hcred0, zero_div, sub_zero] at h
    exact h
  have hd2 : HasDerivAt H ((p : ℂ) * η z + f534 z ^ n / z) z := by
    have h := ((hgd z hz).pow p).mul hGz
    refine h.congr_deriv ?_
    rw [hfac z hz]
    simp only [η, Pi.pow_apply]
    ring
  have hEq := hd1.unique hd2
  rw [Rep.eval_sub, Rep.eval_smul, hφ z hz, hηev z hz, hEq]
  ring

/-- **Lemma 4.1.** For a removable prime `p` there is a primitive pair `(G, c)` with
`G(1+i) − G(1−i)` `p`-integral. -/
theorem oddPrime_removable (n p : ℕ) (hrem : RemovablePrime n p) :
    ∃ (G : ℂ → ℂ) (c : ℂ), IsPrimPair n G c ∧ PInt p (G (1 + I) - G (1 - I)) := by
  have hp := hrem.1
  have h4n : 4 * n < p ^ 2 := hrem.2.1
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨-, h1, -, h3⟩ := hrem
    have hn : n = 0 := by omega
    subst hn
    simp at h3
  obtain ⟨r, hr, hP, hQ, hPz, hQz, hφ, hpair⟩ := exists_rep_h n p hp hp2
  obtain ⟨rH, rη, hHP, hHQ, hηP, hηQ, hdec⟩ := removable_decomp n p hrem hp2 r hr hφ
  refine ⟨r.primFun, (r.Q 0).coeff 1, hpair, ?_⟩
  have key := PInt_delta_primFun hp hp2 r 1 ?_ ?_
  · simpa using key
  · intro j
    rw [one_mul]
    by_cases hj : j < 4 * n
    · have hc : r.P.coeff j = rH.P.coeff (j + 1) * ((j : ℂ) + 1) - (p : ℂ) * rη.P.coeff j := by
        rw [hdec]
        simp [Rep.sub, Rep.smul, Rep.deriv_P_coeff]
      have hj1 : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      have e : r.P.coeff j / ((j : ℂ) + 1)
          = rH.P.coeff (j + 1) - ((p : ℂ) / ((j + 1 : ℕ) : ℂ)) * rη.P.coeff j := by
        rw [hc]
        push_cast
        field_simp
      rw [e]
      exact PInt.sub hp (hHP.coeff_mem _)
        (PInt.mul hp (PInt_p_div hp (by omega) (by omega)) (hηP.coeff_mem _))
    · rw [hPz j (by omega)]
      simpa using PInt.zero hp
  · intro i k
    rw [one_mul]
    by_cases hk : k < 4 * n
    · have hc : (r.Q i).coeff (k + 2)
          = -((rH.Q i).coeff (k + 1) * ((k : ℂ) + 1)) - (p : ℂ) * (rη.Q i).coeff (k + 2) := by
        rw [hdec]
        simp [Rep.sub, Rep.smul, Rep.deriv_Q_coeff_succ_succ]
      have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      have e : (r.Q i).coeff (k + 2) / ((k : ℂ) + 1)
          = -(rH.Q i).coeff (k + 1) - ((p : ℂ) / ((k + 1 : ℕ) : ℂ)) * (rη.Q i).coeff (k + 2) := by
        rw [hc]
        push_cast
        field_simp
      rw [e]
      exact PInt.sub hp ((hHQ i).coeff_mem _).neg
        (PInt.mul hp (PInt_p_div hp (by omega) (by omega)) ((hηQ i).coeff_mem _))
    · rw [hQz i (k + 2) (by omega)]
      simpa using PInt.zero hp

end PiMeasure
