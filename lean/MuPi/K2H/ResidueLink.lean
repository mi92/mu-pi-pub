import MuPi.K2H.OddPrimes

/-!
# K2H: the residue constant of a primitive pair is `cPS n`

If `(G, c)` is a primitive pair for `f(z)^n/z` (`IsPrimPair n G c`), then `c` equals the power-series
coefficient `cPS n` (the coefficient of `X^{4n}` in `N(X)^n (X^2-2)^{-4n}`).

Proof: over `ℚ`, truncating the power series `N^n/(X^2-2)^{4n}` at order `4n+1` gives
`N^n = (X^2-2)^{4n} T + X^{4n+1} Q` with `T` of degree `≤ 4n` and `T.coeff (4n) = cPS n`.  Hence
`f^n/z = T(z)/z^{4n+1} + Q(z)/(z^2-2)^{4n}`; the first term has an explicit partial-fraction
representation supported at `0`, the second one has one with no principal part at `0`.  Uniqueness of
representations (`Rep.ext_of_eval`) identifies the residue at `0`.
-/

open Polynomial

namespace PiMeasure

namespace ResidueLink

/-- `(X^2-2)^{4n}` over `ℚ` -/
noncomputable def Dq (n : ℕ) : ℚ[X] := (X ^ 2 - 2 : ℚ[X]) ^ (4 * n)

/-- the power series `N^n (X^2-2)^{-4n}` -/
noncomputable def Sps (n : ℕ) : PowerSeries ℚ :=
  ((Npoly ^ n : ℚ[X]) : PowerSeries ℚ) * (((X ^ 2 - 2 : ℚ[X]) ^ (4 * n) : ℚ[X]) : PowerSeries ℚ)⁻¹

/-- its truncation at order `4n+1` -/
noncomputable def Tq (n : ℕ) : ℚ[X] := PowerSeries.trunc (4 * n + 1) (Sps n)

lemma Tq_coeff_top (n : ℕ) : (Tq n).coeff (4 * n) = cPS n := by
  rw [Tq, PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_self _)]
  rfl

lemma Tq_natDegree_lt (n : ℕ) : (Tq n).natDegree < 4 * n + 1 :=
  PowerSeries.natDegree_trunc_lt _ _

lemma Dq_mul_Sps (n : ℕ) :
    ((Dq n : ℚ[X]) : PowerSeries ℚ) * Sps n = ((Npoly ^ n : ℚ[X]) : PowerSeries ℚ) := by
  have h0 : PowerSeries.constantCoeff ((Dq n : ℚ[X]) : PowerSeries ℚ) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, Dq, coeff_zero_eq_eval_zero]
    simp
  rw [Sps, ← Dq, mul_left_comm, PowerSeries.mul_inv_cancel _ h0, mul_one]

lemma X_pow_dvd (n : ℕ) : X ^ (4 * n + 1) ∣ Npoly ^ n - Dq n * Tq n := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  have htr : PowerSeries.trunc (4 * n + 1) (((Dq n * Tq n : ℚ[X]) : PowerSeries ℚ)) =
      PowerSeries.trunc (4 * n + 1) (((Npoly ^ n : ℚ[X]) : PowerSeries ℚ)) := by
    rw [Polynomial.coe_mul, Tq, PowerSeries.trunc_mul_trunc, Dq_mul_Sps]
  have hc := congrArg (fun p : ℚ[X] => p.coeff d) htr
  simp only [PowerSeries.coeff_trunc, if_pos hd, Polynomial.coeff_coe] at hc
  rw [coeff_sub, hc, sub_self]

/-- the quotient `(N^n - D T)/X^{4n+1}` -/
noncomputable def Qq (n : ℕ) : ℚ[X] := (X_pow_dvd n).choose

lemma Npoly_pow_eq (n : ℕ) : Npoly ^ n = Dq n * Tq n + X ^ (4 * n + 1) * Qq n := by
  have h := (X_pow_dvd n).choose_spec
  rw [Qq]
  linear_combination h

/-- `T` over `ℂ` -/
noncomputable def TC (n : ℕ) : ℂ[X] := (Tq n).map (algebraMap ℚ ℂ)

/-- `Q` over `ℂ` -/
noncomputable def QC (n : ℕ) : ℂ[X] := (Qq n).map (algebraMap ℚ ℂ)

lemma TC_natDegree_lt (n : ℕ) : (TC n).natDegree < 4 * n + 1 :=
  lt_of_le_of_lt (natDegree_map_le) (Tq_natDegree_lt n)

lemma TC_coeff_top (n : ℕ) : (TC n).coeff (4 * n) = (cPS n : ℂ) := by
  rw [TC, coeff_map, Tq_coeff_top]
  simp

lemma eval_identity (n : ℕ) (z : ℂ) :
    (((z - 1) * (z - 2)) ^ 5 * (z ^ 2 - 2 * z + 2) ^ 3) ^ n =
      (z ^ 2 - 2) ^ (4 * n) * (TC n).eval z + z ^ (4 * n + 1) * (QC n).eval z := by
  have h := congrArg (fun p : ℚ[X] => (p.map (algebraMap ℚ ℂ)).eval z) (Npoly_pow_eq n)
  simpa [Npoly, Dq, TC, QC] using h

lemma f534_pow_div_eq (n : ℕ) {z : ℂ} (hz0 : z ≠ 0) (hz2 : z ^ 2 - 2 ≠ 0) :
    f534 z ^ n / z = (TC n).eval z / z ^ (4 * n + 1) + (QC n).eval z / (z ^ 2 - 2) ^ (4 * n) := by
  rw [f534, div_pow, eval_identity n z, mul_pow, ← pow_mul, ← pow_mul]
  have hA : z ^ (4 * n) ≠ 0 := pow_ne_zero _ hz0
  have hB : (z ^ 2 - 2) ^ (4 * n) ≠ 0 := pow_ne_zero _ hz2
  rw [pow_succ]
  field_simp
  ring

/-- the principal part at `0` of `T(z)/z^{4n+1}`, as a polynomial in `1/z` -/
noncomputable def Q0 (n : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range (4 * n + 1), C ((TC n).coeff j) * X ^ (4 * n + 1 - j)

lemma Q0_coeff_zero (n : ℕ) : (Q0 n).coeff 0 = 0 := by
  rw [Q0, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]

lemma Q0_coeff_one (n : ℕ) : (Q0 n).coeff 1 = (cPS n : ℂ) := by
  rw [Q0, finsetSum_coeff, Finset.sum_eq_single (4 * n)]
  · rw [coeff_C_mul, coeff_X_pow, if_pos (by omega), mul_one, TC_coeff_top]
  · intro j hj hne
    rw [Finset.mem_range] at hj
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self _)) h

lemma eval_Q0 (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    (Q0 n).eval z⁻¹ = (TC n).eval z / z ^ (4 * n + 1) := by
  rw [Q0, eval_finsetSum, eval_eq_sum_range' (TC_natDegree_lt n), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hsplit : z ^ (4 * n + 1) = z ^ j * z ^ (4 * n + 1 - j) := by
    rw [← pow_add]
    congr 1
    omega
  have hj0 : z ^ j ≠ 0 := pow_ne_zero _ hz
  have hj1 : z ^ (4 * n + 1 - j) ≠ 0 := pow_ne_zero _ hz
  rw [eval_mul, eval_C, eval_pow, eval_X, hsplit, inv_pow]
  field_simp

/-- the representation of `T(z)/z^{4n+1}` -/
noncomputable def r₁ (n : ℕ) : Rep := ⟨0, ![Q0 n, 0, 0]⟩

lemma r₁_proper (n : ℕ) : (r₁ n).Proper := by
  intro i
  fin_cases i <;> simp [r₁, Q0_coeff_zero]

lemma r₁_eval (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    (r₁ n).eval z = (TC n).eval z / z ^ (4 * n + 1) := by
  simp [Rep.eval, r₁, Fin.sum_univ_three, pole_zero, eval_Q0 n hz]

lemma r₁_Q_zero_coeff_one (n : ℕ) : ((r₁ n).Q 0).coeff 1 = (cPS n : ℂ) := by
  simp [r₁, Q0_coeff_one]

end ResidueLink

/-- the residue constant of a primitive pair is the power-series coefficient `cPS n` -/
theorem residue_eq_cPS (n : ℕ) {G : ℂ → ℂ} {c : ℂ} (h : IsPrimPair n G c) : c = (cPS n : ℂ) := by
  -- a representation of `f^n/z` together with its primitive pair (any odd prime works; take `3`)
  obtain ⟨r, hr, -, -, -, -, hev, hprim⟩ := exists_rep_h n 3 Nat.prime_three (by norm_num)
  rw [(primPair_unique h hprim).1]
  -- the representation of `Q(z)/(z^2-2)^{4n}`: no principal part at `0`
  obtain ⟨r₂, hr₂, -, -, hdeg₂, -, hev₂⟩ := exists_rep ⊤ (fun _ => Subring.mem_top _)
    (fun _ _ _ => Subring.mem_top _) (N := ResidueLink.QC n)
    (CoeffIn.of_coeff_mem (fun _ => Subring.mem_top _)) ![0, 4 * n, 4 * n]
  have hr₂0 : r₂.Q 0 = 0 := by
    rw [eq_C_of_natDegree_le_zero (hdeg₂ 0), hr₂ 0, C_0]
  -- uniqueness of representations
  have key : r = (ResidueLink.r₁ n).add r₂ := by
    refine Rep.ext_of_eval hr ((ResidueLink.r₁_proper n).add hr₂) (fun z hz => ?_)
    obtain ⟨hz0, hz1, hz2⟩ := mem_Udom.1 hz
    have hm : z - s2 ≠ 0 := sub_ne_zero.2 hz1
    have hp : z + s2 ≠ 0 := fun h' => hz2 (eq_neg_of_add_eq_zero_left h')
    have hsq : z ^ 2 - 2 ≠ 0 := by
      rw [sq_sub_two]
      exact mul_ne_zero hm hp
    have hden : (denPoly ![0, 4 * n, 4 * n]).eval z = (z ^ 2 - 2) ^ (4 * n) := by
      rw [eval_denPoly, Fin.prod_univ_three, pole_zero, pole_one, pole_two, sq_sub_two]
      simp [mul_pow]
    rw [hev z hz, Rep.eval_add, ResidueLink.r₁_eval n hz0, hev₂ z hz, hden,
      ResidueLink.f534_pow_div_eq n hz0 hsq]
  rw [key]
  show ((ResidueLink.r₁ n).Q 0 + r₂.Q 0).coeff 1 = _
  rw [hr₂0, add_zero, ResidueLink.r₁_Q_zero_coeff_one]

end PiMeasure

#print axioms PiMeasure.residue_eq_cPS
