import MuPi.K2H.Defs

/-!
# K2H, triple `(5,3,4)`: growth of the residue `c_n`

For `c_n = cPS n = [X^{4n}] N(X)^n (X^2-2)^{-4n}` (Lemma 6.1 of `K2H_PROOF.md`) we prove

* `PiMeasure.cPS_pos`      : `0 < c_n`;
* `PiMeasure.cPS_supermul` : `c_m c_n ≤ c_{m+n}`;
* `PiMeasure.cPS_growth`   : there is `r` with `0 < r ≤ 10.540357` and
  `exp ((r - η) n) ≤ c_n ≤ exp ((r + η) n)` for every `η > 0` and all large `n`.

## Route (all helper statements live in the namespace `PiMeasure.Growth`)

1. *Sign flip* (`Growth.cPS_eq`). With `H = (2 - X²)⁻¹`, `Ñ(X) = N(-X) = ((X+1)(X+2))^5 (X²+2X+2)^3`
   and `P̃ = Ñ · H^4` one has `c_n = [X^{4n}] P̃^n` (`PowerSeries.rescale (-1)` realises `X ↦ -X`,
   and only an even coefficient is extracted). All coefficients of `P̃` are nonnegative
   (`Growth.nonnegCoeff_Ptil`; for `H` this follows from `H = 1/2 + (X²/2) H` by strong induction).
2. *Supermultiplicativity and positivity*: one term of a Cauchy product with nonnegative terms
   (`Growth.coeff_mul_ge`), `16 ≤ c_1` (`Growth.cPS_one_ge`; the true value is `7345`) and
   `c_1 ^ n ≤ c_n` (`Growth.cPS_one_pow_le`).
3. *Upper bound* `c_n ≤ 37811 ^ n` (`Growth.cPS_le`). No infinite sums: for a series `F` with
   nonnegative coefficients we bound all partial sums `∑_{k<K} [X^k]F · x^k` (`Growth.BddAt`);
   such bounds are stable under `+`, `*`, `^` (`Growth.psum_mul_le`: the triangle `i + j < K` sits
   inside the square `i, j < K`), and the bound `1/(2 - x²)` for `H` follows from its functional
   equation. At `x₀ = 3913/10000` this gives `c_n x₀^{4n} ≤ P̃(x₀)^n`, and
   `P̃(x₀) / x₀^4 = 37810.9917… ≤ 37811`.
4. *Fekete*: `n ↦ -log c_n` is subadditive and `-log c_n / n ≥ -log 37811`, so
   `Subadditive.tendsto_lim` gives the limit; `r := -lim`.
5. *Numerics* (`Growth.exp_bound`): `37811 ≤ exp 10.540357` from `Real.exp_one_gt_d9` and ten terms
   of the Taylor series of `exp 0.540357`.
-/

namespace PiMeasure.Growth

open scoped Polynomial PowerSeries
open PowerSeries

noncomputable section

/-! ## Step 1: the sign flip -/

/-- The geometric factor `(2 - X²)⁻¹` as a power series over `ℚ`. -/
def Hser : ℚ⟦X⟧ := (2 - X ^ 2)⁻¹

theorem Hser_mul : Hser * (2 - X ^ 2) = 1 := by
  unfold Hser
  refine PowerSeries.inv_mul_cancel _ ?_
  rw [map_sub, map_pow, constantCoeff_X, map_ofNat]
  norm_num

/-- `Ñ(X) = N(-X) = ((X+1)(X+2))^5 (X^2+2X+2)^3` as a power series. -/
def Ntil : ℚ⟦X⟧ := ((X + C 1) * (X + C 2)) ^ 5 * (X ^ 2 + C 2 * X + C 2) ^ 3

/-- `P̃ = Ñ · (2 - X²)^{-4}`: the generating series, with nonnegative coefficients. -/
def Ptil : ℚ⟦X⟧ := Ntil * Hser ^ 4

theorem coe_Npoly :
    ((Npoly : ℚ[X]) : ℚ⟦X⟧) = ((X - 1) * (X - 2)) ^ 5 * (X ^ 2 - 2 * X + 2) ^ 3 := by
  have h : ∀ p : ℚ[X], (p : ℚ⟦X⟧) = Polynomial.coeToPowerSeries.ringHom p := fun _ => rfl
  rw [h, Npoly]
  simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

theorem coe_den : ((Polynomial.X ^ 2 - 2 : ℚ[X]) : ℚ⟦X⟧) = X ^ 2 - 2 := by
  have h : ∀ p : ℚ[X], (p : ℚ⟦X⟧) = Polynomial.coeToPowerSeries.ringHom p := fun _ => rfl
  rw [h]
  simp only [map_pow, map_sub, map_ofNat,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

/-- `N(-X) = Ñ(X)`. -/
theorem rescale_Npoly : rescale (-1 : ℚ) (Npoly : ℚ⟦X⟧) = Ntil := by
  rw [coe_Npoly, Ntil]
  simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, rescale_neg_one_X]
  ring

/-- `H` is even. -/
theorem rescale_Hser : rescale (-1 : ℚ) Hser = Hser := by
  have h := congrArg (rescale (-1 : ℚ)) Hser_mul
  simp only [map_mul, map_pow, map_sub, map_one, map_ofNat, rescale_neg_one_X, neg_sq] at h
  calc rescale (-1 : ℚ) Hser = rescale (-1 : ℚ) Hser * (Hser * (2 - X ^ 2)) := by
        rw [Hser_mul, mul_one]
    _ = Hser * (rescale (-1 : ℚ) Hser * (2 - X ^ 2)) := by ring
    _ = Hser := by rw [h, mul_one]

/-- The sign flip: `c_n` is the coefficient of `X^{4n}` in `P̃^n`. -/
theorem cPS_eq (n : ℕ) : cPS n = coeff (4 * n) (Ptil ^ n) := by
  have hcc : constantCoeff (((Polynomial.X ^ 2 - 2 : ℚ[X]) ^ (4 * n) : ℚ[X]) : ℚ⟦X⟧) ≠ 0 := by
    rw [Polynomial.coe_pow, coe_den, map_pow, map_sub, map_pow, constantCoeff_X, map_ofNat]
    norm_num
  have h1 : ((Npoly ^ n : ℚ[X]) : ℚ⟦X⟧) *
      (((Polynomial.X ^ 2 - 2 : ℚ[X]) ^ (4 * n) : ℚ[X]) : ℚ⟦X⟧)⁻¹
        = ((Npoly : ℚ⟦X⟧) * Hser ^ 4) ^ n := by
    symm
    rw [PowerSeries.eq_mul_inv_iff_mul_eq hcc, Polynomial.coe_pow, Polynomial.coe_pow, coe_den,
      pow_mul, ← mul_pow]
    have h2 : (Npoly : ℚ⟦X⟧) * Hser ^ 4 * (X ^ 2 - 2) ^ 4
        = (Npoly : ℚ⟦X⟧) * (Hser * (2 - X ^ 2)) ^ 4 := by ring
    rw [h2, Hser_mul, one_pow, mul_one]
  have h3 : rescale (-1 : ℚ) (((Npoly : ℚ⟦X⟧) * Hser ^ 4) ^ n) = Ptil ^ n := by
    rw [map_pow, map_mul, map_pow, rescale_Npoly, rescale_Hser, Ptil]
  have h4 : (-1 : ℚ) ^ (4 * n) = 1 := by
    rw [pow_mul]
    norm_num
  rw [cPS, h1, ← h3, coeff_rescale, h4, one_mul]

/-! ## Step 2: nonnegative coefficients, supermultiplicativity, positivity -/

/-- All coefficients of the power series are nonnegative. -/
def NonnegCoeff (F : ℚ⟦X⟧) : Prop := ∀ k, 0 ≤ coeff k F

theorem NonnegCoeff.add {F G : ℚ⟦X⟧} (hF : NonnegCoeff F) (hG : NonnegCoeff G) :
    NonnegCoeff (F + G) := by
  intro k
  rw [map_add]
  exact add_nonneg (hF k) (hG k)

theorem NonnegCoeff.mul {F G : ℚ⟦X⟧} (hF : NonnegCoeff F) (hG : NonnegCoeff G) :
    NonnegCoeff (F * G) := by
  intro k
  rw [coeff_mul]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hF _) (hG _)

theorem nonnegCoeff_C {c : ℚ} (hc : 0 ≤ c) : NonnegCoeff (C c) := by
  intro k
  rw [coeff_C]
  split_ifs
  · exact hc
  · exact le_rfl

theorem nonnegCoeff_one : NonnegCoeff 1 := by
  have h := nonnegCoeff_C (c := 1) zero_le_one
  rwa [map_one] at h

theorem nonnegCoeff_X : NonnegCoeff X := by
  intro k
  rw [coeff_X]
  split_ifs <;> norm_num

theorem NonnegCoeff.pow {F : ℚ⟦X⟧} (hF : NonnegCoeff F) (n : ℕ) : NonnegCoeff (F ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact nonnegCoeff_one
  | succ n ih => rw [pow_succ]; exact ih.mul hF

/-- One term of the Cauchy product is a lower bound for a coefficient of the product. -/
theorem coeff_mul_ge {F G : ℚ⟦X⟧} (hF : NonnegCoeff F) (hG : NonnegCoeff G) (a b : ℕ) :
    coeff a F * coeff b G ≤ coeff (a + b) (F * G) := by
  rw [coeff_mul]
  exact Finset.single_le_sum (f := fun p : ℕ × ℕ => coeff p.1 F * coeff p.2 G)
    (fun p _ => mul_nonneg (hF _) (hG _))
    (Finset.mem_antidiagonal.2 rfl : (a, b) ∈ Finset.antidiagonal (a + b))

theorem coeff_pow_ge {F : ℚ⟦X⟧} (hF : NonnegCoeff F) (a n : ℕ) :
    coeff a F ^ n ≤ coeff (a * n) (F ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Nat.mul_zero, coeff_zero_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, Nat.mul_succ]
    exact (mul_le_mul_of_nonneg_right ih (hF a)).trans (coeff_mul_ge (hF.pow n) hF _ _)

/-- The functional equation `H = 1/2 + (X²/2) H`. -/
theorem Hser_rec : Hser = C (1 / 2 : ℚ) + C (1 / 2 : ℚ) * X ^ 2 * Hser := by
  have hc : (C (1 / 2 : ℚ) : ℚ⟦X⟧) * 2 = 1 := by
    rw [← map_ofNat (C (R := ℚ)) 2, ← map_mul]
    norm_num
  linear_combination (C (1 / 2 : ℚ)) * Hser_mul - Hser * hc

theorem coeff_Hser (n : ℕ) : coeff n Hser
    = 1 / 2 * ((if n = 0 then 1 else 0) + (if 2 ≤ n then coeff (n - 2) Hser else 0)) := by
  conv_lhs => rw [Hser_rec]
  rw [map_add, mul_assoc, coeff_C_mul, coeff_C, coeff_X_pow_mul']
  split_ifs <;> ring

theorem nonnegCoeff_Hser : NonnegCoeff Hser := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [coeff_Hser]
    have h1 : (0 : ℚ) ≤ if n = 0 then 1 else 0 := by split_ifs <;> norm_num
    have h2 : (0 : ℚ) ≤ if 2 ≤ n then coeff (n - 2) Hser else 0 := by
      split_ifs with h
      · exact ih _ (by omega)
      · exact le_rfl
    exact mul_nonneg (by norm_num) (add_nonneg h1 h2)

theorem nonnegCoeff_Ntil : NonnegCoeff Ntil := by
  have h1 : NonnegCoeff (C (1 : ℚ)) := nonnegCoeff_C (by norm_num)
  have h2 : NonnegCoeff (C (2 : ℚ)) := nonnegCoeff_C (by norm_num)
  exact (((nonnegCoeff_X.add h1).mul (nonnegCoeff_X.add h2)).pow 5).mul
    ((((nonnegCoeff_X.pow 2).add (h2.mul nonnegCoeff_X)).add h2).pow 3)

theorem nonnegCoeff_Ptil : NonnegCoeff Ptil := nonnegCoeff_Ntil.mul (nonnegCoeff_Hser.pow 4)

/-- A crude lower bound for `c_1` (the true value is `7345`): the term `[X^4](X+1)^4 · R(0)` of
`P̃ = (X+1)^4 · R`. -/
theorem cPS_one_ge : 16 ≤ cPS 1 := by
  have hR : Ptil = (X + C 1) ^ 4 *
      ((X + C 1) * (X + C 2) ^ 5 * (X ^ 2 + C 2 * X + C 2) ^ 3 * Hser ^ 4) := by
    rw [Ptil, Ntil]
    ring
  have h1 : NonnegCoeff (C (1 : ℚ)) := nonnegCoeff_C (by norm_num)
  have h2 : NonnegCoeff (C (2 : ℚ)) := nonnegCoeff_C (by norm_num)
  have hA : NonnegCoeff (X + C (1 : ℚ)) := nonnegCoeff_X.add h1
  have hB : NonnegCoeff ((X + C 1) * (X + C 2) ^ 5 * (X ^ 2 + C 2 * X + C 2) ^ 3 * Hser ^ 4) :=
    ((hA.mul ((nonnegCoeff_X.add h2).pow 5)).mul
      ((((nonnegCoeff_X.pow 2).add (h2.mul nonnegCoeff_X)).add h2).pow 3)).mul
      (nonnegCoeff_Hser.pow 4)
  have h3 : coeff 1 (X + C (1 : ℚ)) = 1 := by
    rw [map_add, coeff_one_X, coeff_C]
    norm_num
  have h4 : coeff 0 ((X + C 1) * (X + C 2) ^ 5 * (X ^ 2 + C 2 * X + C 2) ^ 3 * Hser ^ 4)
      = (16 : ℚ) := by
    rw [coeff_zero_eq_constantCoeff_apply]
    simp only [map_mul, map_pow, map_add, constantCoeff_X, constantCoeff_C, Hser,
      constantCoeff_inv, map_sub, map_ofNat]
    norm_num
  have h5 : (1 : ℚ) ≤ coeff (1 * 4) ((X + C (1 : ℚ)) ^ 4) := by
    have h := coeff_pow_ge hA 1 4
    rwa [h3, one_pow] at h
  have h6 := coeff_mul_ge (hA.pow 4) hB (1 * 4) 0
  rw [h4] at h6
  rw [cPS_eq, pow_one, hR]
  exact le_trans (by linarith) h6

theorem cPS_one_pow_le (n : ℕ) : cPS 1 ^ n ≤ cPS n := by
  rw [cPS_eq n, cPS_eq 1, pow_one, mul_one]
  exact coeff_pow_ge nonnegCoeff_Ptil 4 n

/-! ## Step 3: the upper bound `cPS n ≤ 37811 ^ n` -/

/-- Partial sums of the series `F` evaluated at `x`. -/
def psum (F : ℚ⟦X⟧) (x : ℚ) (K : ℕ) : ℚ := ∑ k ∈ Finset.range K, coeff k F * x ^ k

theorem psum_nonneg {F : ℚ⟦X⟧} (hF : NonnegCoeff F) {x : ℚ} (hx : 0 ≤ x) (K : ℕ) :
    0 ≤ psum F x K :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hF k) (pow_nonneg hx k)

theorem psum_add (F G : ℚ⟦X⟧) (x : ℚ) (K : ℕ) :
    psum (F + G) x K = psum F x K + psum G x K := by
  simp only [psum, map_add, add_mul, Finset.sum_add_distrib]

/-- The triangle `i + j < K` is contained in the square `i, j < K`. -/
theorem sum_antidiagonal_le (f g : ℕ → ℚ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) (K : ℕ) :
    ∑ k ∈ Finset.range K, ∑ p ∈ Finset.antidiagonal k, f p.1 * g p.2
      ≤ (∑ i ∈ Finset.range K, f i) * (∑ j ∈ Finset.range K, g j) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have key : ∀ k ∈ Finset.range K, Finset.antidiagonal k
      = (Finset.range K ×ˢ Finset.range K).filter (fun p => p.1 + p.2 = k) := by
    intro k hk
    ext p
    simp only [Finset.mem_antidiagonal, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hk ⊢
    omega
  rw [Finset.sum_congr rfl (fun k hk => by rw [key k hk])]
  exact Finset.sum_fiberwise_le_sum_of_sum_fiber_nonneg
    (fun y _ => Finset.sum_nonneg fun p _ => mul_nonneg (hf _) (hg _))

/-- Partial sums of a product are at most the product of the partial sums (nonnegative
coefficients, `x ≥ 0`). -/
theorem psum_mul_le {F G : ℚ⟦X⟧} (hF : NonnegCoeff F) (hG : NonnegCoeff G) {x : ℚ}
    (hx : 0 ≤ x) (K : ℕ) : psum (F * G) x K ≤ psum F x K * psum G x K := by
  have h1 : ∀ k, coeff k (F * G) * x ^ k
      = ∑ p ∈ Finset.antidiagonal k, (coeff p.1 F * x ^ p.1) * (coeff p.2 G * x ^ p.2) := by
    intro k
    rw [coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.mem_antidiagonal.1 hp, pow_add]
    ring
  unfold psum
  simp_rw [h1]
  exact sum_antidiagonal_le (fun i => coeff i F * x ^ i) (fun i => coeff i G * x ^ i)
    (fun i => mul_nonneg (hF i) (pow_nonneg hx i)) (fun i => mul_nonneg (hG i) (pow_nonneg hx i)) K

/-- `F` has nonnegative coefficients and all partial sums of `F(x)` are at most `B`. -/
structure BddAt (F : ℚ⟦X⟧) (x B : ℚ) : Prop where
  nonneg : NonnegCoeff F
  le : ∀ K, psum F x K ≤ B

theorem BddAt.add {F G : ℚ⟦X⟧} {x a b : ℚ} (hF : BddAt F x a) (hG : BddAt G x b) :
    BddAt (F + G) x (a + b) :=
  ⟨hF.nonneg.add hG.nonneg, fun K => by rw [psum_add]; exact add_le_add (hF.le K) (hG.le K)⟩

theorem BddAt.mul {F G : ℚ⟦X⟧} {x a b : ℚ} (hx : 0 ≤ x) (hF : BddAt F x a) (hG : BddAt G x b) :
    BddAt (F * G) x (a * b) :=
  ⟨hF.nonneg.mul hG.nonneg, fun K => (psum_mul_le hF.nonneg hG.nonneg hx K).trans
    (mul_le_mul (hF.le K) (hG.le K) (psum_nonneg hG.nonneg hx K)
      ((psum_nonneg hF.nonneg hx K).trans (hF.le K)))⟩

theorem bddAt_C {c : ℚ} (hc : 0 ≤ c) (x : ℚ) : BddAt (C c) x c := by
  refine ⟨nonnegCoeff_C hc, fun K => ?_⟩
  unfold psum
  simp only [coeff_C, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs <;> simp [hc]

theorem bddAt_one (x : ℚ) : BddAt 1 x 1 := by
  have h := bddAt_C (c := 1) zero_le_one x
  rwa [map_one] at h

theorem bddAt_X {x : ℚ} (hx : 0 ≤ x) : BddAt X x x := by
  refine ⟨nonnegCoeff_X, fun K => ?_⟩
  unfold psum
  simp only [coeff_X, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs <;> simp [hx]

theorem BddAt.pow {F : ℚ⟦X⟧} {x a : ℚ} (hx : 0 ≤ x) (hF : BddAt F x a) (n : ℕ) :
    BddAt (F ^ n) x (a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact bddAt_one x
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hx hF

/-- A single term is at most the bound for the partial sums. -/
theorem BddAt.coeff_le {F : ℚ⟦X⟧} {x a : ℚ} (hx : 0 ≤ x) (hF : BddAt F x a) (k : ℕ) :
    coeff k F * x ^ k ≤ a := by
  refine le_trans ?_ (hF.le (k + 1))
  unfold psum
  exact Finset.single_le_sum (f := fun i => coeff i F * x ^ i)
    (fun i _ => mul_nonneg (hF.nonneg i) (pow_nonneg hx i)) (Finset.self_mem_range_succ k)

/-- `H(x) ≤ 1/(2 - x²)` for `0 ≤ x < √2`, from `H = 1/2 + (X²/2) H`. -/
theorem bddAt_Hser {x : ℚ} (hx : 0 ≤ x) (hx2 : x ^ 2 < 2) : BddAt Hser x (1 / (2 - x ^ 2)) := by
  refine ⟨nonnegCoeff_Hser, fun K => ?_⟩
  have hψ : BddAt (C (1 / 2 : ℚ) * X ^ 2) x (1 / 2 * x ^ 2) :=
    (bddAt_C (by norm_num) x).mul hx ((bddAt_X hx).pow hx 2)
  have h1 : psum Hser x K
      = psum (C (1 / 2 : ℚ)) x K + psum (C (1 / 2 : ℚ) * X ^ 2 * Hser) x K := by
    conv_lhs => rw [Hser_rec]
    rw [psum_add]
  have h2 := (bddAt_C (c := 1 / 2) (by norm_num) x).le K
  have h3 := psum_mul_le hψ.nonneg nonnegCoeff_Hser hx K
  have h4 := hψ.le K
  have h5 := psum_nonneg nonnegCoeff_Hser hx K
  have h6 : psum (C (1 / 2 : ℚ) * X ^ 2) x K * psum Hser x K ≤ 1 / 2 * x ^ 2 * psum Hser x K :=
    mul_le_mul_of_nonneg_right h4 h5
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem bddAt_Ptil {x : ℚ} (hx : 0 ≤ x) (hx2 : x ^ 2 < 2) :
    BddAt Ptil x (((x + 1) * (x + 2)) ^ 5 * (x ^ 2 + 2 * x + 2) ^ 3 * (1 / (2 - x ^ 2)) ^ 4) := by
  have h1 : BddAt (C (1 : ℚ)) x 1 := bddAt_C (by norm_num) x
  have h2 : BddAt (C (2 : ℚ)) x 2 := bddAt_C (by norm_num) x
  have hX := bddAt_X hx
  exact ((((hX.add h1).mul hx (hX.add h2)).pow hx 5).mul hx
    ((((hX.pow hx 2).add (h2.mul hx hX)).add h2).pow hx 3)).mul hx ((bddAt_Hser hx hx2).pow hx 4)

/-- `c_n ≤ Λ^n` with `Λ = P̃(x₀)/x₀^4 = 37810.9917… ≤ 37811`, `x₀ = 3913/10000`. -/
theorem cPS_le (n : ℕ) : cPS n ≤ 37811 ^ n := by
  have hx : (0 : ℚ) ≤ 3913 / 10000 := by norm_num
  have hx2 : (3913 / 10000 : ℚ) ^ 2 < 2 := by norm_num
  have h := ((bddAt_Ptil hx hx2).pow hx n).coeff_le hx (4 * n)
  rw [← cPS_eq] at h
  have hB : ((((3913 / 10000 : ℚ) + 1) * (3913 / 10000 + 2)) ^ 5
      * ((3913 / 10000) ^ 2 + 2 * (3913 / 10000) + 2) ^ 3
      * (1 / (2 - (3913 / 10000) ^ 2)) ^ 4) ≤ 37811 * (3913 / 10000) ^ 4 := by
    norm_num
  have hpos : (0 : ℚ) < ((3913 / 10000 : ℚ) ^ 4) ^ n := by positivity
  have h' : cPS n * ((3913 / 10000 : ℚ) ^ 4) ^ n ≤ 37811 ^ n * ((3913 / 10000 : ℚ) ^ 4) ^ n := by
    rw [← mul_pow, ← pow_mul]
    exact h.trans (pow_le_pow_left₀ (by positivity) hB n)
  exact le_of_mul_le_mul_right h' hpos

/-! ## Step 5 (numerics): `37811 ≤ exp 10.540357` -/

theorem exp_bound : (37811 : ℝ) ≤ Real.exp 10.540357 := by
  have h1 : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have h2 : ∑ i ∈ Finset.range 10, (0.540357 : ℝ) ^ i / (i.factorial : ℝ) ≤ Real.exp 0.540357 :=
    Real.sum_le_exp_of_nonneg (by norm_num) 10
  have h3 : Real.exp 10.540357 = Real.exp 1 ^ 10 * Real.exp 0.540357 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  have h4 : (37811 : ℝ)
      ≤ 2.7182818283 ^ 10 * ∑ i ∈ Finset.range 10, (0.540357 : ℝ) ^ i / (i.factorial : ℝ) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  rw [h3]
  refine h4.trans (mul_le_mul (pow_le_pow_left₀ (by norm_num) h1 10) h2 ?_ (by positivity))
  exact Finset.sum_nonneg fun i _ => by positivity

end

end PiMeasure.Growth

/-! ## The three main statements -/

open Polynomial

namespace PiMeasure

theorem cPS_pos (n : ℕ) : 0 < cPS n :=
  lt_of_lt_of_le (pow_pos (lt_of_lt_of_le (by norm_num) Growth.cPS_one_ge) n)
    (Growth.cPS_one_pow_le n)

theorem cPS_supermul (m n : ℕ) : cPS m * cPS n ≤ cPS (m + n) := by
  rw [Growth.cPS_eq, Growth.cPS_eq, Growth.cPS_eq, pow_add, mul_add]
  exact Growth.coeff_mul_ge (Growth.nonnegCoeff_Ptil.pow m) (Growth.nonnegCoeff_Ptil.pow n)
    (4 * m) (4 * n)

/-- Step 4 (Fekete): `c_n = exp ((r + o(1)) n)` with `0 < r ≤ 10.540357`. -/
theorem cPS_growth : ∃ r : ℝ, 0 < r ∧ r ≤ 10.540357 ∧ ∀ η : ℝ, 0 < η → ∃ n₁ : ℕ, ∀ n, n₁ ≤ n →
    Real.exp ((r - η) * n) ≤ (cPS n : ℝ) ∧ (cPS n : ℝ) ≤ Real.exp ((r + η) * n) := by
  have hpos : ∀ n, (0 : ℝ) < (cPS n : ℝ) := fun n => by exact_mod_cast cPS_pos n
  -- `n ↦ -log c_n` is subadditive
  have hsub : Subadditive (fun n => -Real.log (cPS n : ℝ)) := by
    intro m n
    have h' : (cPS m : ℝ) * (cPS n : ℝ) ≤ (cPS (m + n) : ℝ) := by
      exact_mod_cast cPS_supermul m n
    have h := Real.log_le_log (mul_pos (hpos m) (hpos n)) h'
    rw [Real.log_mul (hpos m).ne' (hpos n).ne'] at h
    change -Real.log (cPS (m + n) : ℝ) ≤ -Real.log (cPS m : ℝ) + -Real.log (cPS n : ℝ)
    linarith
  -- upper bound `log c_n ≤ n log 37811`
  have hupper : ∀ n : ℕ, Real.log (cPS n : ℝ) ≤ n * Real.log 37811 := by
    intro n
    have h : (cPS n : ℝ) ≤ (37811 : ℝ) ^ n := by exact_mod_cast Growth.cPS_le n
    have h' := Real.log_le_log (hpos n) h
    rwa [Real.log_pow] at h'
  have hlog : (0 : ℝ) ≤ Real.log 37811 := Real.log_nonneg (by norm_num)
  have hlower : ∀ n : ℕ, -Real.log 37811 ≤ -Real.log (cPS n : ℝ) / n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hlog
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [le_div_iff₀ hn']
      have := hupper n
      linarith
  have hbdd : BddBelow (Set.range fun n : ℕ => -Real.log (cPS n : ℝ) / n) := by
    refine ⟨-Real.log 37811, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hlower n
  -- Fekete's lemma
  have hlim := hsub.tendsto_lim hbdd
  refine ⟨-hsub.lim, ?_, ?_, ?_⟩
  · -- positivity of the rate: `r ≥ log c_1 ≥ log 16 > 0`
    have h1 := hsub.lim_le_div hbdd (n := 1) one_ne_zero
    have h16 : (16 : ℝ) ≤ (cPS 1 : ℝ) := by exact_mod_cast Growth.cPS_one_ge
    have h2 : 0 < Real.log (cPS 1 : ℝ) := Real.log_pos (by linarith)
    simp only [Nat.cast_one, div_one] at h1
    linarith
  · -- `r ≤ log 37811 ≤ 10.540357`
    have h1 : -Real.log 37811 ≤ hsub.lim := ge_of_tendsto' hlim hlower
    have h2 : Real.log 37811 ≤ 10.540357 :=
      (Real.log_le_iff_le_exp (by norm_num)).2 Growth.exp_bound
    linarith
  · intro η hη
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim η hη
    refine ⟨max N 1, fun n hn => ?_⟩
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
    have hd := hN n hnN
    rw [Real.dist_eq, abs_lt] at hd
    obtain ⟨hd1, hd2⟩ := hd
    have e3 : -Real.log (cPS n : ℝ) / n < hsub.lim + η := by linarith
    have e4 : hsub.lim - η < -Real.log (cPS n : ℝ) / n := by linarith
    rw [div_lt_iff₀ hn'] at e3
    rw [lt_div_iff₀ hn'] at e4
    constructor
    · exact (Real.exp_le_exp.2 (by linarith)).trans_eq (Real.exp_log (hpos n))
    · exact (Real.exp_log (hpos n)).symm.le.trans (Real.exp_le_exp.2 (by linarith))

end PiMeasure

#print axioms PiMeasure.cPS_pos
#print axioms PiMeasure.cPS_supermul
#print axioms PiMeasure.cPS_growth
