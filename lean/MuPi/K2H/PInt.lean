import MuPi.K2H.Defs

/-!
# `p`-integers of `ℂ` and the `√2`-adic filtration

`PInt p x` : some multiple `N • x` with `p ∤ N` is an algebraic integer (so `x` is integral at every
place above `p`).  For a rational number this means that `p` does not divide the denominator, and a
rational number that is `p`-integral for every prime `p` is an integer.

`V2 k x` : `x = √2^k · y` with `y` a 2-integer, i.e. "`v₂(x) ≥ k/2`".
-/

namespace PiMeasure

open Complex

/-- `√2` as a complex number. -/
noncomputable def s2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

lemma s2_sq : s2 ^ 2 = 2 := by
  unfold s2
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma s2_ne_zero : s2 ≠ 0 := by
  intro h
  have := s2_sq
  rw [h] at this
  norm_num at this

/-- `ε = √2 - 1`, a unit: `ε (√2 + 1) = 1`. -/
noncomputable def eps : ℂ := s2 - 1

lemma eps_mul : eps * (s2 + 1) = 1 := by
  unfold eps
  linear_combination s2_sq

lemma eps_ne_zero : eps ≠ 0 := by
  intro h
  have := eps_mul
  rw [h, zero_mul] at this
  exact zero_ne_one this

lemma eps_inv : eps⁻¹ = s2 + 1 := inv_eq_of_mul_eq_one_right eps_mul

/-- `c = 1 + ε² = 2√2·ε`. -/
noncomputable def cc : ℂ := 1 + eps ^ 2

lemma cc_eq : cc = s2 ^ 3 * eps := by
  unfold cc eps
  linear_combination (-s2 ^ 2 + s2 - 1) * s2_sq

lemma cc_ne_zero : cc ≠ 0 := by
  rw [cc_eq]
  exact mul_ne_zero (pow_ne_zero _ s2_ne_zero) eps_ne_zero

lemma isIntegral_natCast' (N : ℕ) : IsIntegral ℤ (N : ℂ) := by
  have : (N : ℂ) = algebraMap ℤ ℂ (N : ℤ) := by simp
  rw [this]
  exact isIntegral_algebraMap

lemma isIntegral_intCast' (k : ℤ) : IsIntegral ℤ (k : ℂ) := by
  have : (k : ℂ) = algebraMap ℤ ℂ k := by simp
  rw [this]
  exact isIntegral_algebraMap

lemma s2_isIntegral : IsIntegral ℤ s2 := by
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  rw [s2_sq]
  exact_mod_cast isIntegral_natCast' 2

lemma I_isIntegral : IsIntegral ℤ Complex.I := by
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  rw [Complex.I_sq]
  exact_mod_cast isIntegral_intCast' (-1)

/-- `x ∈ ℂ` is `p`-integral: a multiple `N x`, `N` prime to `p`, is an algebraic integer. -/
def PInt (p : ℕ) (x : ℂ) : Prop := ∃ N : ℕ, ¬ p ∣ N ∧ IsIntegral ℤ ((N : ℂ) * x)

namespace PInt

variable {p : ℕ}

lemma of_isIntegral (hp : p.Prime) {x : ℂ} (h : IsIntegral ℤ x) : PInt p x :=
  ⟨1, hp.not_dvd_one, by simpa using h⟩

lemma zero (hp : p.Prime) : PInt p 0 := of_isIntegral hp isIntegral_zero

lemma one (hp : p.Prime) : PInt p 1 := of_isIntegral hp isIntegral_one

lemma intCast (hp : p.Prime) (k : ℤ) : PInt p (k : ℂ) := of_isIntegral hp (isIntegral_intCast' k)

lemma natCast (hp : p.Prime) (k : ℕ) : PInt p (k : ℂ) := of_isIntegral hp (isIntegral_natCast' k)

lemma add (hp : p.Prime) {x y : ℂ} (hx : PInt p x) (hy : PInt p y) : PInt p (x + y) := by
  obtain ⟨N, hN, hxN⟩ := hx
  obtain ⟨M, hM, hyM⟩ := hy
  refine ⟨N * M, fun h => (hp.dvd_mul.1 h).elim hN hM, ?_⟩
  have e : ((N * M : ℕ) : ℂ) * (x + y) = (M : ℂ) * ((N : ℂ) * x) + (N : ℂ) * ((M : ℂ) * y) := by
    push_cast; ring
  rw [e]
  exact ((isIntegral_natCast' M).mul hxN).add ((isIntegral_natCast' N).mul hyM)

lemma mul (hp : p.Prime) {x y : ℂ} (hx : PInt p x) (hy : PInt p y) : PInt p (x * y) := by
  obtain ⟨N, hN, hxN⟩ := hx
  obtain ⟨M, hM, hyM⟩ := hy
  refine ⟨N * M, fun h => (hp.dvd_mul.1 h).elim hN hM, ?_⟩
  have e : ((N * M : ℕ) : ℂ) * (x * y) = ((N : ℂ) * x) * ((M : ℂ) * y) := by push_cast; ring
  rw [e]
  exact hxN.mul hyM

lemma neg {x : ℂ} (hx : PInt p x) : PInt p (-x) := by
  obtain ⟨N, hN, hxN⟩ := hx
  exact ⟨N, hN, by rw [mul_neg]; exact hxN.neg⟩

lemma sub (hp : p.Prime) {x y : ℂ} (hx : PInt p x) (hy : PInt p y) : PInt p (x - y) := by
  rw [sub_eq_add_neg]
  exact add hp hx hy.neg

lemma pow (hp : p.Prime) {x : ℂ} (hx : PInt p x) (k : ℕ) : PInt p (x ^ k) := by
  induction k with
  | zero => simpa using one hp
  | succ k ih => rw [pow_succ]; exact mul hp ih hx

lemma sum (hp : p.Prime) {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, PInt p (f i)) :
    PInt p (∑ i ∈ s, f i) :=
  Finset.sum_induction f (PInt p) (fun _ _ => add hp) (zero hp) h

lemma prod (hp : p.Prime) {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, PInt p (f i)) :
    PInt p (∏ i ∈ s, f i) :=
  Finset.prod_induction f (PInt p) (fun _ _ => mul hp) (one hp) h

/-- `1/N` is `p`-integral when `p ∤ N`. -/
lemma inv_natCast {N : ℕ} (hN : ¬ p ∣ N) : PInt p ((N : ℂ)⁻¹) := by
  have hN0 : (N : ℂ) ≠ 0 := by
    intro h
    apply hN
    have : N = 0 := by exact_mod_cast h
    rw [this]
    exact dvd_zero p
  exact ⟨N, hN, by rw [mul_inv_cancel₀ hN0]; exact isIntegral_one⟩

/-- `1/k` is `p`-integral when `p ∤ k` (`k` an integer). -/
lemma inv_intCast {k : ℤ} (hk : ¬ (p : ℤ) ∣ k) : PInt p ((k : ℂ)⁻¹) := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hk (dvd_zero _)
  have hN : ¬ p ∣ k.natAbs := fun h => hk (Int.natCast_dvd.2 h)
  rcases Int.natAbs_eq k with h | h
  · have hc : (k : ℂ) = ((k.natAbs : ℕ) : ℂ) :=
      (congrArg (Int.cast : ℤ → ℂ) h).trans (Int.cast_natCast _)
    rw [hc]
    exact inv_natCast hN
  · have hc : (k : ℂ) = -((k.natAbs : ℕ) : ℂ) := by
      have := congrArg (Int.cast : ℤ → ℂ) h
      rw [this, Int.cast_neg, Int.cast_natCast]
    rw [hc, inv_neg]
    exact (inv_natCast hN).neg

/-- A rational `p`-integer of `ℂ` has denominator prime to `p`. -/
lemma not_dvd_den {x : ℚ} (h : PInt p (x : ℂ)) : ¬ p ∣ x.den := by
  obtain ⟨N, hN, hint⟩ := h
  have h1 : IsIntegral ℤ ((N : ℚ) * x) := by
    have e : ((N : ℂ) * (x : ℂ)) = algebraMap ℚ ℂ ((N : ℚ) * x) := by simp
    rw [e] at hint
    exact (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).1 hint
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  have hN0 : (N : ℚ) ≠ 0 := by
    intro h0
    apply hN
    have : N = 0 := by exact_mod_cast h0
    rw [this]
    exact dvd_zero p
  have hx : x = (k : ℚ) / ((N : ℤ) : ℚ) := by
    rw [eq_div_iff (by exact_mod_cast hN0)]
    have : (algebraMap ℤ ℚ) k = (k : ℚ) := by simp
    rw [← this, hk]
    push_cast
    ring
  have hden : (x.den : ℤ) ∣ (N : ℤ) := by
    have := Rat.den_dvd k (N : ℤ)
    rwa [Rat.divInt_eq_div, ← hx] at this
  intro hp
  exact hN (hp.trans (Int.natCast_dvd_natCast.1 hden))

end PInt

/-- A rational number that is `p`-integral at every prime `p` is an integer. -/
theorem exists_int_of_forall_PInt {x : ℚ} (h : ∀ p : ℕ, p.Prime → PInt p (x : ℂ)) :
    ∃ k : ℤ, x = k := by
  have hden : x.den = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    exact PInt.not_dvd_den (h p hp) hpd
  exact ⟨x.num, ((Rat.den_eq_one_iff x).1 hden).symm⟩

/-! ## The `√2`-adic filtration at the prime 2 -/

/-- `x` is divisible by `√2^k` in the ring of 2-integers (`k ∈ ℤ`): "`v₂(x) ≥ k/2`". -/
def V2 (k : ℤ) (x : ℂ) : Prop := ∃ y : ℂ, PInt 2 y ∧ x = s2 ^ k * y

namespace V2

lemma of_PInt {x : ℂ} (h : PInt 2 x) : V2 0 x := ⟨x, h, by simp⟩

lemma to_PInt {x : ℂ} (h : V2 0 x) : PInt 2 x := by
  obtain ⟨y, hy, rfl⟩ := h
  simpa using hy

lemma zero (k : ℤ) : V2 k 0 := ⟨0, PInt.zero Nat.prime_two, by simp⟩

lemma mul {j k : ℤ} {x y : ℂ} (hx : V2 j x) (hy : V2 k y) : V2 (j + k) (x * y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a * b, PInt.mul Nat.prime_two ha hb, by rw [zpow_add₀ s2_ne_zero]; ring⟩

lemma add {k : ℤ} {x y : ℂ} (hx : V2 k x) (hy : V2 k y) : V2 k (x + y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a + b, PInt.add Nat.prime_two ha hb, by ring⟩

lemma neg {k : ℤ} {x : ℂ} (hx : V2 k x) : V2 k (-x) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨-a, ha.neg, by ring⟩

lemma sub {k : ℤ} {x y : ℂ} (hx : V2 k x) (hy : V2 k y) : V2 k (x - y) := by
  rw [sub_eq_add_neg]
  exact add hx hy.neg

lemma mono {j k : ℤ} {x : ℂ} (hx : V2 k x) (hjk : j ≤ k) : V2 j x := by
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨s2 ^ (k - j).toNat * a,
    PInt.mul Nat.prime_two
      (PInt.pow Nat.prime_two (PInt.of_isIntegral Nat.prime_two s2_isIntegral) _) ha, ?_⟩
  have hk : k = j + ((k - j).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  conv_lhs => rw [hk, zpow_add₀ s2_ne_zero, zpow_natCast]
  ring

lemma sum {ι : Type*} {k : ℤ} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, V2 k (f i)) :
    V2 k (∑ i ∈ s, f i) :=
  Finset.sum_induction f (V2 k) (fun _ _ => add) (zero k) h

/-- multiplication by a 2-integer keeps the level -/
lemma mul_PInt {k : ℤ} {x y : ℂ} (hx : V2 k x) (hy : PInt 2 y) : V2 k (x * y) := by
  have := mul hx (of_PInt hy)
  rwa [add_zero] at this

lemma PInt_mul {k : ℤ} {x y : ℂ} (hy : PInt 2 y) (hx : V2 k x) : V2 k (y * x) := by
  rw [mul_comm]
  exact mul_PInt hx hy

lemma s2_zpow (k : ℤ) : V2 k (s2 ^ k) := ⟨1, PInt.one Nat.prime_two, by simp⟩

lemma two_zpow (k : ℤ) : V2 (2 * k) ((2 : ℂ) ^ k) := by
  refine ⟨1, PInt.one Nat.prime_two, ?_⟩
  rw [mul_one, zpow_mul, ← s2_sq]
  norm_cast

lemma two_pow (k : ℕ) : V2 (2 * k) ((2 : ℂ) ^ k) := by
  have := two_zpow (k : ℤ)
  rwa [zpow_natCast] at this

lemma two : V2 2 (2 : ℂ) := by
  have := two_pow 1
  simpa using this

lemma natCast (n : ℕ) : V2 0 (n : ℂ) := of_PInt (PInt.natCast Nat.prime_two n)

lemma intCast (n : ℤ) : V2 0 (n : ℂ) := of_PInt (PInt.intCast Nat.prime_two n)

/-- integer powers of a unit of the 2-integers -/
lemma unit_zpow {u : ℂ} (hu : PInt 2 u) (hu' : PInt 2 u⁻¹) (k : ℤ) : V2 0 (u ^ k) := by
  rcases Int.le_total 0 k with hk | hk
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast]
    exact of_PInt (PInt.pow Nat.prime_two hu m)
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hk)
    have : k = -(m : ℤ) := by omega
    rw [this, zpow_neg, zpow_natCast, ← inv_pow]
    exact of_PInt (PInt.pow Nat.prime_two hu' m)

lemma eps_PInt : PInt 2 eps :=
  PInt.sub Nat.prime_two (PInt.of_isIntegral Nat.prime_two s2_isIntegral) (PInt.one Nat.prime_two)

lemma eps_inv_PInt : PInt 2 eps⁻¹ := by
  rw [eps_inv]
  exact PInt.add Nat.prime_two (PInt.of_isIntegral Nat.prime_two s2_isIntegral)
    (PInt.one Nat.prime_two)

lemma eps_zpow (k : ℤ) : V2 0 (eps ^ k) := unit_zpow eps_PInt eps_inv_PInt k

lemma cc_zpow (k : ℤ) : V2 (3 * k) (cc ^ k) := by
  rw [cc_eq, mul_zpow]
  have h1 : V2 (3 * k) ((s2 ^ 3) ^ k) := by
    refine ⟨1, PInt.one Nat.prime_two, ?_⟩
    rw [mul_one, zpow_mul]
    norm_cast
  have := mul h1 (eps_zpow k)
  rwa [add_zero] at this

/-- the inverse of an odd integer is a 2-integer -/
lemma inv_odd {m : ℤ} (hm : Odd m) : V2 0 ((m : ℂ)⁻¹) := by
  refine of_PInt (PInt.inv_intCast ?_)
  intro h
  have h2 : (2 : ℤ) ∣ m := by exact_mod_cast h
  exact (Int.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h2)

/-- a nonzero natural number `n` is `2^{v₂(n)}` times an odd number -/
lemma natCast_val (n : ℕ) : V2 (2 * (padicValNat 2 n : ℤ)) (n : ℂ) := by
  obtain ⟨m, hm⟩ := @pow_padicValNat_dvd 2 n
  refine ⟨m, PInt.natCast Nat.prime_two m, ?_⟩
  have h1 : (s2 : ℂ) ^ (2 * (padicValNat 2 n : ℤ)) = (2 : ℂ) ^ (padicValNat 2 n) := by
    rw [zpow_mul, ← zpow_natCast (2 : ℂ), ← s2_sq]
    norm_cast
  rw [h1]
  conv_lhs => rw [hm]
  push_cast
  ring

/-- the inverse of a nonzero natural number: only the 2-part is lost -/
lemma inv_natCast_val {n : ℕ} (hn : n ≠ 0) : V2 (-(2 * (padicValNat 2 n : ℤ))) ((n : ℂ)⁻¹) := by
  have hodd : ¬ 2 ∣ n / 2 ^ padicValNat 2 n := by
    have := Nat.not_dvd_ordCompl Nat.prime_two hn
    rwa [Nat.factorization_def n Nat.prime_two] at this
  have hmul : 2 ^ padicValNat 2 n * (n / 2 ^ padicValNat 2 n) = n :=
    Nat.mul_div_cancel' pow_padicValNat_dvd
  refine ⟨((n / 2 ^ padicValNat 2 n : ℕ) : ℂ)⁻¹, PInt.inv_natCast hodd, ?_⟩
  have h1 : (s2 : ℂ) ^ (-(2 * (padicValNat 2 n : ℤ))) = ((2 : ℂ) ^ (padicValNat 2 n))⁻¹ := by
    rw [zpow_neg, zpow_mul, ← zpow_natCast (2 : ℂ), ← s2_sq]
    norm_cast
  rw [h1, ← mul_inv]
  congr 1
  exact_mod_cast hmul.symm

/-- Legendre: `v₂(a!) = a - s₂(a)`. -/
lemma factorial (a : ℕ) :
    V2 (2 * (a : ℤ) - 2 * ((Nat.digits 2 a).sum : ℤ)) ((a.factorial : ℕ) : ℂ) := by
  have h := @sub_one_mul_padicValNat_factorial 2 ⟨Nat.prime_two⟩ a
  have hle : (Nat.digits 2 a).sum ≤ a := Nat.digit_sum_le 2 a
  have hv : (padicValNat 2 a.factorial : ℤ) = (a : ℤ) - ((Nat.digits 2 a).sum : ℤ) := by
    have : padicValNat 2 a.factorial = a - (Nat.digits 2 a).sum := by simpa using h
    rw [this]
    push_cast [hle]
    ring
  have := natCast_val a.factorial
  rw [hv] at this
  convert this using 1
  ring

/-- from the filtration back to 2-integrality of `2^L x` -/
lemma PInt_two_pow_mul {L : ℕ} {x : ℂ} (hx : V2 (-(2 * (L : ℤ))) x) : PInt 2 ((2 : ℂ) ^ L * x) := by
  have := mul (two_pow L) hx
  rw [show (2 * (L : ℤ) + -(2 * (L : ℤ))) = 0 by ring] at this
  exact to_PInt this

end V2

end PiMeasure
