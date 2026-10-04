import MuPi.K2H.Defs

/-!
# K2H, triple `(5,3,4)`: growth rate of the (truncated) arithmetic multiplier

`DmultK K n = lcm(1..4n) / PhiK K n`, where `PhiK K n` is the product of the primes `p` with
`n/p` in one of the first `K` "windows".  Assuming the prime number theorem in the form
`θ(x)/x → 1` we prove `log (DmultK K n) / n → 4 - varpiK K`.
-/

open Filter Topology

namespace PiMeasure

/-- `p` is a prime with `n/p` in one of the first `K` windows. -/
def WindowPrime (K n p : ℕ) : Prop :=
  p.Prime ∧ ∃ k, k < K ∧
    ((4 * n < (4 * k + 3) * p ∧ (3 * k + 2) * p ≤ 3 * n) ∨
     (1 ≤ k ∧ 4 * n < (4 * k + 1) * p ∧ (5 * k + 1) * p ≤ 5 * n))

instance (K n p : ℕ) : Decidable (WindowPrime K n p) := by unfold WindowPrime; infer_instance

def PhiK (K n : ℕ) : ℕ := ∏ p ∈ (Finset.range (4 * n + 1)).filter (WindowPrime K n), p

def DmultK (K n : ℕ) : ℕ := Nat.lcmUpto (4 * n) / PhiK K n

noncomputable def varpiK (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, ((3 : ℝ) / (3 * k + 2) - 4 / (4 * k + 3)) +
  ∑ k ∈ Finset.Ico 1 K, ((5 : ℝ) / (5 * k + 1) - 4 / (4 * k + 1))

/-! ## Window primes are removable -/

/-- Division with remainder, in the form used below. -/
private lemma div_mod_of_eq {a p t s : ℕ} (h : a = p * t + s) (hs : s < p) :
    a / p = t ∧ a % p = s := by
  subst h
  have hp : 0 < p := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hs, Nat.add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs]

/-- First kind of window: `n / p = k` and the remainder `r` satisfies `2p ≤ 3r`, `4r < 3p`. -/
private lemma window_one {n p k : ℕ} (hp : 0 < p) (h1 : 4 * n < (4 * k + 3) * p)
    (h2 : (3 * k + 2) * p ≤ 3 * n) :
    ∃ r, n = p * k + r ∧ r < p ∧ 2 * p ≤ 3 * r ∧ 4 * r < 3 * p := by
  obtain ⟨q, r, hr, hn⟩ : ∃ q r, r < p ∧ p * q + r = n :=
    ⟨n / p, n % p, Nat.mod_lt _ hp, Nat.div_add_mod n p⟩
  have hq : q = k := by
    rcases Nat.lt_trichotomy q k with hlt | heq | hgt
    · exfalso
      have := Nat.mul_le_mul_left p (show q + 1 ≤ k from hlt)
      nlinarith
    · exact heq
    · exfalso
      have := Nat.mul_le_mul_left p (show k + 1 ≤ q from hgt)
      nlinarith
  subst hq
  refine ⟨r, hn.symm, hr, ?_, ?_⟩ <;> nlinarith

/-- Second kind of window: `n / p = k` and the remainder `r` satisfies `p ≤ 5r`, `4r < p`. -/
private lemma window_two {n p k : ℕ} (hp : 0 < p) (h1 : 4 * n < (4 * k + 1) * p)
    (h2 : (5 * k + 1) * p ≤ 5 * n) :
    ∃ r, n = p * k + r ∧ r < p ∧ p ≤ 5 * r ∧ 4 * r < p := by
  obtain ⟨q, r, hr, hn⟩ : ∃ q r, r < p ∧ p * q + r = n :=
    ⟨n / p, n % p, Nat.mod_lt _ hp, Nat.div_add_mod n p⟩
  have hq : q = k := by
    rcases Nat.lt_trichotomy q k with hlt | heq | hgt
    · exfalso
      have := Nat.mul_le_mul_left p (show q + 1 ≤ k from hlt)
      nlinarith
    · exact heq
    · exfalso
      have := Nat.mul_le_mul_left p (show k + 1 ≤ q from hgt)
      nlinarith
  subst hq
  refine ⟨r, hn.symm, hr, ?_, ?_⟩ <;> nlinarith

/-- window primes are removable once `n ≥ 4 K²` (so that `p² > 4n`) -/
theorem windowPrime_removable {K n p : ℕ} (hn : 4 * K ^ 2 ≤ n) (h : WindowPrime K n p) :
    RemovablePrime n p := by
  obtain ⟨hp, k, hk, h⟩ := h
  have hp0 : 0 < p := hp.pos
  -- `n < K * p` in both cases
  have hnK : n < K * p := by
    have hkp : (k + 1) * p ≤ K * p := Nat.mul_le_mul_right p hk
    rcases h with ⟨h1, _⟩ | ⟨_, h1, _⟩ <;> nlinarith
  have h4K : 4 * K < p := by
    by_contra hcon
    have hcon' : p ≤ 4 * K := Nat.le_of_not_lt hcon
    have := Nat.mul_le_mul_left K hcon'
    nlinarith
  have hsq : 4 * n < p ^ 2 := by nlinarith
  refine ⟨hp, hsq, ?_⟩
  rcases h with ⟨h1, h2⟩ | ⟨_, h1, h2⟩
  · obtain ⟨r, rfl, hr, hr1, hr2⟩ := window_one hp0 h1 h2
    obtain ⟨s4, hs4⟩ : ∃ s, 4 * r = 2 * p + s := ⟨4 * r - 2 * p, by omega⟩
    obtain ⟨s5, hs5⟩ : ∃ s, 5 * r = 3 * p + s := ⟨5 * r - 3 * p, by omega⟩
    obtain ⟨s3, hs3⟩ : ∃ s, 3 * r = 2 * p + s := ⟨3 * r - 2 * p, by omega⟩
    obtain ⟨e4, m4⟩ := div_mod_of_eq (a := 4 * (p * k + r)) (p := p) (t := 4 * k + 2) (s := s4)
      (by linarith) (by omega)
    obtain ⟨-, m5⟩ := div_mod_of_eq (a := 5 * (p * k + r)) (p := p) (t := 5 * k + 3) (s := s5)
      (by linarith) (by omega)
    obtain ⟨-, m3⟩ := div_mod_of_eq (a := 3 * (p * k + r)) (p := p) (t := 3 * k + 2) (s := s3)
      (by linarith) (by omega)
    rw [e4, m4, m5, m3]
    exact ⟨⟨2 * k + 1, by ring⟩, by omega⟩
  · obtain ⟨r, rfl, hr, hr1, hr2⟩ := window_two hp0 h1 h2
    obtain ⟨s5, hs5⟩ : ∃ s, 5 * r = p + s := ⟨5 * r - p, by omega⟩
    obtain ⟨e4, m4⟩ := div_mod_of_eq (a := 4 * (p * k + r)) (p := p) (t := 4 * k) (s := 4 * r)
      (by linarith) (by omega)
    obtain ⟨-, m5⟩ := div_mod_of_eq (a := 5 * (p * k + r)) (p := p) (t := 5 * k + 1) (s := s5)
      (by linarith) (by omega)
    obtain ⟨-, m3⟩ := div_mod_of_eq (a := 3 * (p * k + r)) (p := p) (t := 3 * k) (s := 3 * r)
      (by linarith) (by omega)
    rw [e4, m4, m5, m3]
    exact ⟨⟨2 * k, by ring⟩, by omega⟩

/-! ## Divisibility facts about `PhiK` -/

theorem PhiK_dvd_lcmUpto (K n : ℕ) : PhiK K n ∣ Nat.lcmUpto (4 * n) := by
  refine dvd_trans ?_ (Nat.primorial_dvd_lcmUpto (4 * n))
  unfold PhiK primorial
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1⟩

/-- for a prime `p`: `p ∣ PhiK K n` iff `p` is a window prime (and then `p ≤ 4n`) -/
theorem prime_dvd_PhiK_iff {K n p : ℕ} (hp : p.Prime) :
    p ∣ PhiK K n ↔ (WindowPrime K n p ∧ p ≤ 4 * n) := by
  unfold PhiK
  rw [Prime.dvd_finsetProd_iff hp.prime]
  constructor
  · rintro ⟨q, hq, hpq⟩
    rw [Finset.mem_filter, Finset.mem_range] at hq
    have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hq.2.1).mp hpq
    subst hpq'
    exact ⟨hq.2, by omega⟩
  · rintro ⟨hw, hle⟩
    refine ⟨p, ?_, dvd_rfl⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hw⟩

/-! ## `log PhiK` as a combination of values of `θ` -/

/-- `θ m` for a natural number `m`, as a sum over `Ioc 0 m`. -/
private lemma theta_natCast_eq (m : ℕ) :
    Chebyshev.theta (m : ℝ) = ∑ p ∈ Finset.Ioc 0 m, if p.Prime then Real.log p else 0 := by
  rw [Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter]

/-- `θ b - θ a` is the sum of `log p` over the primes `p ∈ (a, b]`. -/
private lemma theta_sub_theta {a b : ℕ} (hab : a ≤ b) :
    Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) =
      ∑ p ∈ Finset.Ioc a b, if p.Prime then Real.log p else 0 := by
  rw [theta_natCast_eq, theta_natCast_eq, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  ring

private lemma mem_Ioc_one {n k p : ℕ} :
    p ∈ Finset.Ioc (4 * n / (4 * k + 3)) (3 * n / (3 * k + 2)) ↔
      (4 * n < (4 * k + 3) * p ∧ (3 * k + 2) * p ≤ 3 * n) := by
  rw [Finset.mem_Ioc, Nat.div_lt_iff_lt_mul (by omega), Nat.le_div_iff_mul_le (by omega),
    mul_comm p, mul_comm p]

private lemma mem_Ioc_two {n k p : ℕ} :
    p ∈ Finset.Ioc (4 * n / (4 * k + 1)) (5 * n / (5 * k + 1)) ↔
      (4 * n < (4 * k + 1) * p ∧ (5 * k + 1) * p ≤ 5 * n) := by
  rw [Finset.mem_Ioc, Nat.div_lt_iff_lt_mul (by omega), Nat.le_div_iff_mul_le (by omega),
    mul_comm p, mul_comm p]

private lemma window_one_div {n p k : ℕ} (hp : 0 < p) (h1 : 4 * n < (4 * k + 3) * p)
    (h2 : (3 * k + 2) * p ≤ 3 * n) :
    n / p = k ∧ 2 * p ≤ 3 * (n % p) ∧ 4 * (n % p) < 3 * p := by
  obtain ⟨r, hn, hr, hr1, hr2⟩ := window_one hp h1 h2
  obtain ⟨hd, hm⟩ := div_mod_of_eq hn hr
  rw [hd, hm]
  exact ⟨rfl, hr1, hr2⟩

private lemma window_two_div {n p k : ℕ} (hp : 0 < p) (h1 : 4 * n < (4 * k + 1) * p)
    (h2 : (5 * k + 1) * p ≤ 5 * n) :
    n / p = k ∧ p ≤ 5 * (n % p) ∧ 4 * (n % p) < p := by
  obtain ⟨r, hn, hr, hr1, hr2⟩ := window_two hp h1 h2
  obtain ⟨hd, hm⟩ := div_mod_of_eq hn hr
  rw [hd, hm]
  exact ⟨rfl, hr1, hr2⟩

/-- a sum of `if c k then x else 0` over `k ∈ s`, when at most one `k ∈ s` satisfies `c k` -/
private lemma sum_ite_eq_of_unique (s : Finset ℕ) (c : ℕ → Prop) [DecidablePred c] (x : ℝ)
    (hu : ∀ k ∈ s, ∀ k' ∈ s, c k → c k' → k = k') :
    (∑ k ∈ s, if c k then x else 0) = if (∃ k ∈ s, c k) then x else 0 := by
  split_ifs with h
  · obtain ⟨k₀, hk₀, hc₀⟩ := h
    rw [Finset.sum_eq_single_of_mem k₀ hk₀
      (fun k hk hne => if_neg (fun hc => hne (hu k hk k₀ hk₀ hc hc₀))), if_pos hc₀]
  · exact Finset.sum_eq_zero (fun k hk => if_neg (fun hc => h ⟨k, hk, hc⟩))

/-- the indicator of the window primes, split according to the window -/
private lemma window_indicator (K n p : ℕ) :
    (if WindowPrime K n p then Real.log p else 0) =
      ∑ k ∈ Finset.range K,
          (if p ∈ Finset.Ioc (4 * n / (4 * k + 3)) (3 * n / (3 * k + 2)) then
            (if p.Prime then Real.log p else 0) else 0) +
      ∑ k ∈ Finset.Ico 1 K,
          (if p ∈ Finset.Ioc (4 * n / (4 * k + 1)) (5 * n / (5 * k + 1)) then
            (if p.Prime then Real.log p else 0) else 0) := by
  by_cases hp : p.Prime
  swap
  · have hW : ¬ WindowPrime K n p := fun h => hp h.1
    simp [hp, hW]
  have hp0 : 0 < p := hp.pos
  have hu1 : ∀ k ∈ Finset.range K, ∀ k' ∈ Finset.range K,
      p ∈ Finset.Ioc (4 * n / (4 * k + 3)) (3 * n / (3 * k + 2)) →
      p ∈ Finset.Ioc (4 * n / (4 * k' + 3)) (3 * n / (3 * k' + 2)) → k = k' := by
    intro k _ k' _ h h'
    obtain ⟨ha, hb⟩ := mem_Ioc_one.mp h
    obtain ⟨ha', hb'⟩ := mem_Ioc_one.mp h'
    exact (window_one_div hp0 ha hb).1.symm.trans (window_one_div hp0 ha' hb').1
  have hu2 : ∀ k ∈ Finset.Ico 1 K, ∀ k' ∈ Finset.Ico 1 K,
      p ∈ Finset.Ioc (4 * n / (4 * k + 1)) (5 * n / (5 * k + 1)) →
      p ∈ Finset.Ioc (4 * n / (4 * k' + 1)) (5 * n / (5 * k' + 1)) → k = k' := by
    intro k _ k' _ h h'
    obtain ⟨ha, hb⟩ := mem_Ioc_two.mp h
    obtain ⟨ha', hb'⟩ := mem_Ioc_two.mp h'
    exact (window_two_div hp0 ha hb).1.symm.trans (window_two_div hp0 ha' hb').1
  have hWiff : WindowPrime K n p ↔
      (∃ k ∈ Finset.range K, p ∈ Finset.Ioc (4 * n / (4 * k + 3)) (3 * n / (3 * k + 2))) ∨
      (∃ k ∈ Finset.Ico 1 K, p ∈ Finset.Ioc (4 * n / (4 * k + 1)) (5 * n / (5 * k + 1))) := by
    constructor
    · rintro ⟨-, k, hk, h | ⟨hk1, h⟩⟩
      · exact Or.inl ⟨k, Finset.mem_range.mpr hk, mem_Ioc_one.mpr h⟩
      · exact Or.inr ⟨k, Finset.mem_Ico.mpr ⟨hk1, hk⟩, mem_Ioc_two.mpr h⟩
    · rintro (⟨k, hk, h⟩ | ⟨k, hk, h⟩)
      · exact ⟨hp, k, Finset.mem_range.mp hk, Or.inl (mem_Ioc_one.mp h)⟩
      · exact ⟨hp, k, (Finset.mem_Ico.mp hk).2, Or.inr ⟨(Finset.mem_Ico.mp hk).1,
          mem_Ioc_two.mp h⟩⟩
  have hX : ¬ ((∃ k ∈ Finset.range K, p ∈ Finset.Ioc (4 * n / (4 * k + 3)) (3 * n / (3 * k + 2)))
      ∧ (∃ k ∈ Finset.Ico 1 K, p ∈ Finset.Ioc (4 * n / (4 * k + 1)) (5 * n / (5 * k + 1)))) := by
    rintro ⟨⟨k, -, h⟩, ⟨k', -, h'⟩⟩
    obtain ⟨c1a, c1b⟩ := mem_Ioc_one.mp h
    obtain ⟨c2a, c2b⟩ := mem_Ioc_two.mp h'
    obtain ⟨-, r1, -⟩ := window_one_div hp0 c1a c1b
    obtain ⟨-, -, r2⟩ := window_two_div hp0 c2a c2b
    generalize n % p = r at r1 r2
    omega
  rw [sum_ite_eq_of_unique (Finset.range K) _ _ hu1, sum_ite_eq_of_unique (Finset.Ico 1 K) _ _ hu2]
  simp only [if_pos hp]
  by_cases h1 : ∃ k ∈ Finset.range K, p ∈ Finset.Ioc (4 * n / (4 * k + 3)) (3 * n / (3 * k + 2))
  · have hW : WindowPrime K n p := hWiff.mpr (Or.inl h1)
    have h2 : ¬ ∃ k ∈ Finset.Ico 1 K, p ∈ Finset.Ioc (4 * n / (4 * k + 1)) (5 * n / (5 * k + 1)) :=
      fun h2 => hX ⟨h1, h2⟩
    rw [if_pos hW, if_pos h1, if_neg h2, add_zero]
  · by_cases h2 : ∃ k ∈ Finset.Ico 1 K, p ∈ Finset.Ioc (4 * n / (4 * k + 1)) (5 * n / (5 * k + 1))
    · have hW : WindowPrime K n p := hWiff.mpr (Or.inr h2)
      rw [if_pos hW, if_neg h1, if_pos h2, zero_add]
    · have hW : ¬ WindowPrime K n p := fun hW => (hWiff.mp hW).elim h1 h2
      rw [if_neg hW, if_neg h1, if_neg h2, add_zero]

private lemma a1_le_b1 (n k : ℕ) : 4 * n / (4 * k + 3) ≤ 3 * n / (3 * k + 2) := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  have h := Nat.div_mul_le_self (4 * n) (4 * k + 3)
  generalize 4 * n / (4 * k + 3) = q at h ⊢
  nlinarith

private lemma a2_le_b2 (n k : ℕ) : 4 * n / (4 * k + 1) ≤ 5 * n / (5 * k + 1) := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  have h := Nat.div_mul_le_self (4 * n) (4 * k + 1)
  generalize 4 * n / (4 * k + 1) = q at h ⊢
  nlinarith

private lemma b1_le (n k : ℕ) : 3 * n / (3 * k + 2) ≤ 4 * n :=
  (Nat.div_le_self _ _).trans (by omega)

private lemma b2_le (n k : ℕ) (hk : 1 ≤ k) : 5 * n / (5 * k + 1) ≤ 4 * n := by
  apply Nat.div_le_of_le_mul
  nlinarith [Nat.mul_le_mul_right n hk]

/-- `log (PhiK K n)` as a combination of values of `θ` -/
private theorem log_PhiK_eq (K n : ℕ) :
    Real.log (PhiK K n) =
      ∑ k ∈ Finset.range K, (Chebyshev.theta ((3 * n / (3 * k + 2) : ℕ) : ℝ) -
        Chebyshev.theta ((4 * n / (4 * k + 3) : ℕ) : ℝ)) +
      ∑ k ∈ Finset.Ico 1 K, (Chebyshev.theta ((5 * n / (5 * k + 1) : ℕ) : ℝ) -
        Chebyshev.theta ((4 * n / (4 * k + 1) : ℕ) : ℝ)) := by
  have h1 : Real.log (PhiK K n) =
      ∑ p ∈ Finset.range (4 * n + 1), if WindowPrime K n p then Real.log p else 0 := by
    unfold PhiK
    rw [Nat.cast_prod, Real.log_prod, Finset.sum_filter]
    intro p hp
    rw [Finset.mem_filter] at hp
    exact_mod_cast hp.2.1.ne_zero
  rw [h1]
  simp_rw [window_indicator K n]
  rw [Finset.sum_add_distrib, Finset.sum_comm (s := Finset.range (4 * n + 1)) (t := Finset.range K),
    Finset.sum_comm (s := Finset.range (4 * n + 1)) (t := Finset.Ico 1 K)]
  congr 1
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr ?_, theta_sub_theta (a1_le_b1 n k)]
    intro p hp
    rw [Finset.mem_Ioc] at hp
    rw [Finset.mem_range]
    have := b1_le n k
    omega
  · refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr ?_, theta_sub_theta (a2_le_b2 n k)]
    intro p hp
    rw [Finset.mem_Ioc] at hp
    rw [Finset.mem_range]
    have := b2_le n k hk1
    omega

private theorem PhiK_pos_aux (K n : ℕ) : 0 < PhiK K n :=
  Finset.prod_pos (fun _ hp => (Finset.mem_filter.mp hp).2.1.pos)

private theorem DmultK_pos_aux (K n : ℕ) : 0 < DmultK K n :=
  Nat.div_pos (Nat.le_of_dvd (Nat.lcmUpto_pos _) (PhiK_dvd_lcmUpto K n)) (PhiK_pos_aux K n)

private theorem log_DmultK_eq (K n : ℕ) :
    Real.log (DmultK K n) = Chebyshev.psi ((4 * n : ℕ) : ℝ) - Real.log (PhiK K n) := by
  have hΦ : (PhiK K n : ℝ) ≠ 0 := by exact_mod_cast (PhiK_pos_aux K n).ne'
  have hL : (Nat.lcmUpto (4 * n) : ℝ) ≠ 0 := by exact_mod_cast Nat.lcmUpto_ne_zero _
  rw [DmultK, Nat.cast_div (PhiK_dvd_lcmUpto K n) hΦ, Real.log_div hL hΦ,
    Chebyshev.psi_eq_log_lcmUpto]

/-! ## Asymptotics, assuming `θ(x) ~ x` -/

private lemma tendsto_theta_mul (hPNT : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Chebyshev.theta (c * n) / n) atTop (𝓝 c) := by
  have h1 : Tendsto (fun n : ℕ => c * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hc tendsto_natCast_atTop_atTop
  have h2 := (hPNT.comp h1).const_mul c
  rw [mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp]
  field_simp

private lemma tendsto_theta_natDiv
    (hPNT : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1))
    {a b : ℕ} {c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : (a : ℝ) / b = c) :
    Tendsto (fun n : ℕ => Chebyshev.theta ((a * n / b : ℕ) : ℝ) / n) atTop (𝓝 c) := by
  have hc0 : 0 < c := by rw [← hc]; positivity
  refine (tendsto_theta_mul hPNT hc0).congr (fun n => ?_)
  have hfl : ⌊c * n⌋₊ = a * n / b := by
    rw [show c * n = ((a * n : ℕ) : ℝ) / ((b : ℕ) : ℝ) by rw [← hc]; push_cast; ring]
    exact Nat.floor_div_eq_div (a * n) b
  rw [Chebyshev.theta_eq_theta_coe_floor (c * n), hfl]

private lemma tendsto_sqrt_mul_log_div :
    Tendsto (fun x : ℝ => 2 * √x * Real.log x / x) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).sqrt
  rw [Real.sqrt_zero] at h
  have h2 := h.const_mul 2
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [one_mul, add_zero, Real.sqrt_div' _ hx0.le, Real.sqrt_sq hlog]
  have hs : 0 < √x := Real.sqrt_pos.mpr hx0
  field_simp
  rw [Real.sq_sqrt hx0.le]

private lemma tendsto_psi_four (hPNT : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => Chebyshev.psi ((4 * n : ℕ) : ℝ) / n) atTop (𝓝 4) := by
  have hθ : Tendsto (fun n : ℕ => Chebyshev.theta (4 * n) / n) atTop (𝓝 4) :=
    tendsto_theta_mul hPNT (by norm_num)
  have hE : Tendsto (fun n : ℕ => (Chebyshev.psi (4 * n) - Chebyshev.theta (4 * n)) / n)
      atTop (𝓝 0) := by
    have h4 : Tendsto (fun n : ℕ => (4 : ℝ) * n) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
    have hb := (tendsto_sqrt_mul_log_div.comp h4).const_mul 4
    rw [mul_zero] at hb
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hx : (1 : ℝ) ≤ 4 * n := by linarith
    have habs := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
    simp only [Function.comp, Real.norm_eq_abs]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < n), div_le_iff₀ (by positivity)]
    calc |Chebyshev.psi (4 * n) - Chebyshev.theta (4 * n)|
        ≤ 2 * √(4 * n) * Real.log (4 * n) := habs
      _ = 4 * (2 * √(4 * n) * Real.log (4 * n) / (4 * n)) * n := by field_simp
  have := hθ.add hE
  rw [add_zero] at this
  refine this.congr (fun n => ?_)
  push_cast
  ring

theorem DmultK_rate (hPNT : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1)) (K : ℕ) :
    ∀ η : ℝ, 0 < η → ∃ n₁ : ℕ, ∀ n, n₁ ≤ n →
      Real.exp ((4 - varpiK K - η) * n) ≤ (DmultK K n : ℝ) ∧
      (DmultK K n : ℝ) ≤ Real.exp ((4 - varpiK K + η) * n) := by
  have hsum1 : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range K,
      (Chebyshev.theta ((3 * n / (3 * k + 2) : ℕ) : ℝ) / n -
        Chebyshev.theta ((4 * n / (4 * k + 3) : ℕ) : ℝ) / n))
      atTop (𝓝 (∑ k ∈ Finset.range K, ((3 : ℝ) / (3 * k + 2) - 4 / (4 * k + 3)))) := by
    refine tendsto_finsetSum _ (fun k _ => ?_)
    exact (tendsto_theta_natDiv hPNT (by norm_num) (by omega) (by push_cast; ring)).sub
      (tendsto_theta_natDiv hPNT (by norm_num) (by omega) (by push_cast; ring))
  have hsum2 : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Ico 1 K,
      (Chebyshev.theta ((5 * n / (5 * k + 1) : ℕ) : ℝ) / n -
        Chebyshev.theta ((4 * n / (4 * k + 1) : ℕ) : ℝ) / n))
      atTop (𝓝 (∑ k ∈ Finset.Ico 1 K, ((5 : ℝ) / (5 * k + 1) - 4 / (4 * k + 1)))) := by
    refine tendsto_finsetSum _ (fun k _ => ?_)
    exact (tendsto_theta_natDiv hPNT (by norm_num) (by omega) (by push_cast; ring)).sub
      (tendsto_theta_natDiv hPNT (by norm_num) (by omega) (by push_cast; ring))
  have hlim : Tendsto (fun n : ℕ => Real.log (DmultK K n) / n) atTop (𝓝 (4 - varpiK K)) := by
    have h := (tendsto_psi_four hPNT).sub (hsum1.add hsum2)
    unfold varpiK
    refine h.congr (fun n => ?_)
    rw [log_DmultK_eq, log_PhiK_eq]
    simp only [sub_div, add_div, Finset.sum_div]
  intro η hη
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim η hη
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hd := hN n hnN
  rw [Real.dist_eq, abs_lt] at hd
  obtain ⟨hlo, hhi⟩ := hd
  have hDpos : (0 : ℝ) < DmultK K n := by exact_mod_cast DmultK_pos_aux K n
  have hlo' : (4 - varpiK K - η) * n ≤ Real.log (DmultK K n) := by
    have := (lt_div_iff₀ hnpos).mp (by linarith : 4 - varpiK K - η < Real.log (DmultK K n) / n)
    linarith
  have hhi' : Real.log (DmultK K n) ≤ (4 - varpiK K + η) * n := by
    have := (div_lt_iff₀ hnpos).mp (by linarith : Real.log (DmultK K n) / n < 4 - varpiK K + η)
    linarith
  constructor
  · calc Real.exp ((4 - varpiK K - η) * n) ≤ Real.exp (Real.log (DmultK K n)) :=
          Real.exp_le_exp.mpr hlo'
      _ = DmultK K n := Real.exp_log hDpos
  · calc (DmultK K n : ℝ) = Real.exp (Real.log (DmultK K n)) := (Real.exp_log hDpos).symm
      _ ≤ Real.exp ((4 - varpiK K + η) * n) := Real.exp_le_exp.mpr hhi'

/-! ## A numerical lower bound for `varpiK 100000` -/

private lemma tele1 {x : ℝ} (hx : 20 ≤ x) :
    (1/12 : ℝ) * (1 / (x + 43/200) - 1 / (x + 1 + 43/200)) ≤ 3 / (3 * x + 2) - 4 / (4 * x + 3) := by
  have h1 : 0 < 3 * x + 2 := by linarith
  have h2 : 0 < 4 * x + 3 := by linarith
  have h3 : 0 < x + 43/200 := by linarith
  have h4 : 0 < x + 1 + 43/200 := by linarith
  rw [div_sub_div _ _ h3.ne' h4.ne', div_sub_div _ _ h1.ne' h2.ne', mul_div_assoc',
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

private lemma tele2 {x : ℝ} (hx : 20 ≤ x) :
    (1/20 : ℝ) * (1 / (x - 67/250) - 1 / (x + 1 - 67/250)) ≤ 5 / (5 * x + 1) - 4 / (4 * x + 1) := by
  have h1 : 0 < 5 * x + 1 := by linarith
  have h2 : 0 < 4 * x + 1 := by linarith
  have h3 : 0 < x - 67/250 := by linarith
  have h4 : 0 < x + 1 - 67/250 := by linarith
  rw [div_sub_div _ _ h3.ne' h4.ne', div_sub_div _ _ h1.ne' h2.ne', mul_div_assoc',
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- telescoping lower bound for the tail of the first series -/
private lemma tail1 (K : ℕ) (hK : 20 ≤ K) :
    (1/12 : ℝ) * (1 / (20 + 43/200) - 1 / (K + 43/200)) ≤
      ∑ k ∈ Finset.Ico 20 K, ((3 : ℝ) / (3 * k + 2) - 4 / (4 * k + 3)) := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm]
    have := tele1 (x := (m : ℝ)) (by exact_mod_cast hm)
    push_cast
    linarith

/-- telescoping lower bound for the tail of the second series -/
private lemma tail2 (K : ℕ) (hK : 20 ≤ K) :
    (1/20 : ℝ) * (1 / (20 - 67/250) - 1 / (K - 67/250)) ≤
      ∑ k ∈ Finset.Ico 20 K, ((5 : ℝ) / (5 * k + 1) - 4 / (4 * k + 1)) := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm]
    have := tele2 (x := (m : ℝ)) (by exact_mod_cast hm)
    push_cast
    linarith

/-- the first `20` terms, evaluated exactly -/
private lemma head_bound :
    (0.293957 : ℝ) - (1/12 : ℝ) * (1 / (20 + 43/200) - 1 / (100000 + 43/200))
      - (1/20 : ℝ) * (1 / (20 - 67/250) - 1 / (100000 - 67/250)) ≤
    ∑ k ∈ Finset.range 20, ((3 : ℝ) / (3 * (k : ℝ) + 2) - 4 / (4 * (k : ℝ) + 3)) +
      ∑ k ∈ Finset.Ico (1 : ℕ) 20, ((5 : ℝ) / (5 * (k : ℝ) + 1) - 4 / (4 * (k : ℝ) + 1)) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem varpiK_lower : (0.293957 : ℝ) ≤ varpiK 100000 := by
  have t1 := tail1 100000 (by norm_num)
  have t2 := tail2 100000 (by norm_num)
  have hh := head_bound
  unfold varpiK
  rw [← Finset.sum_range_add_sum_Ico _ (show 20 ≤ 100000 by norm_num),
    ← Finset.sum_Ico_consecutive _ (show 1 ≤ 20 by norm_num) (show 20 ≤ 100000 by norm_num)]
  generalize ∑ k ∈ Finset.Ico (20 : ℕ) 100000,
    ((3 : ℝ) / (3 * (k : ℝ) + 2) - 4 / (4 * (k : ℝ) + 3)) = S1 at t1 ⊢
  generalize ∑ k ∈ Finset.Ico (20 : ℕ) 100000,
    ((5 : ℝ) / (5 * (k : ℝ) + 1) - 4 / (4 * (k : ℝ) + 1)) = S2 at t2 ⊢
  push_cast at t1 t2
  linarith

end PiMeasure

#print axioms PiMeasure.DmultK_rate
#print axioms PiMeasure.varpiK_lower
