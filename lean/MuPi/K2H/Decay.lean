import MuPi.K2H.ContourBound
import MuPi.K2H.LinearForm

/-!
# K2H, triple `(5,3,4)`: the decay `|J_n| ≤ 4 ρ^n` (Lemma 6.2)

Let `(G, c)` be a primitive pair for `f^n/z` and `F = G + c·log`.  By `J534_eq_of_primPair` and
`log(1+i) − log(1−i) = iπ/2` we have `J_n = −i (F(1+i) − F(1−i))`.  We move the path of integration
to the polygon `1 − i → conj zs → 1 → zs → 1 + i`: the endpoint difference telescopes into four
segment integrals (`segment_integral_of_primPair`; every point of the polygon has real part in
`[1, 19787/16384]`, so it lies in the right half-plane and is not `√2`), and each of them has norm
`≤ ρ^n`, because

* `|f| ≤ ρ` on the two upper segments (`f534_le_seg1`, `f534_le_seg2`) and, by conjugation
  (`f534` has real coefficients), on the two lower ones;
* `|z| ≥ Re z ≥ 1` on the polygon;
* each segment has length `≤ 1`.
-/

namespace PiMeasure

open Complex

namespace Decay

/-- `f534` has real coefficients -/
lemma f534_conj (z : ℂ) : f534 ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f534 z) := by
  unfold f534
  simp only [map_div₀, map_mul, map_pow, map_sub, map_add, map_one, map_ofNat]

lemma norm_f534_conj (z : ℂ) : ‖f534 ((starRingEnd ℂ) z)‖ = ‖f534 z‖ := by
  rw [f534_conj, Complex.norm_conj]

/-- `19787/16384 < √2` -/
lemma zs_re_lt_sqrt_two : (19787 / 16384 : ℝ) < Real.sqrt 2 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

/-- if both endpoints of a segment have real part in `[1, 19787/16384]`, so do all its points -/
lemma seg_re_bounds {a b : ℂ} (ha1 : 1 ≤ a.re) (ha2 : a.re ≤ 19787 / 16384)
    (hb1 : 1 ≤ b.re) (hb2 : b.re ≤ 19787 / 16384) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    1 ≤ (a + t * (b - a)).re ∧ (a + t * (b - a)).re ≤ 19787 / 16384 := by
  have hre : (a + t * (b - a)).re = a.re + t * (b.re - a.re) := by simp
  rw [hre]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 ha1), mul_nonneg h0 (sub_nonneg.2 hb1)]
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 ha2), mul_nonneg h0 (sub_nonneg.2 hb2)]

/-- a segment integral of `f^n/z` has norm `≤ ρ^n` if `|f| ≤ ρ` and `Re z ≥ 1` on the segment and
its length is `≤ 1` -/
lemma seg_integral_norm_le (n : ℕ) (a b : ℂ) (hlen : ‖b - a‖ ≤ 1)
    (hre : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 1 ≤ (a + t * (b - a)).re)
    (hf : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖f534 (a + t * (b - a))‖ ≤ rho) :
    ‖∫ t in (0 : ℝ)..1, f534 (a + t * (b - a)) ^ n / (a + t * (b - a)) * (b - a)‖
      ≤ rho ^ n := by
  have hC : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖f534 (a + t * (b - a)) ^ n / (a + t * (b - a)) * (b - a)‖ ≤ rho ^ n := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have h0 : 0 ≤ t := ht.1.le
    have h1 : t ≤ 1 := ht.2
    have hz : 1 ≤ ‖a + t * (b - a)‖ := (hre t h0 h1).trans (Complex.re_le_norm _)
    have hfn : ‖f534 (a + t * (b - a))‖ ^ n ≤ rho ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) (hf t h0 h1) n
    rw [norm_mul, norm_div, norm_pow]
    calc ‖f534 (a + t * (b - a))‖ ^ n / ‖a + t * (b - a)‖ * ‖b - a‖
        ≤ ‖f534 (a + t * (b - a))‖ ^ n * 1 :=
          mul_le_mul (div_le_self (by positivity) hz) hlen (norm_nonneg _) (by positivity)
      _ ≤ rho ^ n := by rw [mul_one]; exact hfn
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hC).trans (le_of_eq ?_)
  norm_num

/-- the endpoint difference of the primitive `G + c·log` across a segment of the polygon has norm
`≤ ρ^n` -/
lemma seg_diff_norm_le {n : ℕ} {G : ℂ → ℂ} {c : ℂ} (h : IsPrimPair n G c) (a b : ℂ)
    (ha1 : 1 ≤ a.re) (ha2 : a.re ≤ 19787 / 16384)
    (hb1 : 1 ≤ b.re) (hb2 : b.re ≤ 19787 / 16384)
    (hlen : ‖b - a‖ ≤ 1)
    (hf : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖f534 (a + t * (b - a))‖ ≤ rho) :
    ‖(G b + c * Complex.log b) - (G a + c * Complex.log a)‖ ≤ rho ^ n := by
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 < (a + t * (b - a)).re ∧ a + t * (b - a) ≠ s2 := by
    intro t h0 h1
    obtain ⟨hlo, hhi⟩ := seg_re_bounds ha1 ha2 hb1 hb2 h0 h1
    refine ⟨by linarith, ?_⟩
    intro heq
    rw [heq] at hhi
    simp only [s2, Complex.ofReal_re] at hhi
    linarith [zs_re_lt_sqrt_two]
  rw [← segment_integral_of_primPair h a b hseg]
  exact seg_integral_norm_le n a b hlen
    (fun t h0 h1 => (seg_re_bounds ha1 ha2 hb1 hb2 h0 h1).1) hf

/-- `‖w‖ ≤ 1` from `|Re w| + |Im w| ≤ 1` -/
lemma norm_le_one_of {w : ℂ} (h : |w.re| + |w.im| ≤ 1) : ‖w‖ ≤ 1 :=
  (Complex.norm_le_abs_re_add_abs_im w).trans h

/-- the lower-left segment `1 − i → conj zs` is the conjugate of the reversed segment
`zs → 1 + i` -/
lemma segA_eq (t : ℝ) : (1 - I) + t * ((starRingEnd ℂ) zs - (1 - I))
    = (starRingEnd ℂ) (zs + ((1 - t : ℝ) : ℂ) * ((1 + I) - zs)) := by
  simp only [map_add, map_mul, map_sub, map_one, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- the segment `conj zs → 1` is the conjugate of the reversed segment `1 → zs` -/
lemma segB_eq (t : ℝ) : (starRingEnd ℂ) zs + t * (1 - (starRingEnd ℂ) zs)
    = (starRingEnd ℂ) (1 + ((1 - t : ℝ) : ℂ) * (zs - 1)) := by
  simp only [map_add, map_mul, map_sub, map_one, Complex.conj_ofReal]
  push_cast
  ring

end Decay

/-- **Lemma 6.2.** `|J_n| ≤ 4 ρ^n`: integrate along the polygon `1−i → conj zs → 1 → zs → 1+i`. -/
theorem J534_norm_le (n : ℕ) {G : ℂ → ℂ} {c : ℂ} (h : IsPrimPair n G c) : ‖J534 n‖ ≤ 4 * rho ^ n := by
  set w : ℂ := (starRingEnd ℂ) zs with hw
  -- segment `1 − i → conj zs`
  have hA := Decay.seg_diff_norm_le h (1 - I) w (by norm_num) (by norm_num)
    (by norm_num [hw, zs]) (by norm_num [hw, zs])
    (Decay.norm_le_one_of (by simp [hw, zs]; norm_num))
    (fun t h0 h1 => by
      rw [Decay.segA_eq, Decay.norm_f534_conj]
      exact f534_le_seg2 (1 - t) (by linarith) (by linarith))
  -- segment `conj zs → 1`
  have hB := Decay.seg_diff_norm_le h w 1 (by norm_num [hw, zs]) (by norm_num [hw, zs])
    (by norm_num) (by norm_num)
    (Decay.norm_le_one_of (by simp [hw, zs]; norm_num))
    (fun t h0 h1 => by
      rw [Decay.segB_eq, Decay.norm_f534_conj]
      exact f534_le_seg1 (1 - t) (by linarith) (by linarith))
  -- segment `1 → zs`
  have hC := Decay.seg_diff_norm_le h 1 zs (by norm_num) (by norm_num)
    (by norm_num [zs]) (by norm_num [zs])
    (Decay.norm_le_one_of (by simp [zs]; norm_num)) f534_le_seg1
  -- segment `zs → 1 + i`
  have hD := Decay.seg_diff_norm_le h zs (1 + I) (by norm_num [zs]) (by norm_num [zs])
    (by norm_num) (by norm_num)
    (Decay.norm_le_one_of (by simp [zs]; norm_num)) f534_le_seg2
  have hJ : J534 n = -I * (((G (1 + I) + c * Complex.log (1 + I)) - (G zs + c * Complex.log zs))
      + ((G zs + c * Complex.log zs) - (G 1 + c * Complex.log 1))
      + ((G 1 + c * Complex.log 1) - (G w + c * Complex.log w))
      + ((G w + c * Complex.log w) - (G (1 - I) + c * Complex.log (1 - I)))) := by
    rw [J534_eq_of_primPair h]
    linear_combination (I * c) * log_one_add_I_sub_log_one_sub_I
      + (c * (Real.pi : ℂ) / 2) * Complex.I_sq
  rw [hJ, norm_mul, norm_neg, Complex.norm_I, one_mul]
  calc _ ≤ _ := norm_add₄_le
    _ ≤ rho ^ n + rho ^ n + rho ^ n + rho ^ n := add_le_add (add_le_add (add_le_add hD hC) hB) hA
    _ = 4 * rho ^ n := by ring

end PiMeasure

#print axioms PiMeasure.J534_norm_le
