import SpecialImaginaryPoint.V14119Asymptotic177NumeratorIdentity
import SpecialImaginaryPoint.V14119Asymptotic177Reciprocal

/-!
# Manuscript 14.119 — equation (177), complete quantitative asymptotic

The main theorem below is a uniform inequality with a numerical constant
that implies the manuscript's big-O(x² log(1/x)) for x -> 0+.

It is established from actual sinh/log expressions, the kernel-checked
Taylor bounds and purely algebraic error propagation.
-/

namespace SpecialImaginaryPoint.V14119Asymptotic177

private theorem logarithmic_scale_ge_one
    (t : ℝ) (ht : 0 < t) (htSmall : t ≤ 1 / 4) :
    1 ≤ Real.log (6 / t) := by
  have hlarge : (3 : ℝ) ≤ 6 / t := by
    apply (le_div_iff₀ ht).2
    linarith
  let z : ℝ := 6 / t - 1
  have hz2 : 2 ≤ z := by
    dsimp [z]
    linarith
  have hz0 : 0 ≤ z := by linarith
  have hzpos : 0 < z + 2 := by linarith
  have hsmall : 1 ≤ 2 * z / (z + 2) := by
    apply (le_div_iff₀ hzpos).2
    linarith
  have hlog := Real.le_log_one_add_of_nonneg hz0
  have harg : 1 + z = 6 / t := by dsimp [z]; ring
  rw [harg] at hlog
  exact hsmall.trans hlog

private theorem quotient_from_errors
    (t L N D : ℝ)
    (ht : 0 < t) (htSmall : t ≤ 1 / 4)
    (hL : 1 ≤ L) (hDpos : 0 < D)
    (hN : |N - (L - t / 20)| ≤ t ^ 2 / 100)
    (hR : |1 / D - (6 / t + 1 / 5)| ≤ 2 * t) :
    |N / D - ((6 / t) * L + L / 5 - 3 / 10)| ≤ 3 * t * L := by
  let k : ℝ := 6 / t + 1 / 5
  have htne : t ≠ 0 := ne_of_gt ht
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have ht2le : t ^ 2 ≤ t / 4 := by
    nlinarith [mul_nonneg ht.le (show 0 ≤ 1 / 4 - t by linarith)]
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hcenter : 0 ≤ L - t / 20 := by linarith
  have hNBound : |N| ≤ L + t := by
    have hsplit : N = (N - (L - t / 20)) + (L - t / 20) := by ring
    rw [hsplit]
    calc
      |(N - (L - t / 20)) + (L - t / 20)| ≤
          |N - (L - t / 20)| + |L - t / 20| :=
        abs_add_le _ _
      _ ≤ t ^ 2 / 100 + (L - t / 20) := by
        rw [abs_of_nonneg hcenter]
        linarith [hN]
      _ ≤ L + t := by linarith [ht2le]
  have hterm1 : |N * (1 / D - k)| ≤ 2 * t * (L + t) := by
    rw [abs_mul]
    calc
      |N| * |1 / D - k| ≤ |N| * (2 * t) :=
        mul_le_mul_of_nonneg_left hR (abs_nonneg _)
      _ ≤ (L + t) * (2 * t) :=
        mul_le_mul_of_nonneg_right hNBound (by positivity)
      _ = 2 * t * (L + t) := by ring
  have hterm2 : |k * (N - (L - t / 20))| ≤ t / 10 := by
    rw [abs_mul, abs_of_nonneg hk0]
    calc
      k * |N - (L - t / 20)| ≤ k * (t ^ 2 / 100) :=
        mul_le_mul_of_nonneg_left hN hk0
      _ = 3 * t / 50 + t ^ 2 / 500 := by
        dsimp [k]
        field_simp [htne] <;> ring
      _ ≤ t / 10 := by linarith [ht2le]
  have hid :
      N / D - ((6 / t) * L + L / 5 - 3 / 10) =
        N * (1 / D - k) + k * (N - (L - t / 20)) - t / 100 := by
    dsimp [k]
    field_simp [htne, hDne] <;> ring
  have htri :
      |N * (1 / D - k) + k * (N - (L - t / 20)) - t / 100| ≤
        |N * (1 / D - k)| + |k * (N - (L - t / 20))| + |t / 100| := by
    calc
      |N * (1 / D - k) + k * (N - (L - t / 20)) - t / 100| =
          |(N * (1 / D - k) + k * (N - (L - t / 20))) + (-(t / 100))| := by
            rw [sub_eq_add_neg]
      _ ≤ |N * (1 / D - k) + k * (N - (L - t / 20))| +
            |-(t / 100)| := abs_add_le _ _
      _ ≤ |N * (1 / D - k)| + |k * (N - (L - t / 20))| +
            |t / 100| := by
          rw [abs_neg]
          linarith [abs_add_le (N * (1 / D - k)) (k * (N - (L - t / 20)))]
  have hte : t ≤ t * L :=
    (mul_le_mul_of_nonneg_left hL ht.le).trans_eq (by ring)
  rw [hid]
  calc
    |N * (1 / D - k) + k * (N - (L - t / 20)) - t / 100| ≤
        |N * (1 / D - k)| + |k * (N - (L - t / 20))| + |t / 100| := htri
    _ ≤ 2 * t * (L + t) + t / 10 + t / 100 := by
      rw [abs_of_pos (show 0 < t / 100 by positivity)]
      linarith [hterm1, hterm2]
    _ ≤ 3 * t * L := by nlinarith [ht2le, hte]

theorem parry_index_uniform_L (x : ℝ) (hx : 0 < x) (hxSmall : x ≤ 1 / 2) :
    |Real.log (x / (Real.sinh x - x)) /
        Real.log (Real.sinh x / x) -
      ((6 / x ^ 2) * Real.log (6 / x ^ 2) +
        Real.log (6 / x ^ 2) / 5 - 3 / 10)| ≤
      3 * x ^ 2 * Real.log (6 / x ^ 2) := by
  let t : ℝ := x ^ 2
  let L : ℝ := Real.log (6 / t)
  let N : ℝ := Real.log (x / (Real.sinh x - x))
  let D : ℝ := Real.log (Real.sinh x / x)
  have ht : 0 < t := by dsimp [t]; positivity
  have htSmall : t ≤ 1 / 4 := by
    dsimp [t]
    nlinarith [mul_nonneg hx.le (show 0 ≤ 1 / 2 - x by linarith)]
  have hL : 1 ≤ L := logarithmic_scale_ge_one t ht htSmall
  have hx1 : x ≤ 1 := by linarith
  have hAb := epsilon_positive_enclosure x hx hx1
  have hepspos : 0 < epsilon x :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < x ^ 2 / 6) hAb.1
  have hxne : x ≠ 0 := ne_of_gt hx
  have hratio : Real.sinh x / x = 1 + epsilon x := by
    dsimp [epsilon]
    field_simp [hxne] <;> ring
  have hDpos : 0 < D := by
    dsimp [D]
    rw [hratio]
    exact Real.log_pos (by linarith [hepspos])
  have htpow : t ^ 2 / 100 = x ^ 4 / 100 := by dsimp [t]; ring
  have hN : |N - (L - t / 20)| ≤ t ^ 2 / 100 := by
    rw [htpow]
    exact numerator_log_taylor x hx hx1
  have hR : |1 / D - (6 / t + 1 / 5)| ≤ 2 * t :=
    reciprocal_denominator_taylor x hx hxSmall
  have h := quotient_from_errors t L N D ht htSmall hL hDpos hN hR
  simpa only [t, L, N, D] using h

/-- Exact uniform remainder of formula (177): the explicit constant 9
implies the manuscript's O(x² log(1/x)) as x tends to 0 from above. -/
theorem parry_index_uniform_log_inv (x : ℝ)
    (hx : 0 < x) (hxSmall : x ≤ 1 / 6) :
    |Real.log (x / (Real.sinh x - x)) /
        Real.log (Real.sinh x / x) -
      ((6 / x ^ 2) * Real.log (6 / x ^ 2) +
        Real.log (6 / x ^ 2) / 5 - 3 / 10)| ≤
      9 * x ^ 2 * Real.log (1 / x) := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hinv : (0 : ℝ) < 1 / x := by positivity
  have h6inv : (6 : ℝ) ≤ 1 / x := by
    apply (le_div_iff₀ hx).2
    linarith
  have hlog6 : Real.log (6 : ℝ) ≤ Real.log (1 / x) :=
    Real.log_le_log (by norm_num) h6inv
  have hratio : (6 : ℝ) / x ^ 2 = 6 * (1 / x) ^ 2 := by
    field_simp [hxne] <;> ring
  have hlogid :
      Real.log (6 / x ^ 2) =
        Real.log 6 + 2 * Real.log (1 / x) := by
    rw [hratio, Real.log_mul (by norm_num : (6 : ℝ) ≠ 0)
      (ne_of_gt (pow_pos hinv _)), Real.log_pow]
    ring
  have hlogBound : Real.log (6 / x ^ 2) ≤ 3 * Real.log (1 / x) := by
    rw [hlogid]
    linarith [hlog6]
  have hmul :
      3 * x ^ 2 * Real.log (6 / x ^ 2) ≤
        9 * x ^ 2 * Real.log (1 / x) := by
    nlinarith [mul_nonneg (sq_nonneg x)
      (show 0 ≤ 3 * Real.log (1 / x) - Real.log (6 / x ^ 2) by linarith)]
  exact (parry_index_uniform_L x hx (by linarith)).trans hmul

#print axioms SpecialImaginaryPoint.V14119Asymptotic177.parry_index_uniform_L
#print axioms SpecialImaginaryPoint.V14119Asymptotic177.parry_index_uniform_log_inv

end SpecialImaginaryPoint.V14119Asymptotic177
