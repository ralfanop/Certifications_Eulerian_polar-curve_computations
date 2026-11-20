import Mathlib

/-! M16.6 §14.5 (eq:hol-det), follow-up to #346.
Absolute summability of the paired determinant perturbations.
This treats the positive scalar circle-spectrum factors, not the geometric
operator or the identification of the product with its closed Euler formula. -/
namespace Manuscript16.V166HolonomyPair

noncomputable def pairRatio (a φ n : ℝ) : ℝ :=
  (((n-φ)^2+a^2) * ((-n-φ)^2+a^2)) / (n^2+a^2)^2

noncomputable def pairConstant (a φ : ℝ) : ℝ :=
  2 * φ^2 * (a^2+1) + φ^4

theorem pair_positive (a φ n : ℝ) (ha : 0 < a) :
    0 < pairRatio a φ n := by
  unfold pairRatio
  have h : 0 < a^2 := pow_pos ha 2
  apply div_pos
  · apply mul_pos <;> nlinarith [sq_nonneg (n-φ), sq_nonneg (-n-φ)]
  · apply pow_pos
    nlinarith [sq_nonneg n]

theorem pair_sub_one (a φ n : ℝ) (hn : 1 ≤ n) :
    pairRatio a φ n - 1 =
      (2 * φ^2 * (a^2-n^2) + φ^4) / (n^2+a^2)^2 := by
  have hn0 : 0 < n := by linarith
  have hd : 0 < n^2+a^2 := by positivity
  unfold pairRatio
  field_simp [hd.ne'] <;> ring

theorem pair_constant_nonneg (a φ : ℝ) : 0 ≤ pairConstant a φ := by
  unfold pairConstant
  positivity

theorem pair_deviation_bound (a φ n : ℝ) (hn : 1 ≤ n) :
    |pairRatio a φ n - 1| ≤ pairConstant a φ / n^2 := by
  have hn0 : 0 < n := by linarith
  have hn2 : 1 ≤ n^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ n+1 by linarith)]
  have hφ : 0 ≤ 2 * φ^2 := by positivity
  have ha : 0 ≤ a^2 := sq_nonneg a
  have hφ4 : 0 ≤ φ^4 := by positivity
  have hdiff : |a^2-n^2| ≤ a^2+n^2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg n]
  have hscale : a^2+n^2 ≤ (a^2+1)*n^2 := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hn2)]
  have hnum : |2 * φ^2 * (a^2-n^2) + φ^4| ≤ pairConstant a φ * n^2 := by
    calc
      |2 * φ^2 * (a^2-n^2) + φ^4| ≤
          |2 * φ^2 * (a^2-n^2)| + |φ^4| := abs_add_le _ _
      _ = (2*φ^2)*|a^2-n^2|+φ^4 := by
        rw [abs_mul, abs_of_nonneg hφ, abs_of_nonneg hφ4]
      _ ≤ (2*φ^2)*(a^2+n^2)+φ^4 :=
        add_le_add_right (mul_le_mul_of_nonneg_left hdiff hφ) _
      _ ≤ (2*φ^2)*((a^2+1)*n^2)+φ^4*n^2 :=
        add_le_add (mul_le_mul_of_nonneg_left hscale hφ)
          (by simpa using mul_le_mul_of_nonneg_left hn2 hφ4)
      _ = pairConstant a φ*n^2 := by unfold pairConstant; ring
  rw [pair_sub_one a φ n hn, abs_div, abs_of_nonneg (sq_nonneg _)]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  calc
    |2 * φ^2 * (a^2-n^2) + φ^4| * n^2 ≤
        (pairConstant a φ*n^2)*n^2 :=
      mul_le_mul_of_nonneg_right hnum (sq_nonneg n)
    _ = pairConstant a φ*(n^2)^2 := by ring
    _ ≤ pairConstant a φ*(n^2+a^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (pair_constant_nonneg a φ)
      nlinarith [mul_nonneg ha (show 0 ≤ 2*n^2+a^2 by positivity)]

theorem paired_deviation_summable (a φ : ℝ) :
    Summable (fun n : ℕ => |pairRatio a φ ((n : ℝ)+1) - 1|) := by
  have hp : Summable (fun n : ℕ => 1 / |(n : ℝ)+1| ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ)+1)^2) := by
    convert hp using 1
    funext n
    rw [abs_of_nonneg (by positivity), Real.rpow_two]
  have hc := hs.mul_left (pairConstant a φ)
  have hh : Summable (fun n : ℕ => pairConstant a φ / ((n : ℝ)+1)^2) := by
    simpa only [div_eq_mul_inv, one_mul] using hc
  exact Summable.of_nonneg_of_le (fun n => abs_nonneg _)
    (fun n => pair_deviation_bound a φ _ (by linarith [Nat.cast_nonneg (α := ℝ) n])) hh

#print axioms pair_positive
#print axioms pair_sub_one
#print axioms pair_constant_nonneg
#print axioms pair_deviation_bound
#print axioms paired_deviation_summable
end Manuscript16.V166HolonomyPair
