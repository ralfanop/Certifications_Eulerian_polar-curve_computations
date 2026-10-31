import GegenbauerFock.GaussianAreaIntrinsicRieszExactGramScalar
import Mathlib.Analysis.Complex.Norm

/-!
# Strict two-point Gaussian Bargmann–Fock Gram determinant

For positive Gaussian width, the two-point exponential Gram determinant
is strictly positive precisely when the evaluation points are distinct.
The proof uses the exact complex norm of the exponential and the
complex polarization identity, rather than assuming strictness in
the Cauchy–Schwarz inequality.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Two distinct evaluation points have a strictly positive
two-by-two Gaussian Fock Gram determinant. -/
theorem intrinsicRieszKernel_exp_twoPoint_determinant_pos
    (alpha : ℝ) (ha : 0 < alpha) (z w : ℂ) (hzw : z ≠ w) :
    0 < Real.exp (alpha * ‖z‖ ^ 2) *
        Real.exp (alpha * ‖w‖ ^ 2) -
        ‖Complex.exp ((alpha : ℂ) * z * star w)‖ ^ 2 := by
  have hdiff : 0 < ‖z - w‖ ^ 2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzw))
  have hpolar :
      ‖z - w‖ ^ 2 =
        ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * (z * star w).re := by
    calc
      ‖z - w‖ ^ 2 = Complex.normSq (z - w) := Complex.sq_norm _
      _ = Complex.normSq z + Complex.normSq w -
          2 * (z * star w).re := by
            simpa using (Complex.normSq_sub z w)
      _ = ‖z‖ ^ 2 + ‖w‖ ^ 2 -
          2 * (z * star w).re := by
            simp only [Complex.normSq_eq_norm_sq]
  have hre :
      ((alpha : ℂ) * z * star w).re =
        alpha * (z * star w).re := by
    rw [mul_assoc]
    simp [Complex.mul_re]
  have hpositive :
      0 < alpha * (‖z‖ ^ 2 + ‖w‖ ^ 2 -
        2 * (z * star w).re) := by
    rw [← hpolar]
    exact mul_pos ha hdiff
  have hstrict :
      2 * ((alpha : ℂ) * z * star w).re <
        alpha * ‖z‖ ^ 2 + alpha * ‖w‖ ^ 2 := by
    rw [hre]
    nlinarith [hpositive]
  have hexp :
      Real.exp (2 * ((alpha : ℂ) * z * star w).re) <
        Real.exp (alpha * ‖z‖ ^ 2 + alpha * ‖w‖ ^ 2) :=
    Real.exp_lt_exp.mpr hstrict
  have hnorm :
      ‖Complex.exp ((alpha : ℂ) * z * star w)‖ ^ 2 =
        Real.exp (2 * ((alpha : ℂ) * z * star w).re) := by
    rw [Complex.norm_exp]
    calc
      Real.exp (((alpha : ℂ) * z * star w).re) ^ 2 =
          Real.exp (((alpha : ℂ) * z * star w).re) *
          Real.exp (((alpha : ℂ) * z * star w).re) := by ring
      _ = Real.exp (((alpha : ℂ) * z * star w).re +
          ((alpha : ℂ) * z * star w).re) :=
            (Real.exp_add _ _).symm
      _ = Real.exp (2 * ((alpha : ℂ) * z * star w).re) := by
            congr 1
            ring
  apply sub_pos.mpr
  calc
    ‖Complex.exp ((alpha : ℂ) * z * star w)‖ ^ 2 =
      Real.exp (2 * ((alpha : ℂ) * z * star w).re) := hnorm
    _ < Real.exp (alpha * ‖z‖ ^ 2 +
      alpha * ‖w‖ ^ 2) := hexp
    _ = Real.exp (alpha * ‖z‖ ^ 2) *
      Real.exp (alpha * ‖w‖ ^ 2) :=
        (Real.exp_add _ _).symm

/-- The two-point Gaussian Fock Gram determinant vanishes exactly
when the two evaluation nodes coincide. -/
theorem intrinsicRieszKernel_exp_twoPoint_determinant_eq_zero_iff
    (alpha : ℝ) (ha : 0 < alpha) (z w : ℂ) :
    Real.exp (alpha * ‖z‖ ^ 2) *
        Real.exp (alpha * ‖w‖ ^ 2) -
        ‖Complex.exp ((alpha : ℂ) * z * star w)‖ ^ 2 = 0 ↔
      z = w := by
  constructor
  · intro hd
    by_contra hne
    have hp := intrinsicRieszKernel_exp_twoPoint_determinant_pos
      alpha ha z w hne
    rw [hd] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  · intro heq
    subst w
    rw [intrinsicRieszKernel_exp_diagonal alpha ha z]
    rw [Complex.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
    ring

/-- A two-point Gaussian Fock Gram matrix is strictly positive
if and only if its two nodes are distinct. -/
theorem intrinsicRieszKernel_exp_twoPoint_determinant_pos_iff
    (alpha : ℝ) (ha : 0 < alpha) (z w : ℂ) :
    0 < Real.exp (alpha * ‖z‖ ^ 2) *
        Real.exp (alpha * ‖w‖ ^ 2) -
        ‖Complex.exp ((alpha : ℂ) * z * star w)‖ ^ 2 ↔
      z ≠ w := by
  constructor
  · intro hp heq
    have hz := (intrinsicRieszKernel_exp_twoPoint_determinant_eq_zero_iff
      alpha ha z w).mpr heq
    rw [hz] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  · exact intrinsicRieszKernel_exp_twoPoint_determinant_pos alpha ha z w

#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_twoPoint_determinant_pos
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_twoPoint_determinant_eq_zero_iff
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_twoPoint_determinant_pos_iff

end GegenbauerFock.GaussianArea
