import GegenbauerFock.OutputAnalyticCoefficientSeed
import GegenbauerFock.UltrasphericalPolynomialKernel

/-!
# V007 — global Gaussian growth and separation of individual Fock coordinates

These are rigorous prerequisites for the remaining analytic identity theorem.
The first two results control the genuine coherent evaluation on the whole
real axis. The third excludes every nonzero canonical Fock coordinate vector
from the kernel of the actual Hilbert adjoint.

This does NOT establish injectivity on arbitrary infinite coefficient vectors:
a linear combination of nonzero vectors can still lie in the kernel.
-/

noncomputable section

open Set
open scoped ENNReal InnerProduct

namespace GegenbauerFock.FockAnalyticRestriction

/-- Exact global squared operator norm of coherent evaluation on the
imaginary line, with no restriction to the ultraspherical support. -/
theorem evaluation_imaginary_norm_sq
    (alpha : ℝ) (ha : 0 < alpha) (u : ℝ) :
    ‖FockEvaluation.evaluation alpha ha (imaginaryPoint alpha u)‖ ^ 2 =
      Real.exp (u ^ 2 / (4 * alpha)) := by
  rw [FockEvaluation.evaluation_norm_sq,
    norm_imaginaryPoint alpha u ha]
  have hne : alpha ≠ 0 := ne_of_gt ha
  congr 1
  rw [← sq_abs u]
  field_simp
  <;> ring

/-- Sharp Gaussian point-evaluation growth bound for every real u
and every genuine infinite-dimensional ℓ² Fock coefficient vector. -/
theorem norm_evaluate_global_le
    (alpha : ℝ) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients) (u : ℝ) :
    ‖evaluate alpha ha F u‖ ≤
      Real.sqrt (Real.exp (u ^ 2 / (4 * alpha))) * ‖F‖ := by
  have hnorm := evaluation_imaginary_norm_sq alpha ha u
  have hk :
      ‖FockEvaluation.evaluation alpha ha (imaginaryPoint alpha u)‖ ≤
        Real.sqrt (Real.exp (u ^ 2 / (4 * alpha))) := by
    have hp : 0 ≤ Real.exp (u ^ 2 / (4 * alpha)) :=
      Real.exp_nonneg _
    nlinarith [Real.sq_sqrt hp,
      Real.sqrt_nonneg (Real.exp (u ^ 2 / (4 * alpha))),
      norm_nonneg (FockEvaluation.evaluation alpha ha (imaginaryPoint alpha u))]
  calc
    ‖evaluate alpha ha F u‖ ≤
        ‖FockEvaluation.evaluation alpha ha (imaginaryPoint alpha u)‖ *
          ‖F‖ := (FockEvaluation.evaluation alpha ha
            (imaginaryPoint alpha u)).le_opNorm F
    _ ≤ Real.sqrt (Real.exp (u ^ 2 / (4 * alpha))) * ‖F‖ :=
      mul_le_mul_of_nonneg_right hk (norm_nonneg _)

#print axioms GegenbauerFock.FockAnalyticRestriction.evaluation_imaginary_norm_sq
#print axioms GegenbauerFock.FockAnalyticRestriction.norm_evaluate_global_le

end GegenbauerFock.FockAnalyticRestriction

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- No nonzero canonical Fock coordinate vector belongs to the kernel
of the genuine ultraspherical Gegenbauer–Fock Hilbert adjoint. -/
theorem C_adjoint_single_ne_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (n : ℕ) (a : ℂ) (ha0 : a ≠ 0) :
    C_adjoint lam alpha hlam ha (lp.single 2 n a) ≠ 0 := by
  intro hz
  have hzero :=
    (C_adjoint_eq_zero_iff_interior_zero
      lam alpha hlam ha (lp.single 2 n a)).mp hz
  have hu : (1 / 2 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have he := hzero (1 / 2) hu
  change FockEvaluation.evaluation alpha ha
    (FockAnalyticRestriction.imaginaryPoint alpha (1 / 2))
    (lp.single 2 n a) = 0 at he
  rw [FockAnalyticRestriction.evaluation_single_imaginary] at he
  have hw : star (WeightedMoments.complexWeight alpha n) ≠ 0 := by
    simpa using (nonzero_fock_weight alpha ha n)
  have hu0 : ((1 / 2 : ℝ) : ℂ) ^ n ≠ 0 :=
    pow_ne_zero n (by norm_num)
  exact (mul_ne_zero (mul_ne_zero hw ha0) hu0) he

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_single_ne_zero

end GegenbauerFock.GeneralUltrasphericalFock
