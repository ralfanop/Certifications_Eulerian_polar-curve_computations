import SpecialImaginaryPoint.V14119Priority3RelativeUniversalFredholmScalar

/-!
# Priority 3 — quantitative deviation of the genuine relative Fredholm determinant

For any arbitrary complex CFC Schatten-S₁ Hilbert trace-class operators
T and S (including nonnormal/nonselfadjoint), define the actual genuine
Hilbert-compression-limit scalar Fredholm ratio
R_(T,S)(z) = det_F(I+zT) / det_F(I+zS).

At spectral parameters where the reference determinant det_F(I+zS)
does not vanish, the relative scalar ratio obeys the explicit
operatorial trace-norm perturbation estimate
 ‖R_(T,S)(z)-1‖ ≤
   ‖z‖‖T-S‖ exp(‖z‖(‖S‖+‖T-S‖)) / ‖det_F(I+zS)‖.

This connects true relative determinant stability to the independently
certified nonnormal universal Fredholm trace-norm bound; it is NOT an
operator resolvent estimate or a relative zeta determinant identity.
-/

noncomputable section

namespace Manuscript14Priority3.RelativeFredholmTraceNormDeviation

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.RelativeUniversalFredholmScalar

/-- Exact scalar Fredholm relative deviation identity, requiring
only nonvanishing of the reference operator's true determinant. -/
theorem universalFredholmRelativeScalar_sub_one
    (T S : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hS : fredholmDet S z ≠ 0) :
    universalFredholmRelativeScalar T S z - 1 =
      (fredholmDet T z - fredholmDet S z) / fredholmDet S z := by
  unfold universalFredholmRelativeScalar
  field_simp [hS] <;> ring

/-- Dimension-free quantitative trace-norm stability of the TRUE
relative scalar universal CFC-S₁ Fredholm determinant, even for
arbitrary nonnormal and nonselfadjoint Hilbert trace-class operators. -/
theorem universalFredholmRelativeScalar_deviation_norm_le
    (T S : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hS : fredholmDet S z ≠ 0) :
    ‖universalFredholmRelativeScalar T S z - 1‖ ≤
      ((‖z‖ * ‖T - S‖) *
          Real.exp (‖z‖ * (‖S‖ + ‖T - S‖))) /
        ‖fredholmDet S z‖ := by
  have hdiff := fredholmDet_add_traceNorm_bound S (T - S) z
  have heq : S + (T - S) = T := by abel
  rw [heq] at hdiff
  rw [universalFredholmRelativeScalar_sub_one T S z hS, norm_div]
  exact div_le_div_of_nonneg_right hdiff (norm_nonneg _)

#print axioms Manuscript14Priority3.RelativeFredholmTraceNormDeviation.universalFredholmRelativeScalar_sub_one
#print axioms Manuscript14Priority3.RelativeFredholmTraceNormDeviation.universalFredholmRelativeScalar_deviation_norm_le

end Manuscript14Priority3.RelativeFredholmTraceNormDeviation
