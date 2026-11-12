import SpecialImaginaryPoint.V14119Priority3FredholmQuantitativeReciprocal

/-!
# Priority 3 — a posteriori stability and scalar reciprocal bounds of genuine Fredholm determinants

The ACTUAL universal Hilbert-compression-limit CFC Schatten-S₁
Fredholm determinant f_T(z)=det_F(I+zT) of an arbitrary complex Hilbert
trace-class operator T satisfies a sharp global trace-norm perturbation
estimate E(T,R,z).

Here the certified error estimate yields an a posteriori lower bound
  |f_(T+R)(z)| >= |f_T(z)| - E(T,R,z).
If the certified perturbation error is strictly less than the old
determinant modulus, it also yields a quantitative bound for the new
scalar reciprocal:
  |1/f_(T+R)(z)| <= 1 / (|f_T(z)| - E(T,R,z)).

This remains valid for nonnormal, nonselfadjoint operators and asserts
NO operator-resolvent norm equivalence.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmPerturbationReciprocal

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence

/-- The universal Fredholm determinant of an arbitrarily perturbed
trace-class operator is quantitatively separated from zero by the
OLD determinant modulus minus the exact certified perturbation error. -/
theorem universalFredholm_perturbation_modulus_lower_bound
    (T R : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    ‖fredholmDet T z‖ -
        ((‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖))) ≤
      ‖fredholmDet (T + R) z‖ := by
  have h :=
    fredholmDet_add_traceNorm_bound T R z
  have htri : ‖fredholmDet T z‖ ≤
      ‖fredholmDet (T + R) z - fredholmDet T z‖ +
        ‖fredholmDet (T + R) z‖ := by
    calc
      ‖fredholmDet T z‖ =
          ‖(fredholmDet (T + R) z - fredholmDet T z) -
              fredholmDet (T + R) z‖ := by
        simp
      _ ≤ ‖fredholmDet (T + R) z - fredholmDet T z‖ +
          ‖fredholmDet (T + R) z‖ :=
        norm_sub_le _ _
  linarith

/-- If the trace-norm perturbation bound is below the old genuine
Fredholm determinant modulus, the new SCALAR reciprocal has a
finite explicit computable upper bound. -/
theorem universalFredholm_perturbation_reciprocal_norm_bound
    (T R : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hsmall :
      (‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)) <
        ‖fredholmDet T z‖) :
    ‖(fredholmDet (T + R) z)⁻¹‖ ≤
      1 / (‖fredholmDet T z‖ -
        ((‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)))) := by
  have hdenpos :
      0 < ‖fredholmDet T z‖ -
        ((‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖))) := by
    linarith
  have hden :=
    universalFredholm_perturbation_modulus_lower_bound T R z
  calc
    ‖(fredholmDet (T + R) z)⁻¹‖ =
        1 / ‖fredholmDet (T + R) z‖ := by
      simp only [norm_inv, one_div]
    _ ≤
        1 / (‖fredholmDet T z‖ -
          ((‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)))) :=
      one_div_le_one_div_of_le hdenpos hden

#print axioms Manuscript14Priority3.FredholmPerturbationReciprocal.universalFredholm_perturbation_modulus_lower_bound
#print axioms Manuscript14Priority3.FredholmPerturbationReciprocal.universalFredholm_perturbation_reciprocal_norm_bound

end Manuscript14Priority3.FredholmPerturbationReciprocal
