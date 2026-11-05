import GegenbauerFock.GegenbauerIntrinsicEntireTwoGramExactOperatorNorm
import GegenbauerFock.GegenbauerIntrinsicEntireFockOperator

/-!
# V007 — exact norm of the intrinsic entire-Gaussian analysis transform

The actual Gegenbauer analysis map into the closed holomorphic Gaussian
L² subspace is the composition of the coefficient analysis operator
with a proven onto linear isometry. Its operator norm therefore agrees
exactly with that of the coefficient map. Both genuine Hilbert Grams
have operator norms equal to the square of this ORIGINAL analytic
transform's norm; there is no claim that the compact transform is
surjective and no finite-section or matrix approximation.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Passing from infinite coefficients to their actual Gaussian L²
entire-function realization preserves the full operator norm of the
ultraspherical analysis transform. -/
theorem C_intrinsicEntire_operator_norm_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ‖C_intrinsicEntire lam alpha hlam ha‖ =
      ‖C lam alpha hlam ha‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _
      (norm_nonneg (C lam alpha hlam ha))
    intro f
    rw [C_intrinsicEntire_norm lam alpha hlam ha]
    exact (C lam alpha hlam ha).le_opNorm f
  · apply ContinuousLinearMap.opNorm_le_bound _
      (norm_nonneg (C_intrinsicEntire lam alpha hlam ha))
    intro f
    rw [← C_intrinsicEntire_norm lam alpha hlam ha]
    exact (C_intrinsicEntire lam alpha hlam ha).le_opNorm f

/-- The true Gaussian Fock OUTPUT Gram has the exact squared norm
of the actual ultraspherical-to-entire-Gaussian operator itself. -/
theorem C_intrinsicEntire_outputGram_norm_eq_intrinsic_operator_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ‖C_intrinsicEntire_outputGram lam alpha hlam ha‖ =
      ‖C_intrinsicEntire lam alpha hlam ha‖ *
        ‖C_intrinsicEntire lam alpha hlam ha‖ := by
  rw [C_intrinsicEntire_outputGram_norm_eq_analysis_norm_sq
    lam alpha hlam ha, C_intrinsicEntire_operator_norm_eq lam alpha hlam ha]

/-- The same exact intrinsic analysis-norm-square identity holds
simultaneously on both TRUE distinct Hilbert-space Gram operators. -/
theorem C_intrinsicEntire_both_gram_norms_eq_intrinsic_operator_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ‖C_intrinsicEntire_gram lam alpha hlam ha‖ =
        ‖C_intrinsicEntire lam alpha hlam ha‖ *
          ‖C_intrinsicEntire lam alpha hlam ha‖ ∧
      ‖C_intrinsicEntire_outputGram lam alpha hlam ha‖ =
        ‖C_intrinsicEntire lam alpha hlam ha‖ *
          ‖C_intrinsicEntire lam alpha hlam ha‖ := by
  constructor
  · rw [C_intrinsicEntire_gram_eq lam alpha hlam ha,
      sourceGram_norm_eq_analysis_norm_sq lam alpha hlam ha,
      C_intrinsicEntire_operator_norm_eq lam alpha hlam ha]
  · exact C_intrinsicEntire_outputGram_norm_eq_intrinsic_operator_sq
      lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_operator_norm_eq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_norm_eq_intrinsic_operator_sq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_both_gram_norms_eq_intrinsic_operator_sq

end GegenbauerFock.GeneralUltrasphericalFock
