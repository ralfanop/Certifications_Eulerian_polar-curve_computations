import GegenbauerFock.GegenbauerIntrinsicEntireOutputGram
import GegenbauerFock.GegenbauerIntrinsicEntireGramIdentity
import GegenbauerFock.TwoSidedGramExactOperatorNorm
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# V007 — exact operator norms of the genuine source and holomorphic output Grams

The intrinsic entire Gaussian L² output space is a closed, complete
Hilbert subspace; its Gram operator is defined using the actual Hilbert
adjoint of the ultraspherical-to-Fock transform. Both source and output
Gram norms equal the exact square of the operator norm of that
genuine bounded transform. The source Gram has additionally been
certified equal to the original coefficient-side source Gram.

This is a norm identity of the full Hilbert operators, not a
statement about a finite truncation or an assumed surjectivity.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Both actual Gram Hilbert operators have equal operator norm,
because both are formed from the same genuine bounded analysis map. -/
theorem C_intrinsicEntire_two_gram_exact_operator_norm_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ‖C_intrinsicEntire_gram lam alpha hlam ha‖ =
      ‖C_intrinsicEntire_outputGram lam alpha hlam ha‖ := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  have hsource := ContinuousLinearMap.norm_adjoint_comp_self
    (C_intrinsicEntire lam alpha hlam ha)
  have houtput := ContinuousLinearMap.norm_adjoint_comp_self
    (C_intrinsicEntire lam alpha hlam ha).adjoint
  change ‖C_intrinsicEntire_gram lam alpha hlam ha‖ =
    ‖C_intrinsicEntire lam alpha hlam ha‖ *
      ‖C_intrinsicEntire lam alpha hlam ha‖ at hsource
  simp only [ContinuousLinearMap.adjoint_adjoint,
    LinearIsometryEquiv.norm_map] at houtput
  change ‖C_intrinsicEntire_outputGram lam alpha hlam ha‖ =
    ‖C_intrinsicEntire lam alpha hlam ha‖ *
      ‖C_intrinsicEntire lam alpha hlam ha‖ at houtput
  exact hsource.trans houtput.symm

/-- The true complete analytic Gaussian output Gram has exactly
the squared coefficient-analysis norm, independently of the
representation chosen for its holomorphic codomain. -/
theorem C_intrinsicEntire_outputGram_norm_eq_analysis_norm_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ‖C_intrinsicEntire_outputGram lam alpha hlam ha‖ =
      ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖ := by
  rw [← C_intrinsicEntire_two_gram_exact_operator_norm_eq
    lam alpha hlam ha,
    C_intrinsicEntire_gram_eq lam alpha hlam ha]
  exact sourceGram_norm_eq_analysis_norm_sq lam alpha hlam ha

/-- Both true source/output norms equal the same squared norm of
the original ultraspherical-to-Fock analysis operator. -/
theorem C_intrinsicEntire_two_gram_norms_eq_analysis_norm_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ‖C_intrinsicEntire_gram lam alpha hlam ha‖ =
        ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖ ∧
      ‖C_intrinsicEntire_outputGram lam alpha hlam ha‖ =
        ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖ := by
  constructor
  · rw [C_intrinsicEntire_gram_eq lam alpha hlam ha]
    exact sourceGram_norm_eq_analysis_norm_sq lam alpha hlam ha
  · exact C_intrinsicEntire_outputGram_norm_eq_analysis_norm_sq
      lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_two_gram_exact_operator_norm_eq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_norm_eq_analysis_norm_sq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_two_gram_norms_eq_analysis_norm_sq

end GegenbauerFock.GeneralUltrasphericalFock
