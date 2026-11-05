import GegenbauerFock.TwoSidedGramSpectrumEquality
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# V007 — exact operator norm equality of the two true Grams

For the genuine Gegenbauer–Fock analysis operator C between the
ultraspherical L² Hilbert space and the full coefficient Hilbert
space, the C-star identity gives

  ‖C†C‖ = ‖CC†‖ = ‖C‖ * ‖C‖.

The two underlying Hilbert spaces remain distinct. This operator
norm equality is stronger than the earlier common-spectral upper
bound involving the minimum of the two operator norms; it is
independent of finite spectral truncations and eigenvalue estimates.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Exact norm-square identity for the concrete source Gram. -/
theorem sourceGram_norm_eq_analysis_norm_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ‖gram lam alpha hlam ha‖ =
      ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖ := by
  change ‖(C lam alpha hlam ha).adjoint ∘L
    (C lam alpha hlam ha)‖ = _
  exact ContinuousLinearMap.norm_adjoint_comp_self
    (C lam alpha hlam ha)

/-- The coefficient-side Gram has the same exact squared analysis norm. -/
theorem outputGram_norm_eq_analysis_norm_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ‖outputGram lam alpha hlam ha‖ =
      ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖ := by
  have h := ContinuousLinearMap.norm_adjoint_comp_self
    (C lam alpha hlam ha).adjoint
  change ‖(C lam alpha hlam ha).adjoint.adjoint ∘L
    (C lam alpha hlam ha).adjoint‖ =
      ‖(C lam alpha hlam ha).adjoint‖ *
        ‖(C lam alpha hlam ha).adjoint‖ at h
  simp only [ContinuousLinearMap.adjoint_adjoint,
    LinearIsometryEquiv.norm_map] at h
  change ‖(C lam alpha hlam ha) ∘L
    (C lam alpha hlam ha).adjoint‖ = _
  exact h

/-- The operator norms of C†C and CC† agree exactly, even though
the source and output Hilbert spaces are not identified. -/
theorem two_sided_gram_exact_operator_norm_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ‖gram lam alpha hlam ha‖ =
      ‖outputGram lam alpha hlam ha‖ := by
  rw [sourceGram_norm_eq_analysis_norm_sq,
    outputGram_norm_eq_analysis_norm_sq]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_norm_eq_analysis_norm_sq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_norm_eq_analysis_norm_sq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_exact_operator_norm_eq

end GegenbauerFock.GeneralUltrasphericalFock
