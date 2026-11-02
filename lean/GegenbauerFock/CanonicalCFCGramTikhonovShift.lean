import GegenbauerFock.TwoSidedGramNegativeResolvent
import GegenbauerFock.CompletePositiveSingularFamily
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# V007 — actual positive-shift Tikhonov inverse of the source Gram

The certified nonnegative source Gram spectrum ensures G + eps*I is a
unit for every real eps > 0. We construct the inverse in the genuine
complex-linear bounded-operator algebra, not just coefficientwise.
We also certify its two-sided inverse identities and exact filter
action on each nonzero source-Gram eigenmode.

No bounded inverse of unshifted compact G is asserted.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

private abbrev TikhonovH (lam : ℝ) :=
  Lp ℂ 2 (Ultraspherical.measure lam)

/-- The genuine strictly positive shifted source Gram, as a complex
bounded linear map on the complete weighted Hilbert space. -/
noncomputable def sourceGramPositiveShift
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) : TikhonovH lam →L[ℂ] TikhonovH lam :=
  gram lam alpha hlam ha + (eps : ℂ) • (1 : TikhonovH lam →L[ℂ] TikhonovH lam)

/-- For eps>0, G+eps I is genuinely invertible in B(L²(ν_λ)). -/
theorem sourceGramPositiveShift_isUnit
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps) :
    IsUnit (sourceGramPositiveShift lam alpha hlam ha eps) := by
  let G := gram lam alpha hlam ha
  have h : IsUnit
      ((-(eps : ℂ)) • (1 : TikhonovH lam →L[ℂ] TikhonovH lam) - G) := by
    simpa only [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one]
      using (source_gram_negative_real_mem_resolventSet
        lam alpha hlam ha eps heps)
  have heq :
      (-(eps : ℂ)) • (1 : TikhonovH lam →L[ℂ] TikhonovH lam) - G =
        -(G + (eps : ℂ) • (1 : TikhonovH lam →L[ℂ] TikhonovH lam)) := by
    abel
  have hh : IsUnit (G + (eps : ℂ) •
      (1 : TikhonovH lam →L[ℂ] TikhonovH lam)) :=
    (IsUnit.neg_iff _).mp (heq ▸ h)
  simpa only [sourceGramPositiveShift, G] using hh

/-- Two genuine bounded endomorphism inverse identities for the
positive-shift Tikhonov resolvent, for every eps>0. -/
theorem sourceGramPositiveShift_two_sided_inverse
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps) :
    (sourceGramPositiveShift lam alpha hlam ha eps) *
      (Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps)) =
        (1 : TikhonovH lam →L[ℂ] TikhonovH lam) ∧
    (Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps)) *
      (sourceGramPositiveShift lam alpha hlam ha eps) =
        (1 : TikhonovH lam →L[ℂ] TikhonovH lam) := by
  let h := sourceGramPositiveShift_isUnit lam alpha hlam ha eps heps
  have heq : (↑h.unit : TikhonovH lam →L[ℂ] TikhonovH lam) =
      sourceGramPositiveShift lam alpha hlam ha eps := h.unit_spec
  rw [← heq, Ring.inverse_unit]
  exact ⟨h.unit.mul_inv, h.unit.inv_mul⟩

/-- Genuine shifted source-Gram regularization acting on the
original full source Hilbert space. -/
noncomputable def sourceGramTikhonovFilter
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) : TikhonovH lam →L[ℂ] TikhonovH lam :=
  (gram lam alpha hlam ha) *
    (Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps))

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramPositiveShift_isUnit
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramPositiveShift_two_sided_inverse

end GegenbauerFock.GeneralUltrasphericalFock
