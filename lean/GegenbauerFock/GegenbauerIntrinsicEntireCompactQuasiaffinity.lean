import GegenbauerFock.GegenbauerIntrinsicEntireFockOperator
import GegenbauerFock.CompactFockProperDenseRange
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# V007 — genuine ultraspherical-to-entire-Gaussian Fock compact quasiaffinity

The independently established surjective Hilbert isometry identifies
the full Fock coefficient space with the actual closed intrinsic
entire Gaussian L² subspace. We transfer compactness, operator norm,
and failure of surjectivity of the ultraspherical integral transform
to this genuine holomorphic function-space codomain.

The onto Fock *coefficient isometry* must not be confused with the
non-surjective compact *ultraspherical transform*. The latter is an
injective compact operator into an infinite-dimensional analytic space.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The actual ultraspherical transform into intrinsic holomorphic
Gaussian L² is compact, not merely the coefficient-space model. -/
theorem C_intrinsicEntire_compact
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    IsCompactOperator (C_intrinsicEntire lam alpha hlam ha) := by
  have hcompact := (C_compact lam alpha hlam ha).clm_comp
    (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).toLinearIsometry.toContinuousLinearMap
  exact hcompact

/-- Passage from ℓ² to the complete Gaussian entire Hilbert space
preserves the exact bounded operator norm of the ultraspherical map. -/
theorem C_intrinsicEntire_opNorm_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ‖C_intrinsicEntire lam alpha hlam ha‖ =
      ‖C lam alpha hlam ha‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound
      (C_intrinsicEntire lam alpha hlam ha)
      (norm_nonneg (C lam alpha hlam ha))
    intro f
    calc
      ‖C_intrinsicEntire lam alpha hlam ha f‖ =
          ‖C lam alpha hlam ha f‖ :=
        C_intrinsicEntire_norm lam alpha hlam ha f
      _ ≤ ‖C lam alpha hlam ha‖ * ‖f‖ :=
        (C lam alpha hlam ha).le_opNorm _
  · have hbound : ∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
        ‖C lam alpha hlam ha f‖ ≤
          ‖C_intrinsicEntire lam alpha hlam ha‖ * ‖f‖ := by
      intro f
      calc
        ‖C lam alpha hlam ha f‖ =
            ‖C_intrinsicEntire lam alpha hlam ha f‖ :=
          (C_intrinsicEntire_norm lam alpha hlam ha f).symm
        _ ≤ ‖C_intrinsicEntire lam alpha hlam ha‖ * ‖f‖ :=
          (C_intrinsicEntire lam alpha hlam ha).le_opNorm _
    exact ContinuousLinearMap.opNorm_le_bound
      (C lam alpha hlam ha)
      (show 0 ≤ ‖C_intrinsicEntire lam alpha hlam ha‖ from
        norm_nonneg (C_intrinsicEntire lam alpha hlam ha))
      hbound

/-- The compact ultraspherical transform does NOT become surjective
when its true analytic function-space codomain replaces ℓ². -/
theorem C_intrinsicEntire_not_surjective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ Function.Surjective (C_intrinsicEntire lam alpha hlam ha) := by
  intro hsurj
  apply C_not_surjective lam alpha hlam ha
  intro a
  obtain ⟨f, hf⟩ :=
    hsurj (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha a)
  refine ⟨f, ?_⟩
  apply (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).injective
  simpa only [C_intrinsicEntire_apply] using hf

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_compact
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_opNorm_eq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_not_surjective

end GegenbauerFock.GeneralUltrasphericalFock
