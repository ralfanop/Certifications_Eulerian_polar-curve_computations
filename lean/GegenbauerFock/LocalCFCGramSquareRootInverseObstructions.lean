import GegenbauerFock.LocalCFCGramSquareRoot
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# V007 — intrinsic inverse obstructions for the exported CFC root

The named operator localCFCGramSqrt has compact, injective,
dense and nonclosed range in the actual ultraspherical Hilbert space.
This immediately rules out both surjectivity and a uniform
anti-Lipschitz estimate, without requiring CFC algebra instances
from callers or postulating an inverse operator.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The exported canonical Gram root is neither surjective nor
anti-Lipschitz with any finite nonnegative constant. -/
theorem local_cfc_gram_sqrt_not_surjective_and_not_antilipschitz
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ Function.Surjective (localCFCGramSqrt lam alpha hlam ha) ∧
    ¬ ∃ K : NNReal, AntilipschitzWith K
      (localCFCGramSqrt lam alpha hlam ha) := by
  classical
  obtain ⟨W, hcompact, hinj, hdense, hnotclosed, hC⟩ :=
    exists_local_cfc_sqrt_compact_dense_nonclosed lam alpha hlam ha
  constructor
  · intro hsurj
    have htop :
        (localCFCGramSqrt lam alpha hlam ha).range =
          (⊤ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :=
      LinearMap.range_eq_top.mpr hsurj
    apply hnotclosed
    rw [htop]
    exact isClosed_univ
  · intro hbound
    have hclosed :=
      ((localCFCGramSqrt lam alpha hlam ha).isClosed_range_iff_antilipschitz_of_injective
        hinj).mpr hbound
    apply hnotclosed
    simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using hclosed

#print axioms GegenbauerFock.GeneralUltrasphericalFock.local_cfc_gram_sqrt_not_surjective_and_not_antilipschitz

end GegenbauerFock.GeneralUltrasphericalFock
