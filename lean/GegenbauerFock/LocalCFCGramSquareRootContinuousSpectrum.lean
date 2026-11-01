import GegenbauerFock.LocalCFCGramSquareRoot
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# V007 — continuous-spectrum zero for the named canonical CFC Gram root

The exported operator localCFCGramSqrt, with its real CFC scalar
instances discharged inside its definition, is a compact injective map
with dense nonclosed image. Hence zero is spectral but not an eigenvalue.

Unlike the earlier raw CFC formulation, the present statement needs no
locally installed algebra classes at the calling site.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The named, actual canonical CFC Gram square root has zero in its
continuous spectrum: zero belongs to the spectrum, while its kernel
vanishes and its range is dense. -/
theorem local_cfc_gram_sqrt_zero_continuous_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (0 : ℂ) ∈ spectrum ℂ (localCFCGramSqrt lam alpha hlam ha) ∧
    (localCFCGramSqrt lam alpha hlam ha).ker = ⊥ ∧
    (localCFCGramSqrt lam alpha hlam ha).range.topologicalClosure =
      (⊤ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
  classical
  obtain ⟨W, hcompact, hinj, hdense, hnotclosed, hC⟩ :=
    exists_local_cfc_sqrt_compact_dense_nonclosed lam alpha hlam ha
  let P := localCFCGramSqrt lam alpha hlam ha
  have hnotSurj : ¬ Function.Surjective P := by
    intro hsurj
    have hrange :
        P.range = (⊤ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :=
      LinearMap.range_eq_top.mpr hsurj
    have hclosed : IsClosed (P.range : Set (Lp ℂ 2 (Ultraspherical.measure lam))) := by
      rw [hrange]
      exact isClosed_univ
    exact hnotclosed hclosed
  have hzero : (0 : ℂ) ∈ spectrum ℂ P := by
    apply spectrum.zero_mem ℂ
    intro hunit
    exact hnotSurj (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).2
  have hker : P.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  exact ⟨hzero, hker, hdense⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.local_cfc_gram_sqrt_zero_continuous_spectrum

end GegenbauerFock.GeneralUltrasphericalFock
