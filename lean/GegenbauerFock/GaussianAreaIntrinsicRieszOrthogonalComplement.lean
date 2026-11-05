import GegenbauerFock.GaussianAreaIntrinsicRieszSeparates
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# V007 — trivial orthogonal complement of the genuine intrinsic Riesz span

This assertion is algebraically stronger than pointwise separation but
does not require resolving the full Hilbert-space completeness instance.
The genuine Gaussian-L² Riesz reproducing vectors form a total family:
the orthogonal complement of their complex linear span is trivial.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The orthogonal complement of the complex linear span of the
genuine intrinsic Fock Riesz vectors contains only the zero vector. -/
theorem intrinsicRieszKernel_span_orthogonal_eq_bot
    (alpha : ℝ) (ha : 0 < alpha) :
    (Submodule.span ℂ (Set.range (intrinsicRieszKernel alpha ha)))ᗮ =
      (⊥ : Submodule ℂ (entireGaussianL2Submodule alpha)) := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hzero : x = 0 := by
    apply (intrinsicRieszKernel_pairings_zero_iff alpha ha x).mp
    intro z
    have hmem : intrinsicRieszKernel alpha ha z ∈
        Submodule.span ℂ (Set.range (intrinsicRieszKernel alpha ha)) :=
      Submodule.subset_span ⟨z, rfl⟩
    exact hx _ hmem
  exact (Submodule.mem_bot ℂ).mpr hzero

#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_span_orthogonal_eq_bot

end GegenbauerFock.GaussianArea
