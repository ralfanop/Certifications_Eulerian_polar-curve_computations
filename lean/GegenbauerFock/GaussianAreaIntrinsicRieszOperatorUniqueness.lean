import GegenbauerFock.GaussianAreaIntrinsicRieszDenseSpan
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# V007 — bounded operators on intrinsic Fock are determined by coherent vectors

The complete family of genuine Gaussian-L² Riesz coherent vectors has
dense complex linear span. Therefore any two bounded complex-linear
operators out of intrinsic Bargmann–Fock into a normed complex target
coincide as soon as they agree on all coherent reproducing vectors.

This is a consequence of the independently kernel-certified Hilbert
density theorem, and it applies to the full intrinsic holomorphic
Gaussian-L² space rather than only the polynomial span.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Any continuous complex-linear operators on the complete intrinsic
Gaussian Fock Hilbert space that agree on every reproducing coherent
vector must agree identically on all holomorphic Gaussian-L² classes. -/
theorem intrinsicRieszKernel_continuousLinearMap_ext
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (alpha : ℝ) (ha : 0 < alpha)
    (T U : entireGaussianL2Submodule alpha →L[ℂ] E)
    (h : ∀ z : ℂ,
      T (intrinsicRieszKernel alpha ha z) =
        U (intrinsicRieszKernel alpha ha z)) :
    T = U := by
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (intrinsicRieszKernel_span_dense alpha ha))
  rintro _ ⟨z, rfl⟩
  exact h z

#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_continuousLinearMap_ext

end GegenbauerFock.GaussianArea
