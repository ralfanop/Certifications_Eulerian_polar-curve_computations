import GegenbauerFock.OutputEntireCoefficientUniqueness

/-!
# V007 — quantitative dense output-range approximation

The actual Gegenbauer–Fock map C : L²(ν_λ) → ℓ² has dense range.
This module turns that certified analytic uniqueness result into
an explicit epsilon-approximation property in the full Fock
coefficient Hilbert space.

The theorem does not assert surjectivity of C or the existence of
a bounded inverse; a compact injective map may have dense,
proper and nonclosed range.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- The actual Fock analysis map has dense range in the *complete*
coefficient Hilbert space. This is the set-valued dense-range
form of the previously proved adjoint-uniqueness theorem. -/
theorem C_denseRange
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    DenseRange (C lam alpha hlam ha) := by
  apply denseRange_iff_closure_range.mpr
  have h := C_dense_range_unconditional lam alpha hlam ha
  have hset := congrArg
    (fun S : Submodule ℂ InfiniteAnalysis.FockCoefficients =>
      (S : Set InfiniteAnalysis.FockCoefficients)) h
  simpa only [Submodule.topologicalClosure_coe,
    Submodule.top_coe, ContinuousLinearMap.range_coe] using hset

/-- Every coefficient-space target F can be approximated arbitrarily
closely by the image of a genuine ultraspherical L² vector. No
surjectivity or positive lower operator-norm bound is assumed. -/
theorem C_approximate_Fock_target
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ f : Lp ℂ 2 (Ultraspherical.measure lam),
      ‖C lam alpha hlam ha f - F‖ < eps := by
  obtain ⟨f, hf⟩ :=
    (C_denseRange lam alpha hlam ha).exists_dist_lt F heps
  refine ⟨f, ?_⟩
  simpa only [dist_eq_norm, norm_sub_rev] using hf

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_denseRange
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_approximate_Fock_target

end GegenbauerFock.GeneralUltrasphericalFock
