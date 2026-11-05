import GegenbauerFock.UltrasphericalPolynomialApproximation

/-!
# V007 — final functional-analytic reduction of weighted polynomial density

This theorem proves, for the ACTUAL Beta-pushforward ultraspherical
probability measure, that uniform complex-polynomial approximation of
bounded continuous functions on [-1,1] forces the span of genuine
weighted-L² Riesz monomials to be dense. It uses no abstract or
finite-rank substitute for the Gegenbauer-Fock transform.

The hypothesis of uniform complex polynomial approximation is stated
explicitly and must subsequently be discharged from the real/imaginary
Stone–Weierstrass approximants; it is NOT declared as an axiom.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- The final analytic implication: complex uniform Weierstrass
approximation on the ultraspherical support, together with the
already certified density of bounded continuous functions in the
actual L², gives density of the original Riesz monomial span. -/
theorem sourceMonomialSpan_dense_of_complexWeierstrass
    (lam : ℝ) (hlam : 0 < lam)
    (hWeier : ∀ (f : BoundedContinuousFunction ℝ ℂ)
      (eps : ℝ), 0 < eps →
        ∃ P : Polynomial ℂ,
          ∀ u ∈ Set.Icc (-1 : ℝ) 1,
            ‖f u - P.eval (u : ℂ)‖ < eps) :
    (sourceMonomialSpan lam hlam).topologicalClosure = ⊤ := by
  let D := sourceMonomialSpan lam hlam
  have hRange :
      Set.range (Ultraspherical.boundedContinuousToLp lam hlam) ⊆
        (D.topologicalClosure : Set (Lp ℂ 2 (Ultraspherical.measure lam))) := by
    rintro y ⟨f, rfl⟩
    change Ultraspherical.boundedContinuousToLp lam hlam f ∈
      closure (D : Set (Lp ℂ 2 (Ultraspherical.measure lam)))
    apply Metric.mem_closure_iff.mpr
    intro eps heps
    obtain ⟨P, hP⟩ := hWeier f (eps / 2) (half_pos heps)
    refine ⟨sourcePolynomial lam hlam P, ?_, ?_⟩
    · exact sourcePolynomial_mem_span lam hlam P
    · rw [dist_eq_norm]
      have hnorm := boundedContinuous_sourcePolynomial_norm_sub_le
        lam hlam f P (eps / 2) (half_pos heps).le
        (fun u hu => (hP u hu).le)
      exact lt_of_le_of_lt hnorm (half_lt_self heps)
  have hDense :
      Set.univ ⊆
        (D.topologicalClosure : Set (Lp ℂ 2 (Ultraspherical.measure lam))) := by
    rw [← (Ultraspherical.boundedContinuous_toLp_denseRange lam hlam).closure_range]
    exact (Submodule.isClosed_topologicalClosure D).closure_subset_iff.mpr hRange
  exact Submodule.eq_top_iff'.mpr fun x => hDense (Set.mem_univ x)

/-- Given uniform polynomial approximation on the compact support,
the true ultraspherical-Fock transform is injective for EVERY α>0. -/
theorem C_injective_of_complexWeierstrass
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (hWeier : ∀ (f : BoundedContinuousFunction ℝ ℂ)
      (eps : ℝ), 0 < eps →
        ∃ P : Polynomial ℂ,
          ∀ u ∈ Set.Icc (-1 : ℝ) 1,
            ‖f u - P.eval (u : ℂ)‖ < eps) :
    Function.Injective (C lam alpha hlam ha) := by
  exact C_injective_of_monomialSpan_dense lam alpha hlam ha
    (sourceMonomialSpan_dense_of_complexWeierstrass lam hlam hWeier)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceMonomialSpan_dense_of_complexWeierstrass
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_injective_of_complexWeierstrass

end GegenbauerFock.GeneralUltrasphericalFock
