import GegenbauerFock.GaussianAreaPolynomialClosureEquiv
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# V007 — polynomial closure by vanishing Gaussian holomorphic moments

An ambient Gaussian L² vector is orthogonal to the actual closed
holomorphic polynomial span precisely when each normalized monomial
moment vanishes. In that closed span, the moments separate points.

This gives a rigorous formulation of the analytic density obligation:
to identify the entire-representative Fock space with the polynomial
closure, one must exclude entire L² vectors with all monomial moments
zero (and justify the required analytic closure arguments).

No analytic polynomial density or onto full Bargmann–Fock claim is
assumed or made here.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Exact orthogonal-complement criterion for the closed polynomial
span inside the genuinely weighted Gaussian L² space. -/
theorem mem_gaussianPolynomialClosure_orthogonal_iff
    (alpha : ℝ) (ha : 0 < alpha)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) :
    x ∈ (gaussianPolynomialClosure alpha ha)ᗮ ↔
      ∀ n : ℕ,
        inner ℂ (normalizedMonomialL2Vector alpha ha n) x = 0 := by
  constructor
  · intro hx n
    apply (Submodule.mem_orthogonal _ x).mp hx
    change normalizedMonomialL2Vector alpha ha n ∈
      (Submodule.span ℂ (Set.range
        (fun k : ℕ => normalizedMonomialL2Vector alpha ha k))).topologicalClosure
    exact (Submodule.le_topologicalClosure _)
      (Submodule.subset_span (Set.mem_range_self n))
  · intro hx
    change x ∈ ((Submodule.span ℂ (Set.range
      (fun k : ℕ => normalizedMonomialL2Vector alpha ha k))).topologicalClosure)ᗮ
    rw [Submodule.orthogonal_closure]
    have hspan :
        Submodule.span ℂ (Set.range
          (fun k : ℕ => normalizedMonomialL2Vector alpha ha k)) ≤
        (ℂ ∙ x)ᗮ := by
      apply Submodule.span_le.mpr
      rintro y ⟨n, rfl⟩
      exact (Submodule.mem_orthogonal_singleton_iff_inner_left).2 (hx n)
    exact (Submodule.mem_orthogonal _ x).2 (by
      intro y hy
      exact (Submodule.mem_orthogonal_singleton_iff_inner_left).1
        (hspan hy))

/-- No nonzero vector of the closed Gaussian holomorphic polynomial
span can have all its normalized monomial moments equal to zero. -/
theorem gaussianPolynomialClosure_eq_zero_of_all_moments_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (x : gaussianPolynomialClosure alpha ha)
    (hx : ∀ n : ℕ,
      inner ℂ (normalizedMonomialL2Vector alpha ha n)
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) = 0) :
    x = 0 := by
  have horth :
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) ∈
        (gaussianPolynomialClosure alpha ha)ᗮ :=
    (mem_gaussianPolynomialClosure_orthogonal_iff alpha ha
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha))).2 hx
  have hz :
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) ∈
        (gaussianPolynomialClosure alpha ha) ⊓
        (gaussianPolynomialClosure alpha ha)ᗮ :=
    ⟨x.property, horth⟩
  have hxzero : (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) = 0 := by
    simpa [(gaussianPolynomialClosure alpha ha).inf_orthogonal_eq_bot] using hz
  exact Subtype.ext hxzero

#print axioms GegenbauerFock.GaussianArea.mem_gaussianPolynomialClosure_orthogonal_iff
#print axioms GegenbauerFock.GaussianArea.gaussianPolynomialClosure_eq_zero_of_all_moments_zero

end GegenbauerFock.GaussianArea
