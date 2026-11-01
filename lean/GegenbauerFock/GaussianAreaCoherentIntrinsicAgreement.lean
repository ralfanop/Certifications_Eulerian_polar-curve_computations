import GegenbauerFock.GaussianAreaCoherentSeriesAe
import GegenbauerFock.GaussianAreaProjectedPointEvaluation

/-!
# V007 — intrinsic entire Gaussian representative agrees with coherent synthesis

The already-certified a.e. identification of L² synthesis with the entire
coherent series, combined with full support of Gaussian area measure,
identifies the intrinsic entire representative POINTWISE with coherent
Fock evaluation. Thus on the genuine closed polynomial span, intrinsic
point evaluation is the restriction of the bounded ambient projected
evaluation. This is stronger than the earlier finite-polynomial result.

It does not assert the reverse inclusion of all entire Gaussian L²
classes in the polynomial closure; analytic polynomial density and
surjectivity onto the full intrinsic Bargmann–Fock space remain open.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Canonical intrinsic analytic class of a synthesized ℓ² coefficient
vector, using its genuinely entire almost-everywhere representative. -/
noncomputable def synthesizedIntrinsicVector
    (alpha : ℝ) (ha : 0 < alpha)
    (a : lp (fun _ : ℕ => ℂ) 2) :
    entireGaussianL2Submodule alpha :=
  ⟨coefficientSynthesisL2 alpha ha a,
    coefficientSynthesisL2_mem_entireGaussianL2Submodule alpha ha a⟩

/-- The unique intrinsic entire representative of a synthesized
Gaussian L² vector is the coherent Fock series at EVERY complex point. -/
theorem entireRepresentative_synthesized
    (alpha : ℝ) (ha : 0 < alpha)
    (a : lp (fun _ : ℕ => ℂ) 2) :
    entireRepresentative alpha (synthesizedIntrinsicVector alpha ha a) =
      (fun z : ℂ => FockEvaluation.evaluation alpha ha z a) := by
  apply entireGaussianRepresentative_unique alpha ha
    (coefficientSynthesisL2 alpha ha a)
  · exact entireRepresentative_differentiable alpha _
  · exact FockEvaluation.differentiable_evaluation_complex alpha ha a
  · exact entireRepresentative_ae alpha _
  · exact (coefficientSynthesisL2_ae_coherentEvaluation alpha ha a).symm

/-- Intrinsic entire evaluation of a synthesized vector equals the
Hilbert coefficient-space coherent evaluation pointwise. -/
theorem intrinsicEntireEvaluation_synthesized
    (alpha : ℝ) (ha : 0 < alpha)
    (a : lp (fun _ : ℕ => ℂ) 2) (z : ℂ) :
    intrinsicEntireEvaluation alpha ha z
      (synthesizedIntrinsicVector alpha ha a) =
        FockEvaluation.evaluation alpha ha z a := by
  exact congrFun (entireRepresentative_synthesized alpha ha a) z

/-- Intrinsic entire point evaluation and the ambient bounded
projected evaluation coincide on the FULL CLOSED polynomial span,
not merely on its algebraic finite-polynomial subspace. -/
theorem intrinsicEntireEvaluation_eq_projected_on_polynomialClosure
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha))
    (hx : x ∈ gaussianPolynomialClosure alpha ha) :
    intrinsicEntireEvaluation alpha ha z
      (⟨x, gaussianPolynomialClosure_le_entireGaussianL2Submodule
        alpha ha hx⟩ : entireGaussianL2Submodule alpha) =
      projectedGaussianEvaluation alpha ha z x := by
  have hxrange :
      x ∈ LinearMap.range (coefficientSynthesisL2 alpha ha).toLinearMap := by
    rw [coefficientSynthesisL2_range_eq_closure_span alpha ha]
    exact hx
  obtain ⟨a, rfl⟩ := hxrange
  change intrinsicEntireEvaluation alpha ha z
    (synthesizedIntrinsicVector alpha ha a) =
      projectedGaussianEvaluation alpha ha z
        (coefficientSynthesisL2 alpha ha a)
  exact (intrinsicEntireEvaluation_synthesized alpha ha a z).trans
    (projectedGaussianEvaluation_synthesis alpha ha z a).symm

/-- True analytic evaluation on the closed polynomial span obeys the
coherent-state bound with the genuine Gaussian L² norm. -/
theorem intrinsicEntireEvaluation_norm_le_on_polynomialClosure
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha))
    (hx : x ∈ gaussianPolynomialClosure alpha ha) :
    ‖intrinsicEntireEvaluation alpha ha z
      (⟨x, gaussianPolynomialClosure_le_entireGaussianL2Submodule
        alpha ha hx⟩ : entireGaussianL2Submodule alpha)‖ ≤
      ‖FockEvaluation.evaluation alpha ha z‖ * ‖x‖ := by
  rw [intrinsicEntireEvaluation_eq_projected_on_polynomialClosure
    alpha ha z x hx]
  exact projectedGaussianEvaluation_norm_le alpha ha z x

#print axioms GegenbauerFock.GaussianArea.entireRepresentative_synthesized
#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluation_synthesized
#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluation_eq_projected_on_polynomialClosure
#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluation_norm_le_on_polynomialClosure

end GegenbauerFock.GaussianArea
