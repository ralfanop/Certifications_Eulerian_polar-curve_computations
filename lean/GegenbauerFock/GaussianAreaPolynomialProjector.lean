import GegenbauerFock.GaussianAreaCoefficientAnalysisAdjoint

/-!
# V007 — canonical Hilbert projection onto Gaussian holomorphic polynomials

Synthesis S : ℓ² → L² is an isometry and analysis A := S† is its
Hilbert adjoint. Their composition P := S ∘ A is the canonical
idempotent projection onto the closed Gaussian polynomial span.

The residual x - P x is orthogonal to that span, by the exact
moment/adjoint-kernel criterion. This identifies the precise analytic
obstruction to proving that the independently defined entire Gaussian
L² submodule is exhausted by polynomial synthesis.

No full onto holomorphic Bargmann–Fock assertion is used here.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The actual continuous complex-linear polynomial projector on all
Gaussian weighted L², constructed from synthesis and its Hilbert adjoint. -/
noncomputable def gaussianPolynomialProjector
    (alpha : ℝ) (ha : 0 < alpha) :
    Lp ℂ 2 (gaussianAreaMeasure alpha) →L[ℂ]
      Lp ℂ 2 (gaussianAreaMeasure alpha) :=
  (coefficientSynthesisL2 alpha ha).toContinuousLinearMap ∘L
    coefficientAnalysisL2 alpha ha

/-- The projector is the identity on the entire infinite ℓ² synthesis
range, not merely on the finite polynomial vectors. -/
theorem gaussianPolynomialProjector_synthesis
    (alpha : ℝ) (ha : 0 < alpha)
    (a : lp (fun _ : ℕ => ℂ) 2) :
    gaussianPolynomialProjector alpha ha
      (coefficientSynthesisL2 alpha ha a) =
        coefficientSynthesisL2 alpha ha a := by
  change coefficientSynthesisL2 alpha ha
    (coefficientAnalysisL2 alpha ha
      (coefficientSynthesisL2 alpha ha a)) =
      coefficientSynthesisL2 alpha ha a
  rw [coefficientAnalysisL2_synthesis alpha ha a]

/-- Idempotence of the concrete bounded Gaussian polynomial projector. -/
theorem gaussianPolynomialProjector_idempotent
    (alpha : ℝ) (ha : 0 < alpha)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) :
    gaussianPolynomialProjector alpha ha
      (gaussianPolynomialProjector alpha ha x) =
        gaussianPolynomialProjector alpha ha x := by
  change coefficientSynthesisL2 alpha ha
    (coefficientAnalysisL2 alpha ha
      (coefficientSynthesisL2 alpha ha
        (coefficientAnalysisL2 alpha ha x))) =
      coefficientSynthesisL2 alpha ha (coefficientAnalysisL2 alpha ha x)
  rw [coefficientAnalysisL2_synthesis alpha ha]

/-- Every projected vector lies in the genuine closed polynomial span. -/
theorem gaussianPolynomialProjector_mem_closure
    (alpha : ℝ) (ha : 0 < alpha)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) :
    gaussianPolynomialProjector alpha ha x ∈
      gaussianPolynomialClosure alpha ha :=
  coefficientSynthesisL2_mem_gaussianPolynomialClosure alpha ha
    (coefficientAnalysisL2 alpha ha x)

/-- The projector fixes precisely the closed Gaussian polynomial span. -/
theorem gaussianPolynomialProjector_eq_self_iff
    (alpha : ℝ) (ha : 0 < alpha)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) :
    gaussianPolynomialProjector alpha ha x = x ↔
      x ∈ gaussianPolynomialClosure alpha ha := by
  constructor
  · intro hx
    rw [← hx]
    exact gaussianPolynomialProjector_mem_closure alpha ha x
  · intro hx
    have hrange :
        x ∈ LinearMap.range
          (coefficientSynthesisL2 alpha ha).toLinearMap := by
      rw [coefficientSynthesisL2_range_eq_closure_span alpha ha]
      exact hx
    obtain ⟨a, rfl⟩ := hrange
    exact gaussianPolynomialProjector_synthesis alpha ha a

/-- The exact residual after polynomial projection is orthogonal to
all Gaussian holomorphic polynomials, equivalently all their moments vanish. -/
theorem gaussianPolynomialProjector_residual_orthogonal
    (alpha : ℝ) (ha : 0 < alpha)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) :
    x - gaussianPolynomialProjector alpha ha x ∈
      (gaussianPolynomialClosure alpha ha)ᗮ := by
  apply (coefficientAnalysisL2_eq_zero_iff_orthogonal alpha ha _).mp
  have h :
      coefficientAnalysisL2 alpha ha
        (x - gaussianPolynomialProjector alpha ha x) =
          coefficientAnalysisL2 alpha ha x -
            coefficientAnalysisL2 alpha ha
              (gaussianPolynomialProjector alpha ha x) := by
    exact map_sub (coefficientAnalysisL2 alpha ha) x
      (gaussianPolynomialProjector alpha ha x)
  rw [h]
  change coefficientAnalysisL2 alpha ha x -
    coefficientAnalysisL2 alpha ha
      (coefficientSynthesisL2 alpha ha
        (coefficientAnalysisL2 alpha ha x)) = 0
  rw [coefficientAnalysisL2_synthesis alpha ha]
  exact sub_self _

#print axioms GegenbauerFock.GaussianArea.gaussianPolynomialProjector_synthesis
#print axioms GegenbauerFock.GaussianArea.gaussianPolynomialProjector_idempotent
#print axioms GegenbauerFock.GaussianArea.gaussianPolynomialProjector_mem_closure
#print axioms GegenbauerFock.GaussianArea.gaussianPolynomialProjector_eq_self_iff
#print axioms GegenbauerFock.GaussianArea.gaussianPolynomialProjector_residual_orthogonal

end GegenbauerFock.GaussianArea
