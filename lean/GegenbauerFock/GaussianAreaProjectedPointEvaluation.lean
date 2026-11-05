import GegenbauerFock.GaussianAreaPolynomialParseval
import GegenbauerFock.GaussianAreaIntrinsicMonomialEvaluation
import GegenbauerFock.FockEvaluationSequence

/-!
# V007 — bounded projected Gaussian point evaluation

The coefficient-space coherent-state evaluation composes with the
actual Gaussian L² coefficient-analysis adjoint. This yields a
continuous linear functional on the WHOLE Gaussian L² space, agreeing
with the Fock evaluation on the entire polynomial-closure range.

The resulting functional is evaluation of the orthogonal projection,
not yet evaluation of an arbitrary entire-representative L² class.
The analytic equality of these two evaluations is the outstanding
polynomial-density / onto Bargmann–Fock obligation.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The coefficient-model Fock evaluation applied to the true Gaussian
L² monomial coefficient analysis. This is bounded on the ambient L². -/
noncomputable def projectedGaussianEvaluation
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    Lp ℂ 2 (gaussianAreaMeasure alpha) →L[ℂ] ℂ :=
  (FockEvaluation.evaluation alpha ha z).comp
    (coefficientAnalysisL2 alpha ha)

/-- On the whole ℓ² synthesis range, projected Gaussian evaluation
recovers exactly the bounded coefficient-model Fock evaluation. -/
theorem projectedGaussianEvaluation_synthesis
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ)
    (a : lp (fun _ : ℕ => ℂ) 2) :
    projectedGaussianEvaluation alpha ha z
      (coefficientSynthesisL2 alpha ha a) =
        FockEvaluation.evaluation alpha ha z a := by
  change FockEvaluation.evaluation alpha ha z
    (coefficientAnalysisL2 alpha ha
      (coefficientSynthesisL2 alpha ha a)) = _
  rw [coefficientAnalysisL2_synthesis alpha ha a]

/-- The bounded projected evaluation depends only on the orthogonal
Gaussian polynomial projection of the input. -/
theorem projectedGaussianEvaluation_projector
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) :
    projectedGaussianEvaluation alpha ha z
      (gaussianPolynomialProjector alpha ha x) =
        projectedGaussianEvaluation alpha ha z x := by
  change FockEvaluation.evaluation alpha ha z
    (coefficientAnalysisL2 alpha ha
      (coefficientSynthesisL2 alpha ha
        (coefficientAnalysisL2 alpha ha x))) =
      FockEvaluation.evaluation alpha ha z
        (coefficientAnalysisL2 alpha ha x)
  rw [coefficientAnalysisL2_synthesis alpha ha]

/-- The coherent-state bound holds for arbitrary genuine Gaussian L²
vectors, without assuming any analytic polynomial-density theorem. -/
theorem projectedGaussianEvaluation_norm_le
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) :
    ‖projectedGaussianEvaluation alpha ha z x‖ ≤
      ‖FockEvaluation.evaluation alpha ha z‖ * ‖x‖ := by
  change ‖FockEvaluation.evaluation alpha ha z
    (coefficientAnalysisL2 alpha ha x)‖ ≤ _
  calc
    _ ≤ ‖FockEvaluation.evaluation alpha ha z‖ *
        ‖coefficientAnalysisL2 alpha ha x‖ :=
      (FockEvaluation.evaluation alpha ha z).le_opNorm _
    _ ≤ ‖FockEvaluation.evaluation alpha ha z‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_left
        (coefficientAnalysisL2_norm_le alpha ha x) (norm_nonneg _)

/-- The coefficient-model Fock evaluation of a basis coefficient is
the exact normalized entire Gaussian monomial at the same point. -/
theorem coefficientFockEvaluation_single
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) (z : ℂ) :
    FockEvaluation.evaluation alpha ha z
      (lp.single 2 n (1 : ℂ)) = normalizedMonomial alpha n z := by
  change inner ℂ (FockEvaluation.kernelVector alpha ha z)
    (lp.single 2 n (1 : ℂ)) = _
  rw [lp.inner_single_right, RCLike.inner_apply]
  simp [FockEvaluation.kernelVector, FockEvaluation.kernelCoordinate,
    normalizedMonomial, monomialWeight]

/-- The bounded projected evaluation and the intrinsic analytic
evaluation agree on every genuine normalized monomial vector. -/
theorem projectedGaussianEvaluation_normalizedMonomial
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) (z : ℂ) :
    projectedGaussianEvaluation alpha ha z
      (normalizedMonomialL2Vector alpha ha n) =
        intrinsicEntireEvaluation alpha ha z
          (normalizedMonomialIntrinsicVector alpha ha n) := by
  rw [← coefficientSynthesisL2_single alpha ha n]
  rw [projectedGaussianEvaluation_synthesis]
  rw [coefficientFockEvaluation_single]
  exact (intrinsicEntireEvaluation_normalizedMonomial alpha ha n z).symm

#print axioms GegenbauerFock.GaussianArea.projectedGaussianEvaluation_synthesis
#print axioms GegenbauerFock.GaussianArea.projectedGaussianEvaluation_projector
#print axioms GegenbauerFock.GaussianArea.projectedGaussianEvaluation_norm_le
#print axioms GegenbauerFock.GaussianArea.coefficientFockEvaluation_single
#print axioms GegenbauerFock.GaussianArea.projectedGaussianEvaluation_normalizedMonomial

end GegenbauerFock.GaussianArea
