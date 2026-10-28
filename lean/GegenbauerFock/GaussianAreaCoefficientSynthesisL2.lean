import GegenbauerFock.GaussianAreaTrueL2OrthonormalFamily
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# V007 — isometric coefficient synthesis into genuine Gaussian L²

The actual normalized complex monomials form an orthonormal family
in the completed Gaussian weighted L²(ℂ). The canonical Hilbert-sum
isometry synthesizes a square-summable coefficient vector into an
actual L² Gaussian vector, not a formal sequence of Gram entries.

The range is the closure of the polynomial span; equality of this
closed range with the complete holomorphic Gaussian L² subspace is
the remaining density/surjectivity obligation.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GegenbauerFock.GaussianArea

/-- Genuine isometric synthesis of arbitrary square-summable
Gaussian Fock coefficients into weighted complex L²(ℂ). -/
noncomputable def coefficientSynthesisL2
    (alpha : ℝ) (ha : 0 < alpha) :
    (lp (fun _ : ℕ => ℂ) 2) →ₗᵢ[ℂ]
      Lp ℂ 2 (gaussianAreaMeasure alpha) :=
  (orthonormal_normalizedMonomialL2Vector alpha ha).orthogonalFamily.linearIsometry

/-- The synthesis preserves the exact Hilbert norm of any infinite
square-summable sequence, without a finite-rank restriction. -/
theorem coefficientSynthesisL2_norm
    (alpha : ℝ) (ha : 0 < alpha)
    (a : lp (fun _ : ℕ => ℂ) 2) :
    ‖coefficientSynthesisL2 alpha ha a‖ = ‖a‖ :=
  (coefficientSynthesisL2 alpha ha).norm_map a

/-- Consequently the coefficient synthesis is injective on all ℓ². -/
theorem coefficientSynthesisL2_injective
    (alpha : ℝ) (ha : 0 < alpha) :
    Function.Injective (coefficientSynthesisL2 alpha ha) :=
  (coefficientSynthesisL2 alpha ha).injective

/-- The isometric synthesis is exactly the Hilbert-space sum of the
normalized monomial vectors, for every square-summable coefficient family. -/
theorem coefficientSynthesisL2_hasSum
    (alpha : ℝ) (ha : 0 < alpha)
    (a : lp (fun _ : ℕ => ℂ) 2) :
    HasSum (fun n : ℕ =>
      a n • normalizedMonomialL2Vector alpha ha n)
      (coefficientSynthesisL2 alpha ha a) := by
  simpa only [coefficientSynthesisL2, LinearIsometry.toSpanSingleton_apply] using
    ((orthonormal_normalizedMonomialL2Vector alpha ha).orthogonalFamily).hasSum_linearIsometry a

/-- The range of the genuine Gaussian L² synthesis is precisely the
closed complex linear span of the normalized holomorphic monomials.
This does not yet identify that span with all holomorphic L² functions. -/
theorem coefficientSynthesisL2_range_eq_closure_span
    (alpha : ℝ) (ha : 0 < alpha) :
    LinearMap.range (coefficientSynthesisL2 alpha ha).toLinearMap =
      (Submodule.span ℂ (Set.range
        (fun n : ℕ => normalizedMonomialL2Vector alpha ha n))).topologicalClosure := by
  classical
  change LinearMap.range
    (((orthonormal_normalizedMonomialL2Vector alpha ha).orthogonalFamily).linearIsometry.toLinearMap) = _
  rw [((orthonormal_normalizedMonomialL2Vector alpha ha).orthogonalFamily).range_linearIsometry]
  congr 1
  simp [← LinearMap.span_singleton_eq_range, ← Submodule.span_iUnion]

#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisL2_hasSum
#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisL2_range_eq_closure_span

#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisL2_norm
#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisL2_injective

end GegenbauerFock.GaussianArea
