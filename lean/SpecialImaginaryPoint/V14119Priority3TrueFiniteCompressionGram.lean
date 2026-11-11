import SpecialImaginaryPoint.V14119Priority3CompressedEuclideanCoordinates
import SpecialImaginaryPoint.V14119Priority3FiniteNuclearFredholm
import SpecialImaginaryPoint.V14119Priority3ComplexGramMinorBridge

/-!
# Priority 3 — actual Hilbert-compression determinant as sharp mixed-Gram determinant

The TRUE N×N compression determinant of a finite-nuclear CFC-S₁
operator equals the determinant of the arbitrary complex mixed-Gram
matrix of the first N finite Hilbert coefficient vectors.

Because the coefficient-vector map is contractive by Bessel's
inequality, these identities transfer all previously certified
dimension-free unrestricted mixed-Gram perturbation theorems
to genuine CFC-S₁ finite compressions, with the ORIGINAL
nuclear costs as upper bounds.

No positivity, normality, diagonalization, invertibility, or
basis truncation invariance is assumed here.
-/

noncomputable section
namespace Manuscript14Priority3.TrueFiniteCompressionGram

open Matrix InnerProductSpace
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.FiniteNuclearFredholm
open Manuscript14Priority3.CompressedEuclideanCoordinates
open Manuscript14Priority3.ComplexGramMinorBridge

/-- The true truncated Gram matrix is the complex mixed-Gram matrix
of finite-dimensional Euclidean coordinate vectors. -/
theorem truncatedGram_eq_coordinate_mixedGram
    (N m : ℕ) (u v : Fin m → H) :
    rightMatrix N m v * leftMatrix N m u =
      mixedGram (fun i => coefficients b N (u i))
        (fun i => coefficients b N (v i)) := by
  ext i j
  change
      (∑ k : Fin N,
        inner ℂ (v i) (b k.val) * inner ℂ (b k.val) (u j)) =
      inner ℂ (coefficients b N (v i)) (coefficients b N (u j))
  exact (coefficients_inner_eq_truncated b N (u j) (v i)).symm

/-- The actual N-dimensional ambient Hilbert compression
determinant is a genuine mixed-Gram determinant of Euclidean
coefficient vectors, valid for any nonnormal finite-rank operator. -/
theorem finiteDeterminant_eq_coordinate_mixedGram
    (N m : ℕ) (u v : Fin m → H) (z : ℂ) :
    Manuscript14Priority3.FiniteRankFredholm.finiteDeterminant N
      (finiteNuclear m u v) z =
      (1 + z • mixedGram
        (fun i => coefficients b N (u i))
        (fun i => coefficients b N (v i))).det := by
  rw [finiteNuclear_det_eq_truncatedGram,
    truncatedGram_eq_coordinate_mixedGram]

/-- Uniform in the compression dimension N:
the nuclear mass of the coefficient vectors cannot exceed the
true original finite nuclear PRESENTATION mass. -/
theorem coordinate_nuclear_mass_le
    (N m : ℕ) (u v : Fin m → H) :
    (∑ i : Fin m,
      ‖coefficients b N (u i)‖ *
        ‖coefficients b N (v i)‖) ≤
      ∑ i : Fin m, ‖u i‖ * ‖v i‖ := by
  apply Finset.sum_le_sum
  intro i hi
  calc
    ‖coefficients b N (u i)‖ *
        ‖coefficients b N (v i)‖ ≤
      ‖u i‖ * ‖coefficients b N (v i)‖ :=
        mul_le_mul_of_nonneg_right
          (coefficients_norm_le b b.orthonormal N (u i))
          (norm_nonneg _)
    _ ≤ ‖u i‖ * ‖v i‖ :=
      mul_le_mul_of_nonneg_left
        (coefficients_norm_le b b.orthonormal N (v i))
        (norm_nonneg _)

/-- Zero rank-one left vector stays zero after Euclidean
compression, so erased terms remain genuinely absent. -/
theorem coefficients_zero (N : ℕ) :
    coefficients b N (0 : H) = 0 := by
  ext i
  simp [coefficients]

#print axioms Manuscript14Priority3.TrueFiniteCompressionGram.truncatedGram_eq_coordinate_mixedGram
#print axioms Manuscript14Priority3.TrueFiniteCompressionGram.finiteDeterminant_eq_coordinate_mixedGram
#print axioms Manuscript14Priority3.TrueFiniteCompressionGram.coordinate_nuclear_mass_le
#print axioms Manuscript14Priority3.TrueFiniteCompressionGram.coefficients_zero

end Manuscript14Priority3.TrueFiniteCompressionGram
