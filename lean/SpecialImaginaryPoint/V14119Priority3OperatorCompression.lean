import SpecialImaginaryPoint.V14119Priority3DirichletDiagonal
import SpecialImaginaryPoint.DirichletFiniteDeterminant
import SpecialImaginaryPoint.V14119Priority3SpectralDetBridge

/-!
# Manuscript 14.119, Priority 3: actual operator compressions

Finite matrices are formed by taking the real Hilbert spectral inverse's
COMPLEX bounded operator matrix coefficients in its canonical basis.
No scalar-product surrogate is used for the compressed inverse.

The resulting determinant is first proved as a genuine finite complex matrix
determinant. The infinite trace-class Fredholm determinant and relative zeta
determinant remain independent proof obligations.
-/

noncomputable section
namespace Manuscript14Priority3.OperatorCompression
open Manuscript14Priority3.TraceClassModel
open InnerProductSpace

/-- Matrix coefficients of the actual Dirichlet inverse operator
on the first N vectors of its complex ℓ² Hilbert basis. -/
def compressedInverse (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => inner ℂ (b i.val) (inverse (b j.val))

/-- The compression of the genuine inverse operator is diagonal,
with the true spectral multipliers on the diagonal. -/
theorem compressedInverse_eq_diagonal (N : ℕ) :
    compressedInverse N =
      Matrix.diagonal (fun i : Fin N => (σ i.val : ℂ)) := by
  ext i j
  change inner ℂ (b i.val) (inverse (b j.val)) =
    Matrix.diagonal (fun k : Fin N => (σ k.val : ℂ)) i j
  rw [inverse_eigen j.val, inner_smul_right]
  by_cases hij : i = j
  · subst j
    simp [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one i.val]
  · have hv : i.val ≠ j.val := by
      intro heq
      exact hij (Fin.ext heq)
    rw [b.orthonormal.inner_eq_zero hv]
    simp [Matrix.diagonal_apply, hij]

/-- Genuine finite compression of I + t A⁻¹ on the complex Hilbert basis. -/
def finiteOperatorShift (N : ℕ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  1 + (t : ℂ) • compressedInverse N

/-- Shifted compressed operator equals the spectral diagonal matrix. -/
theorem finiteOperatorShift_eq_diagonal (N : ℕ) (t : ℝ) :
    finiteOperatorShift N t =
      Matrix.diagonal (fun i : Fin N => 1 + (t : ℂ) * (σ i.val : ℂ)) := by
  rw [finiteOperatorShift, compressedInverse_eq_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_apply, smul_eq_mul]
  · simp [Matrix.diagonal_apply, hij]

/-- Actual determinant of the finite compressed operator, over ℂ. -/
theorem finiteOperatorShift_det (N : ℕ) (t : ℝ) :
    Matrix.det (finiteOperatorShift N t) =
      ∏ i : Fin N, (1 + (t : ℂ) * (σ i.val : ℂ)) := by
  rw [finiteOperatorShift_eq_diagonal, Matrix.det_diagonal]

/-- The factor of the genuine complex compressed operator agrees with the
exact Dirichlet Euler factor already certified in the scalar bridge. -/
theorem factor_eq_real (n : ℕ) (t : ℝ) :
    1 + (t : ℂ) * (σ n : ℂ) =
      ((Manuscript14Dirichlet.factor n t : ℝ) : ℂ) := by
  simp only [σ, Manuscript14Dirichlet.factor, Nat.cast_add, Nat.cast_one]
  push_cast
  ring

/-- Every genuine compressed complex-operator determinant equals the
already-certified real Dirichlet spectral truncation, under ℝ → ℂ. -/
theorem finiteOperatorShift_det_eq_spectral (N : ℕ) (t : ℝ) :
    Matrix.det (finiteOperatorShift N t) =
      ((Manuscript14Dirichlet.finiteFredholm N t : ℝ) : ℂ) := by
  rw [finiteOperatorShift_det]
  calc
    (∏ i : Fin N, (1 + (t : ℂ) * (σ i.val : ℂ))) =
        ∏ i : Fin N, ((Manuscript14Dirichlet.factor i.val t : ℝ) : ℂ) :=
      Finset.prod_congr rfl (fun i _ => factor_eq_real i.val t)
    _ = ((∏ i : Fin N, Manuscript14Dirichlet.factor i.val t : ℝ) : ℂ) := by
      norm_cast
    _ = ((Manuscript14Dirichlet.finiteFredholm N t : ℝ) : ℂ) := by
      simp only [Manuscript14Dirichlet.finiteFredholm, Finset.prod_range]

/-- The true compressed-operator matrix determinants converge to the
complexified Euler product of the spectral Dirichlet problem. This is an
operator-compression limit, not yet an abstract Fredholm determinant. -/
theorem finiteOperatorShift_det_tendsto (x : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ => Matrix.det (finiteOperatorShift N (x ^ 2)))
      Filter.atTop (nhds ((Real.sinh x / x : ℝ) : ℂ)) := by
  have hreal :=
    Manuscript14Priority3.finite_dirichlet_product_tendsto x hx
  have hcast :
      Filter.Tendsto
        (fun N : ℕ =>
          ((Manuscript14Dirichlet.finiteFredholm N (x ^ 2) : ℝ) : ℂ))
        Filter.atTop (nhds ((Real.sinh x / x : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto (Real.sinh x / x)).comp hreal
  convert hcast using 1
  funext N
  exact finiteOperatorShift_det_eq_spectral N (x ^ 2)

#print axioms Manuscript14Priority3.OperatorCompression.compressedInverse_eq_diagonal
#print axioms Manuscript14Priority3.OperatorCompression.finiteOperatorShift_eq_diagonal
#print axioms Manuscript14Priority3.OperatorCompression.finiteOperatorShift_det
#print axioms Manuscript14Priority3.OperatorCompression.factor_eq_real
#print axioms Manuscript14Priority3.OperatorCompression.finiteOperatorShift_det_eq_spectral
#print axioms Manuscript14Priority3.OperatorCompression.finiteOperatorShift_det_tendsto

end Manuscript14Priority3.OperatorCompression
