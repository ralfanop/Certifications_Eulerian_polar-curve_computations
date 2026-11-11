import SpecialImaginaryPoint.V14119Priority3UniversalFredholmExistence
import SpecialImaginaryPoint.V14119Priority3PositiveDiagonalFredholm
import SpecialImaginaryPoint.V14119Priority3SpectralDetBridge

/-!
# Priority 3 — exact operatorial Dirichlet sinh quotient for the universal CFC-S₁ Fredholm determinant

This is the bridge from the formerly separate certified:
* genuine positive diagonal trace-class Hilbert operators;
* classical Dirichlet inverse spectral product; and
* UNIVERSAL, representation-independent CFC Schatten-S₁ Fredholm determinant.

For every positive summable diagonal D and real shift t, the actual
universal trace-class determinant evaluated at the genuine
infinite-dimensional Hilbert operator S1Diagonal(D) equals the
convergent infinite Euler product of D's diagonal spectral factors.

In particular the TRUE universal Fredholm determinant of the
genuine Dirichlet spectral INVERSE model on ℓ²(ℕ,ℂ) satisfies
    det(I + x² A_D⁻¹) = sinh(x)/x      for x ≠ 0.
No definition by decree: the equality is proved by the identical
actual finite Hilbert compression matrices and the uniqueness of
their complex limits.

This does NOT identify the ℓ² spectral inverse with the differential
inverse of the Dirichlet Laplacian on L²(0,1), nor is it a
zeta-regularized determinant of the unbounded Laplacian.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalDirichletSinh

open Filter Topology
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.FiniteRankFredholm
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.PositiveDiagonalFredholm

/-- EXACT equality between the finite genuine Hilbert compression
determinant of the actual CFC-S₁ diagonal operator and the
already-certified finite diagonal Fredholm determinant. -/
theorem finiteDeterminant_diagonal_eq_finiteShift
    (D : PositiveDiagonalFredholm.Data) (N : ℕ) (t : ℝ) :
    finiteDeterminant N (S1Diagonal D) (t : ℂ) =
      Matrix.det (finiteShift D N t) := by
  have hm : compressedCFC N (S1Diagonal D) = compressed D N := by
    ext i j
    change inner ℂ (b i.val) ((S1Diagonal D).1 (b j.val)) =
      inner ℂ (b i.val) (boundedDiagonal D (b j.val))
    rw [S1Diagonal_operator_eq D]
  simp only [finiteDeterminant, finiteShift, hm]

/-- Universality specializes EXACTLY to the spectral Euler product
on the whole positive summable diagonal CFC trace-class sector:
no normality or diagonal assumption was used in the universal
construction itself, only in this specialization of its value. -/
theorem fredholmDet_positive_diagonal_eq_product
    (D : PositiveDiagonalFredholm.Data) (t : ℝ) :
    fredholmDet (S1Diagonal D) (t : ℂ) =
      (PositiveDiagonalFredholm.determinant D t : ℂ) := by
  have hs :
      (fun N : ℕ => finiteDeterminant N (S1Diagonal D) (t : ℂ)) =
        (fun N : ℕ => Matrix.det (finiteShift D N t)) :=
    funext (fun N => finiteDeterminant_diagonal_eq_finiteShift D N t)
  have hconv := finiteDeterminant_tendsto_fredholmDet (S1Diagonal D) (t : ℂ)
  rw [hs] at hconv
  exact tendsto_nhds_unique hconv (finiteShift_det_tendsto D t)

/-- The positive-diagonal product of the certified Dirichlet
spectral inverse is literally the existing scalar spectral product,
with every individual factor identical. -/
theorem dirichlet_positive_diagonal_eq_spectralProduct (t : ℝ) :
    PositiveDiagonalFredholm.determinant dirichlet t =
      Manuscript14Priority3.spectralProduct t := by
  unfold PositiveDiagonalFredholm.determinant
    Manuscript14Priority3.spectralProduct
  congr 1
  funext n
  change 1 + t * σ n =
    Manuscript14Dirichlet.factor n t
  simp only [σ, Manuscript14Dirichlet.factor, Nat.cast_add,
    Nat.cast_one, div_eq_mul_inv]

/-- The classical hyperbolic sine quotient is the ACTUAL
universal Fredholm determinant of the genuine CFC-S₁
positive diagonal Dirichlet inverse spectral model. -/
theorem fredholmDet_dirichlet_sinh_quotient
    (x : ℝ) (hx : x ≠ 0) :
    fredholmDet (S1Diagonal dirichlet) ((x ^ 2 : ℝ) : ℂ) =
      ((Real.sinh x / x : ℝ) : ℂ) := by
  rw [fredholmDet_positive_diagonal_eq_product,
    dirichlet_positive_diagonal_eq_spectralProduct,
    Manuscript14Priority3.spectralProduct_sq x hx]

/-- The actual CFC trace-class inverse as an element of the full
infinite-dimensional Schatten-S₁ Banach ideal, independently of
its positive diagonal series representation. -/
def inverseTraceClass : ProbabilisticTheory.TraceClass H :=
  ProbabilisticTheory.TraceClass.ofOperator H inverse inverse_isTraceClass

/-- The certified Dirichlet inverse and the positive-diagonal CFC-S₁
sum are equal as TRUE trace-class operators, not merely as spectra. -/
theorem inverseTraceClass_eq_S1Diagonal :
    inverseTraceClass = S1Diagonal dirichlet := by
  apply Subtype.ext
  exact (dirichlet_S1Diagonal_eq_inverse).symm

/-- Direct manuscript-facing operator identity:
the UNIVERSAL determinant of the independently constructed
genuine CFC-S₁ Dirichlet spectral inverse equals sinh(x)/x. -/
theorem fredholmDet_true_dirichlet_inverse_sinh_quotient
    (x : ℝ) (hx : x ≠ 0) :
    fredholmDet inverseTraceClass ((x ^ 2 : ℝ) : ℂ) =
      ((Real.sinh x / x : ℝ) : ℂ) := by
  rw [inverseTraceClass_eq_S1Diagonal]
  exact fredholmDet_dirichlet_sinh_quotient x hx

#print axioms Manuscript14Priority3.UniversalDirichletSinh.finiteDeterminant_diagonal_eq_finiteShift
#print axioms Manuscript14Priority3.UniversalDirichletSinh.fredholmDet_positive_diagonal_eq_product
#print axioms Manuscript14Priority3.UniversalDirichletSinh.dirichlet_positive_diagonal_eq_spectralProduct
#print axioms Manuscript14Priority3.UniversalDirichletSinh.fredholmDet_dirichlet_sinh_quotient
#print axioms Manuscript14Priority3.UniversalDirichletSinh.inverseTraceClass_eq_S1Diagonal
#print axioms Manuscript14Priority3.UniversalDirichletSinh.fredholmDet_true_dirichlet_inverse_sinh_quotient

end Manuscript14Priority3.UniversalDirichletSinh
