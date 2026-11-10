import SpecialImaginaryPoint.V14119Priority3ComplexDiagonalFredholm
import GegenbauerFock.PhyslibTraceClassCoisometricConjugation

/-!
# Manuscript 14.119 Priority 3 — transported, non-fixed-basis Fredholm sectors

Given arbitrary complex absolutely summable diagonal data D and any
coisometry U (U U† = I), this module constructs an actual operator
U† T_D U in the genuine CFC S₁ ideal, proves its exact trace norm,
and identifies its spectral action on the transported orthonormal
system U† e_n.

A Fredholm determinant is defined as a genuine function of operators
in the image of this transported sector and proved independent of its
diagonal-data witness for each fixed coisometry U. The coisometry
may be nonunitary, so this includes actual non-fixed-basis S₁
operators not diagonal in the original basis.

The result does NOT identify determinant values for arbitrary
different coisometric representations of the same operator, nor
construct the universal basis-independent Fredholm determinant on
every trace-class operator. This distinction is essential.
-/

noncomputable section

namespace Manuscript14Priority3.ComplexDiagonalFredholm
open Filter Topology InnerProductSpace
open scoped ComplexOrder lp
open Manuscript14Priority3.TraceClassModel

/-- Actual CFC S₁ endomorphism obtained from a complex diagonal
S₁ operator by arbitrary bounded-operator conjugation. -/
def transported (U : H →L[ℂ] H) (D : Data) :
    ProbabilisticTheory.TraceClass H :=
  ProbabilisticTheory.TraceClass.conjugate (S1Diagonal D) U

@[simp] theorem transported_operator (U : H →L[ℂ] H) (D : Data) :
    (transported U D).1 = U.adjoint * (S1Diagonal D).1 * U := rfl

/-- An actual coisometry carries every complex diagonal eigenvector
to an eigenvector in the transported orthonormal family. -/
theorem transported_eigen (U : H →L[ℂ] H)
    (hUUstar : U * U.adjoint = 1)
    (D : Data) (n : ℕ) :
    (transported U D).1 (U.adjoint (b n)) =
      D.coeff n • U.adjoint (b n) := by
  calc
    (transported U D).1 (U.adjoint (b n)) =
        U.adjoint ((S1Diagonal D).1 (U (U.adjoint (b n)))) := rfl
    _ = U.adjoint ((S1Diagonal D).1 (b n)) := by
      have hvector : U (U.adjoint (b n)) = b n := by
        calc
          U (U.adjoint (b n)) = (U * U.adjoint) (b n) := rfl
          _ = b n := by rw [hUUstar]; rfl
      rw [hvector]
    _ = U.adjoint (D.coeff n • b n) := by
      rw [S1Diagonal_eigen D n]
    _ = D.coeff n • U.adjoint (b n) := map_smul U.adjoint _ _

/-- Exact basis-independent CFC trace-norm conservation even for
coisometric embeddings, not merely unitary coordinate changes. -/
theorem transported_traceNorm_eq (U : H →L[ℂ] H)
    (hUUstar : U * U.adjoint = 1)
    (hUnorm : ‖U‖ ≤ (1 : ℝ)) (D : Data) :
    ProbabilisticTheory.TraceClass.traceNorm H (transported U D) =
      ProbabilisticTheory.TraceClass.traceNorm H (S1Diagonal D) :=
  ProbabilisticTheory.TraceClass.coisometric_conjugate_traceNorm_eq_v007
    (S1Diagonal D) U hUUstar hUnorm

/-- True S₁ convergence of all actual transported finite-rank
compressions, on any coisometric image. -/
theorem transported_truncation_tendsto (U : H →L[ℂ] H) (D : Data) :
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N,
          ProbabilisticTheory.TraceClass.conjugate (S1term D n) U)
      atTop (𝓝 (transported U D)) := by
  let F : ProbabilisticTheory.TraceClass H →L[ℂ]
      ProbabilisticTheory.TraceClass H :=
    ProbabilisticTheory.TraceClass.sandwichContinuous U.adjoint U
  have hlim :
      Tendsto (fun N : ℕ => F (∑ n ∈ Finset.range N, S1term D n))
        atTop (𝓝 (F (S1Diagonal D))) :=
    (F.continuous.tendsto (S1Diagonal D)).comp (S1Diagonal_tendsto D)
  have hpart (N : ℕ) :
      F (∑ n ∈ Finset.range N, S1term D n) =
        ∑ n ∈ Finset.range N,
          ProbabilisticTheory.TraceClass.conjugate (S1term D n) U := by
    simp only [map_sum]
    rfl
  simpa only [hpart, F, ProbabilisticTheory.TraceClass.sandwichContinuous_apply,
    transported, ProbabilisticTheory.TraceClass.conjugate] using hlim

/-- Actual complex matrix of the restriction of a transported infinite
CFC S₁ operator to the first N transported orthonormal vectors. -/
def compressedTransported (U : H →L[ℂ] H) (D : Data) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => inner ℂ (U.adjoint (b i.val))
    ((transported U D).1 (U.adjoint (b j.val)))

/-- True transported Hilbert-space compressions are IDENTICAL to
the original complex diagonal Hilbert compressions, for every
coisometry U. This is an actual matrix-coefficient theorem. -/
theorem compressedTransported_eq (U : H →L[ℂ] H)
    (hUUstar : U * U.adjoint = 1) (D : Data) (N : ℕ) :
    compressedTransported U D N = compressed D N := by
  ext i j
  have hiso :
      inner ℂ (U.adjoint (b i.val)) (U.adjoint (b j.val)) =
      inner ℂ (b i.val) (b j.val) := by
    rw [ContinuousLinearMap.adjoint_inner_right]
    have hu : U (U.adjoint (b i.val)) = b i.val := by
      calc
        U (U.adjoint (b i.val)) =
            (U * U.adjoint) (b i.val) := rfl
        _ = b i.val := by rw [hUUstar]; rfl
    rw [hu]
  change inner ℂ (U.adjoint (b i.val))
      ((transported U D).1 (U.adjoint (b j.val))) =
    inner ℂ (b i.val) ((S1Diagonal D).1 (b j.val))
  rw [transported_eigen U hUUstar D j.val, S1Diagonal_eigen D j.val]
  rw [inner_smul_right, inner_smul_right, hiso]

def finiteTransportedShift
    (U : H →L[ℂ] H) (D : Data) (N : ℕ) (z : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  1 + z • compressedTransported U D N

/-- Exact finite complex matrix determinant of the TRUE
transported non-fixed-basis Hilbert-space compression. -/
theorem finiteTransportedShift_det_eq (U : H →L[ℂ] H)
    (hUUstar : U * U.adjoint = 1)
    (D : Data) (N : ℕ) (z : ℂ) :
    Matrix.det (finiteTransportedShift U D N z) =
      Matrix.det (finiteShift D N z) := by
  rw [finiteTransportedShift, compressedTransported_eq U hUUstar]
  rfl

/-- Actual transported complex Hilbert-space compression determinants
converge to the complex Fredholm product for arbitrary z. -/
theorem finiteTransportedShift_det_tendsto (U : H →L[ℂ] H)
    (hUUstar : U * U.adjoint = 1)
    (D : Data) (z : ℂ) :
    Tendsto
      (fun N : ℕ => Matrix.det (finiteTransportedShift U D N z))
      atTop (𝓝 (determinant D z)) := by
  have heq :
      (fun N : ℕ => Matrix.det (finiteTransportedShift U D N z)) =
      (fun N : ℕ => Matrix.det (finiteShift D N z)) := by
    funext N
    exact finiteTransportedShift_det_eq U hUUstar D N z
  rw [heq]
  exact finiteShift_det_tendsto D z

/-- Equality of transported trace-class operators forces equality
of arbitrary complex coefficient data. This uses the actual
coisometric inverse on S₁ rather than a formal symbol argument. -/
theorem transported_coeff_eq (U : H →L[ℂ] H)
    (hUUstar : U * U.adjoint = 1) (D E : Data)
    (h : transported U D = transported U E) :
    D.coeff = E.coeff := by
  have hh := congrArg
    (fun T : ProbabilisticTheory.TraceClass H =>
      ProbabilisticTheory.TraceClass.conjugate T U.adjoint) h
  have hback : S1Diagonal D = S1Diagonal E := by
    simpa only [transported,
      ProbabilisticTheory.TraceClass.coisometric_conjugate_inverse_v007
        (S1Diagonal D) U hUUstar,
      ProbabilisticTheory.TraceClass.coisometric_conjugate_inverse_v007
        (S1Diagonal E) U hUUstar] using hh
  exact funext (coeff_eq_of_S1_eq D E hback)

/-- The complex Fredholm determinant depends only on the actual
transported trace-class operator, once the coisometry is fixed. -/
theorem transported_determinant_eq_of_eq
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1)
    (D E : Data) (h : transported U D = transported U E) (z : ℂ) :
    determinant D z = determinant E z := by
  have hcoeff := transported_coeff_eq U hUUstar D E h
  simp only [determinant, hcoeff]

/-- Actual S₁ operator sector arising from a fixed arbitrary
coisometry, not restricted to diagonal operators in the original basis. -/
def transportedSector (U : H →L[ℂ] H) :
    Set (ProbabilisticTheory.TraceClass H) :=
  Set.range (transported U)

/-- Genuine operator-argument complex Fredholm functional, for the
fixed coisometric transported sector. -/
def determinantOnTransportedSector (U : H →L[ℂ] H)
    (T : transportedSector U) (z : ℂ) : ℂ :=
  determinant (Classical.choose T.property) z

/-- Independence of the chosen complex coefficient representation
of an actual transported Schatten-S₁ operator for fixed U. -/
theorem determinantOnTransportedSector_eq
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1)
    (T : transportedSector U) (D : Data)
    (hD : transported U D = T.val) (z : ℂ) :
    determinantOnTransportedSector U T z = determinant D z := by
  unfold determinantOnTransportedSector
  apply transported_determinant_eq_of_eq U hUUstar
  exact (Classical.choose_spec T.property).trans hD.symm

/-- The operatorial fixed-coisometry determinant of its actual
transported D agrees with the convergent complex spectral product. -/
theorem determinantOnTransportedSector_ofData
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1)
    (D : Data) (z : ℂ) :
    determinantOnTransportedSector U
      ⟨transported U D, ⟨D, rfl⟩⟩ z = determinant D z :=
  determinantOnTransportedSector_eq U hUUstar _ D rfl z

#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.transported_operator
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.transported_eigen
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.transported_traceNorm_eq
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.transported_truncation_tendsto
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.compressedTransported_eq
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.finiteTransportedShift_det_eq
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.finiteTransportedShift_det_tendsto
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.transported_coeff_eq
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.transported_determinant_eq_of_eq
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.determinantOnTransportedSector_eq
#print axioms Manuscript14Priority3.ComplexDiagonalFredholm.determinantOnTransportedSector_ofData

end Manuscript14Priority3.ComplexDiagonalFredholm
