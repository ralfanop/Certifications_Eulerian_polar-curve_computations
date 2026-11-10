import SpecialImaginaryPoint.V14119Priority3TraceClassModel
import GegenbauerFock.PhyslibTraceClassOperatorEmbedding
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Manuscript 14.119 Priority 3 — finite-rank determinant intrinsic algebra

The Weinstein–Aronszajn/Sylvester formula identifies det(I+zAB)
with det(I+zBA) for arbitrary rectangular COMPLEX matrices of
different dimensions. As a consequence, finite-rank determinant
values arising from two factorizations of the same ambient finite
operator are equal, even when the auxiliary factorization dimensions
differ.

Separately, the matrix of the actual finite Hilbert-basis compression
of ANY complex CFC Schatten S₁ operator is constructed, without
positivity, self-adjointness, diagonality or a spectral enumeration.
Each matrix entry is 1-Lipschitz in the GENUINE CFC trace norm.

This supplies precise finite-dimensional ingredients for the
universal operatorial Fredholm construction. It does NOT yet
establish trace-norm convergence of arbitrary finite compressions,
a global finite-determinant perturbation bound, or the infinite
basis-independent determinant on all S₁(H).
-/

noncomputable section

namespace Manuscript14Priority3.FiniteRankFredholm
open InnerProductSpace
open scoped ComplexOrder lp
open Manuscript14Priority3.TraceClassModel

/-- Genuine Weinstein–Aronszajn identity with an arbitrary COMPLEX
spectral coupling z and rectangular matrices of DIFFERENT dimensions. -/
theorem determinant_rectangular_comm
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (B : Matrix n m ℂ) (z : ℂ) :
    Matrix.det (1 + z • (A * B)) =
      Matrix.det (1 + z • (B * A)) := by
  calc
    Matrix.det (1 + z • (A * B)) =
        Matrix.det (1 + (z • A) * B) := by
      rw [Matrix.smul_mul]
    _ = Matrix.det (1 + B * (z • A)) :=
      Matrix.det_one_add_mul_comm (z • A) B
    _ = Matrix.det (1 + z • (B * A)) := by
      rw [Matrix.mul_smul]

/-- Independence of the finite determinant under TWO arbitrary
rectangular factorizations of the SAME complex ambient operator,
even if the two auxiliary spaces have distinct dimensions. -/
theorem determinant_factorization_independent
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix n m ℂ)
    (C : Matrix m p ℂ) (D : Matrix p m ℂ)
    (h : A * B = C * D) (z : ℂ) :
    Matrix.det (1 + z • (B * A)) =
      Matrix.det (1 + z • (D * C)) := by
  calc
    Matrix.det (1 + z • (B * A)) =
        Matrix.det (1 + z • (A * B)) :=
      (determinant_rectangular_comm A B z).symm
    _ = Matrix.det (1 + z • (C * D)) := by rw [h]
    _ = Matrix.det (1 + z • (D * C)) :=
      determinant_rectangular_comm C D z

/-- True finite Hilbert-space compression matrix of any actual
CFC trace-class operator; no diagonal, positivity or normality
hypothesis. The Hilbert basis comes from the project spectral model. -/
def compressedCFC (N : ℕ)
    (T : ProbabilisticTheory.TraceClass H) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => inner ℂ (b i.val) (T.1 (b j.val))

/-- Matrix of I+zT on the actual finite-dimensional Hilbert
compression for arbitrary, possibly nonnormal trace-class T. -/
def finiteDeterminant (N : ℕ)
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) : ℂ :=
  Matrix.det (1 + z • compressedCFC N T)

/-- Genuine complex-linear behavior of finite matrix compressions
with respect to adding arbitrary CFC trace-class operators. -/
theorem compressedCFC_add (N : ℕ)
    (T V : ProbabilisticTheory.TraceClass H) :
    compressedCFC N (T + V) =
      compressedCFC N T + compressedCFC N V := by
  ext i j
  simp only [compressedCFC, Matrix.add_apply,
    ProbabilisticTheory.TraceClass.add_operator,
    ContinuousLinearMap.add_apply, inner_add_right]

/-- Exact operator-level subtraction of arbitrary finite Hilbert
compression entries. No conditional positivity is assumed. -/
theorem compressedCFC_sub (N : ℕ)
    (T V : ProbabilisticTheory.TraceClass H) :
    compressedCFC N (T - V) =
      compressedCFC N T - compressedCFC N V := by
  ext i j
  simp only [compressedCFC, Matrix.sub_apply,
    ProbabilisticTheory.TraceClass.sub_operator,
    ContinuousLinearMap.sub_apply, inner_sub_right]

/-- Sharp, basis-independent trace-norm control of EVERY complex
matrix coefficient of the actual finite compression of arbitrary
CFC S₁ maps; uniform in the compression dimension N. -/
theorem compressedCFC_entry_sub_norm_le (N : ℕ)
    (T V : ProbabilisticTheory.TraceClass H)
    (i j : Fin N) :
    ‖compressedCFC N T i j - compressedCFC N V i j‖ ≤
      ‖T - V‖ := by
  have hinner :
      compressedCFC N T i j - compressedCFC N V i j =
        inner ℂ (b i.val) ((T - V).1 (b j.val)) := by
    rw [← Matrix.sub_apply, ← compressedCFC_sub]
    rfl
  rw [hinner]
  calc
    ‖inner ℂ (b i.val) ((T - V).1 (b j.val))‖ ≤
        ‖b i.val‖ * ‖(T - V).1 (b j.val)‖ :=
      norm_inner_le_norm _ _
    _ = ‖(T - V).1 (b j.val)‖ := by
      rw [b.orthonormal.norm_eq_one i.val, one_mul]
    _ ≤ ‖(T - V).1‖ * ‖b j.val‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖(T - V).1‖ := by
      rw [b.orthonormal.norm_eq_one j.val, mul_one]
    _ ≤ ‖T - V‖ :=
      ProbabilisticTheory.TraceClass.operator_norm_le_trace_norm (T - V)

#print axioms Manuscript14Priority3.FiniteRankFredholm.determinant_rectangular_comm
#print axioms Manuscript14Priority3.FiniteRankFredholm.determinant_factorization_independent
#print axioms Manuscript14Priority3.FiniteRankFredholm.compressedCFC_add
#print axioms Manuscript14Priority3.FiniteRankFredholm.compressedCFC_sub
#print axioms Manuscript14Priority3.FiniteRankFredholm.compressedCFC_entry_sub_norm_le

end Manuscript14Priority3.FiniteRankFredholm
