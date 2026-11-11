import SpecialImaginaryPoint.V14119Priority3DirichletFredholmZeroLattice

/-!
# Priority 3 — exact negative real zeros at each Dirichlet eigenvalue

For every nonzero integer k the TRUE universal CFC Schatten-S₁
Fredholm determinant of the actual Dirichlet inverse spectral
operator on l² vanishes at
    lambda = -(k*pi)^2.

These are genuine negative real spectral determinant zeros, not
a merely formal cancellation of an infinite Euler factor.
The proof specializes the complete square-root zero classification
of the actual CFC-S₁ determinant, using i²=-1.
The reverse implication for arbitrary lambda is a distinct
spectral-zero completeness statement.
-/

noncomputable section

namespace Manuscript14Priority3.DirichletNegativeFredholmZeros

open Filter Topology
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalDirichletSinh
open Manuscript14Priority3.DirichletFredholmZeroLattice

/-- Every nonzero integer Dirichlet spectral mode produces an
ACTUAL complex Fredholm determinant zero at -(k*pi)^2. -/
theorem genuine_dirichlet_fredholm_vanishes_at_negative_eigenvalues
    (k : ℤ) (hk : k ≠ 0) :
    fredholmDet inverseTraceClass
      (-(((k : ℂ) * (Real.pi : ℂ)) ^ 2)) = 0 := by
  let z : ℂ := (k : ℂ) * (Real.pi : ℂ) * Complex.I
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz : z ≠ 0 := by
    dsimp [z]
    exact mul_ne_zero (mul_ne_zero hkC hpiC) Complex.I_ne_zero
  have hzero : fredholmDet inverseTraceClass (z ^ 2) = 0 :=
    (dirichlet_fredholm_square_zero_iff_integer_pi_I z hz).2
      ⟨k, hk, rfl⟩
  have hsquare :
      z ^ 2 = -(((k : ℂ) * (Real.pi : ℂ)) ^ 2) := by
    dsimp [z]
    rw [mul_pow, Complex.I_sq]
    ring
  rwa [hsquare] at hzero

#print axioms Manuscript14Priority3.DirichletNegativeFredholmZeros.genuine_dirichlet_fredholm_vanishes_at_negative_eigenvalues

end Manuscript14Priority3.DirichletNegativeFredholmZeros
