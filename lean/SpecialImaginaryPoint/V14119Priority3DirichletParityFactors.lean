import SpecialImaginaryPoint.Section67ScalarCertificate

/-!
# Manuscript 14, §7 — finite parity splitting of actual Dirichlet spectral factors

At spectral parameter x², the length-two Dirichlet inverse eigenvalues
are the union (with multiplicity) of the length-one Dirichlet inverse
eigenvalues and the mixed Dirichlet–Neumann inverse eigenvalues.
This module proves the *individual exact Euler factor identities*
for even and odd spectral indices, including all real x.

This is an algebraic component of the spectral direct-sum argument,
not a proof of unitary equivalence for the actual unbounded
differential operators and not an abstract Fredholm determinant identity.
Neither a scalar surrogate for an operator determinant nor a new
mathematical result is introduced.
-/

noncomputable section

namespace Manuscript14Priority3.DirichletParityFactors

open Real
open Manuscript14Section67

/-- The length-two Dirichlet factor at even (one-indexed) mode 2n+2
coincides with the length-one Dirichlet factor at mode n+1. -/
theorem even_dirichlet_factor (n : ℕ) (x : ℝ) :
    sinhFac (2 * x) (2 * n + 1) = sinhFac x n := by
  unfold sinhFac
  have hc : (((2 * n + 1 : ℕ) : ℝ) + 1) = 2 * ((n : ℝ) + 1) := by
    push_cast
    ring
  rw [hc]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  <;> ring

/-- The length-two Dirichlet factor at odd (one-indexed) mode 2n+1
coincides with the mixed Dirichlet–Neumann factor at mode n+1/2. -/
theorem odd_dirichlet_factor (n : ℕ) (x : ℝ) :
    sinhFac (2 * x) (2 * n) = coshFac x n := by
  unfold sinhFac coshFac
  have hc : (((2 * n : ℕ) : ℝ) + 1) = 2 * ((n : ℝ) + 1 / 2) := by
    push_cast
    ring
  rw [hc]
  have hn : (n : ℝ) + 1 / 2 ≠ 0 := by positivity
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  <;> ring

#print axioms Manuscript14Priority3.DirichletParityFactors.even_dirichlet_factor
#print axioms Manuscript14Priority3.DirichletParityFactors.odd_dirichlet_factor

end Manuscript14Priority3.DirichletParityFactors
