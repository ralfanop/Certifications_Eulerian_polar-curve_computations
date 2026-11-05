import SpecialImaginaryPoint.DirichletFiniteDeterminant

/-!
# Manuscript 14.1 §7 — finite resolvent traces

This module formalizes diagonal finite resolvent traces and their
nonnegative, monotonically growing partial sums. These are the
truncations of the trace formula in Theorem 7.3 and the squared
Hilbert–Schmidt trace in Corollary 7.4.

The trace-class limit and equality with the hyperbolic-function
closed forms are NOT asserted here. No infinite-dimensional operator
or infinite sum is replaced by a finite sample.
-/

namespace Manuscript14Dirichlet

/-- Positive shifted eigenvalues of the auxiliary Dirichlet Laplacian. -/
noncomputable def shiftedEigenvalue (n : ℕ) (t : ℝ) : ℝ :=
  Real.pi ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 2) + t

theorem shiftedEigenvalue_pos (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 < shiftedEigenvalue n t := by
  unfold shiftedEigenvalue
  positivity

/-- Concrete diagonal truncation of the shifted inverse A+tI. -/
noncomputable def finiteResolvent (N : ℕ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => 1 / shiftedEigenvalue i.val t)

/-- The finite resolvent trace by its spectral sum. -/
noncomputable def finiteTrace (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, 1 / shiftedEigenvalue n t

/-- The exact trace of the finite diagonal resolvent matrix. -/
theorem finiteResolvent_trace (N : ℕ) (t : ℝ) :
    Matrix.trace (finiteResolvent N t) =
      ∑ i : Fin N, 1 / shiftedEigenvalue i.val t := by
  simp [finiteResolvent, Matrix.trace]

/-- Finite resolvent trace is positive semidefinite for t≥0. -/
theorem finiteTrace_nonneg (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ finiteTrace N t := by
  unfold finiteTrace
  apply Finset.sum_nonneg
  intro n hn
  exact div_nonneg (by norm_num) (le_of_lt (shiftedEigenvalue_pos n t ht))

/-- Spectral resolvent trace recurrence, with no omitted tail. -/
theorem finiteTrace_succ (N : ℕ) (t : ℝ) :
    finiteTrace (N + 1) t =
      finiteTrace N t + 1 / shiftedEigenvalue N t := by
  simp only [finiteTrace, Finset.sum_range_succ]

theorem finiteTrace_mono_step (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    finiteTrace N t ≤ finiteTrace (N + 1) t := by
  rw [finiteTrace_succ]
  have hn : 0 ≤ 1 / shiftedEigenvalue N t :=
    div_nonneg (by norm_num) (le_of_lt (shiftedEigenvalue_pos N t ht))
  linarith

/-- Sum of squares of the first N resolvent eigenvalues. -/
noncomputable def finiteSquaredTrace (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, 1 / (shiftedEigenvalue n t) ^ 2

theorem finiteSquaredTrace_nonneg (N : ℕ) (t : ℝ) :
    0 ≤ finiteSquaredTrace N t := by
  unfold finiteSquaredTrace
  apply Finset.sum_nonneg
  intro n hn
  positivity

theorem finiteSquaredTrace_succ (N : ℕ) (t : ℝ) :
    finiteSquaredTrace (N + 1) t =
      finiteSquaredTrace N t + 1 / (shiftedEigenvalue N t) ^ 2 := by
  simp only [finiteSquaredTrace, Finset.sum_range_succ]

#print axioms Manuscript14Dirichlet.shiftedEigenvalue_pos
#print axioms Manuscript14Dirichlet.finiteResolvent_trace
#print axioms Manuscript14Dirichlet.finiteTrace_nonneg
#print axioms Manuscript14Dirichlet.finiteTrace_succ
#print axioms Manuscript14Dirichlet.finiteTrace_mono_step
#print axioms Manuscript14Dirichlet.finiteSquaredTrace_nonneg
#print axioms Manuscript14Dirichlet.finiteSquaredTrace_succ

end Manuscript14Dirichlet
