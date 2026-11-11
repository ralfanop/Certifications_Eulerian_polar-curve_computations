import SpecialImaginaryPoint.V14119Priority3DirichletCompleteSpectralZeroSet

/-!
# Priority 3 — nonreal and positive spectral shifts are zero-free
# for the actual universal CFC Schatten-S₁ Dirichlet Fredholm determinant

After complete operatorial complex zero classification, we certify
two immediate and mathematically useful consequences:
* No nonreal complex parameter can be a determinant zero.
* Every strictly positive REAL spectral shift is zero-free.

These statements concern the genuine trace-class Fredholm determinant
of the actual l² Dirichlet inverse spectral model. They do not
assert anything about a differential L² realization not yet linked
to that spectral model in Lean.
-/

noncomputable section

namespace Manuscript14Priority3.DirichletNonrealZeroExclusion

open Filter Topology
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalDirichletSinh
open Manuscript14Priority3.DirichletCompleteSpectralZeroSet

/-- The actual genuine CFC-S₁ Dirichlet inverse determinant
has no zeros off the real spectral axis. -/
theorem dirichlet_fredholm_nonzero_of_nonreal
    (λ : ℂ) (hIm : λ.im ≠ 0) :
    fredholmDet inverseTraceClass λ ≠ 0 := by
  intro hzero
  obtain ⟨k, _hk0, hk⟩ :=
    (universal_dirichlet_fredholm_zero_iff_negative_pi_square λ).mp hzero
  have hreal :
      λ = ((-(((k : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) := by
    calc
      λ = -(((k : ℂ) * (Real.pi : ℂ)) ^ 2) := hk
      _ = ((-(((k : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) := by
        push_cast
        ring
  have hImZero : λ.im = 0 := by
    rw [hreal]
    simp
  exact hIm hImZero

/-- Every positive real shift of the actual infinite-dimensional
trace-class Dirichlet inverse Fredholm determinant is nonzero. -/
theorem dirichlet_fredholm_nonzero_of_positive_real
    (x : ℝ) (hx : 0 < x) :
    fredholmDet inverseTraceClass (x : ℂ) ≠ 0 := by
  intro hzero
  obtain ⟨k, _hk0, hk⟩ :=
    (universal_dirichlet_fredholm_zero_iff_negative_pi_square
      (x : ℂ)).mp hzero
  have hEqComplex :
      (x : ℂ) = ((-(((k : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) := by
    calc
      (x : ℂ) = -(((k : ℂ) * (Real.pi : ℂ)) ^ 2) := hk
      _ = ((-(((k : ℝ) * Real.pi) ^ 2) : ℝ) : ℂ) := by
        push_cast
        ring
  have hEqReal : x = -(((k : ℝ) * Real.pi) ^ 2) :=
    Complex.ofReal_injective hEqComplex
  nlinarith only [hEqReal, hx, sq_nonneg ((k : ℝ) * Real.pi)]

#print axioms Manuscript14Priority3.DirichletNonrealZeroExclusion.dirichlet_fredholm_nonzero_of_nonreal
#print axioms Manuscript14Priority3.DirichletNonrealZeroExclusion.dirichlet_fredholm_nonzero_of_positive_real

end Manuscript14Priority3.DirichletNonrealZeroExclusion
