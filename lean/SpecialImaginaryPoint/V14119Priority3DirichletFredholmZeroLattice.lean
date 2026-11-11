import SpecialImaginaryPoint.V14119Priority3ComplexDirichletSinhEntire
import SpecialImaginaryPoint.V14119Priority3ComplexSinhIntegerZeros

/-!
# Priority 3 — complete zero lattice of the GENUINE universal Dirichlet inverse Fredholm determinant

For all NONZERO complex spectral square-root parameters z:
  det_F(I + z² A_D⁻¹) = 0  iff
  z = kπi for some NONZERO integer k.

This is NOT a declaration about a formal Euler product only: the
left side is the proven universal actual CFC Schatten S₁ Fredholm
determinant of the genuine l² Dirichlet inverse spectral model.
The proof combines the kernel-certified universal complex entire
sinh identity with the exact integer-lattice zeros of complex sinh.

The original spectral operator is the l² Dirichlet spectral inverse;
no identification with a differential realization on L²(0,1)
is asserted here.
-/

noncomputable section

namespace Manuscript14Priority3.DirichletFredholmZeroLattice

open Filter Topology
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalDirichletSinh
open Manuscript14Priority3.ComplexDirichletSinhEntire
open Manuscript14Priority3.ComplexSinhIntegerZeros

/-- COMPLETE zero lattice of the TRUE universal Fredholm
determinant of the genuine Dirichlet inverse spectral operator,
on the spectral square-root plane away from zero. -/
theorem dirichlet_fredholm_square_zero_iff_integer_pi_I
    (z : ℂ) (hz : z ≠ 0) :
    fredholmDet inverseTraceClass (z ^ 2) = 0 ↔
      ∃ k : ℤ, k ≠ 0 ∧
        z = (k : ℂ) * (Real.pi : ℂ) * Complex.I := by
  have hzero :
      (fredholmDet inverseTraceClass (z ^ 2) = 0) ↔
        Complex.sinh z = 0 := by
    constructor
    · intro hdet
      have h := universal_dirichlet_sinh_entire_identity z
      rw [hdet, mul_zero] at h
      exact h.symm
    · intro hs
      have h := universal_dirichlet_sinh_entire_identity z
      rw [hs] at h
      rcases mul_eq_zero.mp h with hz0 | hdet
      · exact (hz hz0).elim
      · exact hdet
  rw [hzero, complex_sinh_eq_zero_iff_integer_pi_I]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, hk⟩
    intro hk0
    have hz0 : z = 0 := by simpa [hk0] using hk
    exact hz hz0
  · rintro ⟨k, _hk0, hk⟩
    exact ⟨k, hk⟩

#print axioms Manuscript14Priority3.DirichletFredholmZeroLattice.dirichlet_fredholm_square_zero_iff_integer_pi_I

end Manuscript14Priority3.DirichletFredholmZeroLattice
