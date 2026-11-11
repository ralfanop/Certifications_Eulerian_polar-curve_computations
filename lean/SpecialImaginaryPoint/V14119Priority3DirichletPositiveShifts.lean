import SpecialImaginaryPoint.V14119Priority3UniversalDirichletSinh

/-!
# Priority 3 — strict positivity on the complete nonnegative Dirichlet spectral axis

For the ACTUAL universal Fredholm determinant of the genuine CFC
Schatten-S₁ Dirichlet inverse spectral operator, all λ>0 satisfy

  det_F(I + λ A_D⁻¹) = sinh(sqrt λ)/sqrt λ > 0.

At λ=0 the universal determinant equals 1; hence for every λ≥0
its complex value is a strictly positive REAL number. These
are intrinsic results about the actual CFC S₁ operator determinant,
not about a scalar substitute or zeta regularization.

This module uses the earlier kernel-verified Dirichlet sinh quotient
and universal normalization at spectral parameter zero. It does not
claim equivalence between the spectral ℓ² inverse and an unverified
differential operator realization.
-/

noncomputable section

namespace Manuscript14Priority3.DirichletPositiveShifts

open Filter Topology
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalDirichletSinh

/-- An exact positive-shift operatorial identity, with the
nonzero denominator established by positive square root. -/
theorem dirichlet_universal_positive_shift_sinh
    (λ : ℝ) (hλ : 0 < λ) :
    fredholmDet inverseTraceClass (λ : ℂ) =
      ((Real.sinh (Real.sqrt λ) / Real.sqrt λ : ℝ) : ℂ) := by
  have hsqrt : Real.sqrt λ ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hλ)
  have h :=
    fredholmDet_true_dirichlet_inverse_sinh_quotient
      (Real.sqrt λ) hsqrt
  rw [Real.sq_sqrt (le_of_lt hλ)] at h
  exact h

/-- Strict REAL positivity of the actual universal Dirichlet inverse
Fredholm determinant at every positive spectral shift. -/
theorem dirichlet_universal_positive_shift_real_pos
    (λ : ℝ) (hλ : 0 < λ) :
    0 < (fredholmDet inverseTraceClass (λ : ℂ)).re := by
  rw [dirichlet_universal_positive_shift_sinh λ hλ]
  rw [Complex.ofReal_re]
  exact div_pos
    (Real.sinh_pos_iff.mpr (Real.sqrt_pos.2 hλ))
    (Real.sqrt_pos.2 hλ)

/-- Nonnegative real spectral shifts all yield strictly positive
real Fredholm determinants, including the normalized λ=0 case. -/
theorem dirichlet_universal_nonnegative_shift_real_pos
    (λ : ℝ) (hλ : 0 ≤ λ) :
    0 < (fredholmDet inverseTraceClass (λ : ℂ)).re := by
  rcases (eq_or_lt_of_le hλ) with hzero | hpos
  · subst λ
    simpa only [Complex.ofReal_zero, fredholmDet_zero, Complex.one_re]
      using (show (0 : ℝ) < 1 by norm_num)
  · exact dirichlet_universal_positive_shift_real_pos λ hpos

#print axioms Manuscript14Priority3.DirichletPositiveShifts.dirichlet_universal_positive_shift_sinh
#print axioms Manuscript14Priority3.DirichletPositiveShifts.dirichlet_universal_positive_shift_real_pos
#print axioms Manuscript14Priority3.DirichletPositiveShifts.dirichlet_universal_nonnegative_shift_real_pos

end Manuscript14Priority3.DirichletPositiveShifts
