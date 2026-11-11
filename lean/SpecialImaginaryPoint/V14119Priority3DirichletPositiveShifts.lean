import SpecialImaginaryPoint.V14119Priority3UniversalDirichletSinh

/-!
# Priority 3 — strict positivity on the complete nonnegative Dirichlet spectral axis

For the ACTUAL universal Fredholm determinant of the genuine CFC
Schatten-S₁ Dirichlet inverse spectral operator, all t>0 satisfy

  det_F(I + t A_D⁻¹) = sinh(sqrt t)/sqrt t > 0.

At t=0 the universal determinant equals 1; hence for every t≥0
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
    (t : ℝ) (ht : 0 < t) :
    fredholmDet inverseTraceClass (t : ℂ) =
      ((Real.sinh (Real.sqrt t) / Real.sqrt t : ℝ) : ℂ) := by
  have hsqrt : Real.sqrt t ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 ht)
  have h :=
    fredholmDet_true_dirichlet_inverse_sinh_quotient
      (Real.sqrt t) hsqrt
  rw [Real.sq_sqrt (le_of_lt ht)] at h
  exact h

/-- Strict REAL positivity of the actual universal Dirichlet inverse
Fredholm determinant at every positive spectral shift. -/
theorem dirichlet_universal_positive_shift_real_pos
    (t : ℝ) (ht : 0 < t) :
    0 < (fredholmDet inverseTraceClass (t : ℂ)).re := by
  rw [dirichlet_universal_positive_shift_sinh t ht]
  rw [Complex.ofReal_re]
  exact div_pos
    (Real.sinh_pos_iff.mpr (Real.sqrt_pos.2 ht))
    (Real.sqrt_pos.2 ht)

/-- Nonnegative real spectral shifts all yield strictly positive
real Fredholm determinants, including the normalized t=0 case. -/
theorem dirichlet_universal_nonnegative_shift_real_pos
    (t : ℝ) (ht : 0 ≤ t) :
    0 < (fredholmDet inverseTraceClass (t : ℂ)).re := by
  rcases (eq_or_lt_of_le ht) with hzero | hpos
  · subst t
    simpa only [Complex.ofReal_zero, fredholmDet_zero, Complex.one_re]
      using (show (0 : ℝ) < 1 by norm_num)
  · exact dirichlet_universal_positive_shift_real_pos t hpos

#print axioms Manuscript14Priority3.DirichletPositiveShifts.dirichlet_universal_positive_shift_sinh
#print axioms Manuscript14Priority3.DirichletPositiveShifts.dirichlet_universal_positive_shift_real_pos
#print axioms Manuscript14Priority3.DirichletPositiveShifts.dirichlet_universal_nonnegative_shift_real_pos

end Manuscript14Priority3.DirichletPositiveShifts
