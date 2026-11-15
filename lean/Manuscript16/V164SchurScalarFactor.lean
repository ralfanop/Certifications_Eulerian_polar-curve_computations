import Mathlib

/-!
Manuscript 16 v16.4 §13, equation (mixed-factor-164).
Scalar Schur-complement determinant analogue over the reals.
This is NOT a theorem about unbounded graph-domain operators, compactness,
Fredholm index, or regularized determinants.
-/
namespace Manuscript16

/-- Exact scalar block determinant factorisation when the lower
diagonal entry is invertible. -/
theorem v164_schur_scalar_det_factor
    (a b c l : ℝ) (hl : l ≠ 0) :
    a * l - b * c = (a - b * l⁻¹ * c) * l := by
  field_simp [hl]
  <;> ring

/-- Scalar Schur complement nonvanishing iff the 2x2 determinant
is nonzero, provided the lower block is invertible. -/
theorem v164_schur_scalar_ne_zero_iff
    (a b c l : ℝ) (hl : l ≠ 0) :
    a * l - b * c ≠ 0 ↔ a - b * l⁻¹ * c ≠ 0 := by
  rw [v164_schur_scalar_det_factor a b c l hl]
  simp [hl]

/-- Corresponding zero-locus equivalence. -/
theorem v164_schur_scalar_zero_iff
    (a b c l : ℝ) (hl : l ≠ 0) :
    a * l - b * c = 0 ↔ a - b * l⁻¹ * c = 0 := by
  rw [v164_schur_scalar_det_factor a b c l hl]
  simp [hl]

#print axioms Manuscript16.v164_schur_scalar_det_factor
#print axioms Manuscript16.v164_schur_scalar_ne_zero_iff
#print axioms Manuscript16.v164_schur_scalar_zero_iff

end Manuscript16
