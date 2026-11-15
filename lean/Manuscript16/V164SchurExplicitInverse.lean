import Mathlib

/-!
Manuscript 16 v16.4 §13, exact two-sided inverse of the scalar 2×2
Schur block. This is a finite-dimensional algebraic model only;
no Fredholmness, graph-domain continuity, or det₄ is asserted.
-/

namespace Manuscript16

/-- The proposed inverse of the 2×2 scalar block, with the
    determinant written explicitly to avoid an auxiliary axiom. -/
theorem schur_two_sided_inverse_entries (a b c l : ℂ)
    (hdet : a * l - b * c ≠ 0) :
    a * (l / (a * l - b * c)) +
      b * (-c / (a * l - b * c)) = 1 ∧
    a * (-b / (a * l - b * c)) +
      b * (a / (a * l - b * c)) = 0 ∧
    c * (l / (a * l - b * c)) +
      l * (-c / (a * l - b * c)) = 0 ∧
    c * (-b / (a * l - b * c)) +
      l * (a / (a * l - b * c)) = 1 ∧
    (l / (a * l - b * c)) * a +
      (-b / (a * l - b * c)) * c = 1 ∧
    (l / (a * l - b * c)) * b +
      (-b / (a * l - b * c)) * l = 0 ∧
    (-c / (a * l - b * c)) * a +
      (a / (a * l - b * c)) * c = 0 ∧
    (-c / (a * l - b * c)) * b +
      (a / (a * l - b * c)) * l = 1 := by
  constructor
  · field_simp [hdet]
    <;> ring
  constructor
  · field_simp [hdet]
    <;> ring
  constructor
  · field_simp [hdet]
    <;> ring
  constructor
  · field_simp [hdet]
    <;> ring
  constructor
  · field_simp [hdet]
    <;> ring
  constructor
  · field_simp [hdet]
    <;> ring
  constructor
  · field_simp [hdet]
    <;> ring
  · field_simp [hdet]
    <;> ring

#print axioms Manuscript16.schur_two_sided_inverse_entries
end Manuscript16
