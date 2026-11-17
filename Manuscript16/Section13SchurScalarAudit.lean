import Mathlib

/-!
# Manuscript 16 v16.5, Section 13: scalar Schur complement audit

Source ZIP SHA-256:
4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e

This file proves only a finite-dimensional scalar identity.
It does NOT establish the graph-domain block factorisation, Fredholm equivalence,
Schatten-class membership, det4 zero criterion, or any numerical certificate.
Do not confuse a successful CI on this file with certification of Section 13.
-/

namespace Manuscript16.Section13.SchurScalar

/-- Scalar determinant identity underlying the Schur complement when the
lower-right entry is nonzero. This is an algebraic prerequisite, not an
operator-theoretic factorisation. -/
theorem schur_scalar_identity (a b c l : ℂ) (hl : l ≠ 0) :
    (a - b * l⁻¹ * c) * l = a * l - b * c := by
  field_simp [hl]
  <;> ring

end Manuscript16.Section13.SchurScalar
