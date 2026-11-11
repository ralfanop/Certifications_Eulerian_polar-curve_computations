import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Priority 3 — exact zero lattice of the entire complex hyperbolic sine

For every complex number z, sinh(z)=0 iff z=k*pi*i for an integer k.
Unlike the real sinh function, the complex hyperbolic sine has an
entire imaginary lattice of zeros. The result gives a precise
spectral-zero classification for the genuine Dirichlet inverse
Fredholm determinant established in Priority 3.

This module is strictly classical complex analysis and independent
of any operator-specific identification.
-/

noncomputable section

namespace Manuscript14Priority3.ComplexSinhIntegerZeros

open Complex

/-- Complete complex zero lattice of hyperbolic sine. -/
theorem complex_sinh_eq_zero_iff_integer_pi_I (z : ℂ) :
    Complex.sinh z = 0 ↔
      ∃ k : ℤ, z = (k : ℂ) * (Real.pi : ℂ) * Complex.I := by
  have hsin : Complex.sin (z * Complex.I) =
      Complex.sinh z * Complex.I := Complex.sin_mul_I z
  constructor
  · intro hz
    have hs : Complex.sin (z * Complex.I) = 0 := by
      rw [hsin, hz, zero_mul]
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
    refine ⟨-k, ?_⟩
    calc
      z = (z * Complex.I) * (-Complex.I) := by
        simp [mul_assoc, Complex.I_mul_I]
      _ = (k : ℂ) * (Real.pi : ℂ) * (-Complex.I) := by rw [hk]
      _ = ((-k : ℤ) : ℂ) * (Real.pi : ℂ) * Complex.I := by
        push_cast
        ring
  · rintro ⟨k, rfl⟩
    have hs : Complex.sin ((k : ℂ) * (Real.pi : ℂ)) = 0 :=
      Complex.sin_eq_zero_iff.mpr ⟨k, rfl⟩
    rw [Complex.sinh_mul_I, hs, zero_mul]

#print axioms Manuscript14Priority3.ComplexSinhIntegerZeros.complex_sinh_eq_zero_iff_integer_pi_I

end Manuscript14Priority3.ComplexSinhIntegerZeros
