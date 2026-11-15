import SpecialImaginaryPoint.V14119Priority3OperatorFredholmEulerianParryBridge

/-!
# Manuscript 15 — all-real genuine Dirichlet Fredholm–Eulerian identity

The exact universal CFC-S₁ Hilbert-compression Fredholm determinant for
the Dirichlet inverse spectral model was previously identified with
sinh(x)/x and with the Eulerian Fourier profile along the imaginary axis
for x ≠ 0.  Manuscript 15 states its D(x) identity for ALL real x,
including the removable singularity at zero.

Here we close that analytic endpoint using the *genuine operator*
Fredholm determinant normalization, and also certify positivity of the
real-valued Fredholm profile.  The latter legitimizes the real logarithm
of D(x) in subsequent Langevin calculations.

The Hilbert operator is the actual trace-class spectral model on
complex ℓ². This module does not assert a unitary identification with
the unbounded differential Dirichlet Laplacian on L²(0,1), nor does it
certify a trace-resolvent/logarithmic-derivative identity.
-/

noncomputable section
namespace Manuscript15

open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.DirichletInverseFredholmDerivativeTrace
open Manuscript14Priority3.DirichletTrueFredholmSinhBridge

/-- Manuscript 15's genuine operator-defined cycloidal Dirichlet
Fredholm profile, with real spectral parameter x and shift x². -/
def trueDirichletFredholmProfile (x : ℝ) : ℂ :=
  fredholmDet dirichletInverseS1 ((x ^ 2 : ℝ) : ℂ)

/-- The real normalized hyperbolic-sine profile with its exactly
removable zero singularity filled by one. -/
def normalizedRealSinh (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sinh x / x

/-- The TRUE operator Fredholm determinant equals the continuous
normalized sinh formula for every real x, INCLUDING x=0. -/
theorem trueDirichletFredholmProfile_eq_normalizedRealSinh (x : ℝ) :
    trueDirichletFredholmProfile x = (normalizedRealSinh x : ℂ) := by
  by_cases hx : x = 0
  · subst x
    simp [trueDirichletFredholmProfile, normalizedRealSinh, fredholmDet_zero]
  · simpa only [trueDirichletFredholmProfile, normalizedRealSinh,
      if_neg hx] using genuine_dirichlet_fredholm_real_square_eq_sinh x hx

/-- COMPLETE imaginary-axis Eulerian Fourier bridge, including the
value at the origin. Unlike the earlier nonzero-parameter theorem,
this statement has no side condition on x. -/
theorem trueDirichletFredholmProfile_eq_eulerian_all_real (x : ℝ) :
    trueDirichletFredholmProfile x =
      Manuscript14Section67.rE (2 * ((x : ℂ) * Complex.I)) := by
  by_cases hx : x = 0
  · subst x
    simp [trueDirichletFredholmProfile, Manuscript14Section67.rE,
      fredholmDet_zero]
  · exact genuine_dirichlet_fredholm_real_square_eq_eulerian x hx

/-- The genuine operator determinant profile is even as a function
of the real spectral square root x. -/
theorem trueDirichletFredholmProfile_even (x : ℝ) :
    trueDirichletFredholmProfile (-x) = trueDirichletFredholmProfile x := by
  simp only [trueDirichletFredholmProfile, neg_sq]

/-- The normalized real hyperbolic-sine quotient is strictly positive
on ALL real x, including zero and negative x. -/
theorem normalizedRealSinh_pos (x : ℝ) : 0 < normalizedRealSinh x := by
  rcases lt_trichotomy x 0 with hn | hz | hp
  · have hx : x ≠ 0 := ne_of_lt hn
    have hs : Real.sinh x < 0 := by
      have h := Real.sinh_pos_iff.mpr (neg_pos.mpr hn)
      rw [Real.sinh_neg] at h
      linarith
    simp only [normalizedRealSinh, if_neg hx]
    exact div_pos_of_neg_of_neg hs hn
  · subst x
    simp [normalizedRealSinh]
  · have hx : x ≠ 0 := ne_of_gt hp
    simp only [normalizedRealSinh, if_neg hx]
    exact div_pos (Real.sinh_pos_iff.mpr hp) hp

/-- Consequently the REAL PART of the genuine CFC-S₁ Fredholm
determinant D(x) is strictly positive for every real x. In
combination with the exact complex equality, it follows that D(x)
lies on the positive real axis and Real.log D(x) is meaningful. -/
theorem trueDirichletFredholmProfile_re_pos (x : ℝ) :
    0 < (trueDirichletFredholmProfile x).re := by
  rw [trueDirichletFredholmProfile_eq_normalizedRealSinh]
  simpa only [Complex.ofReal_re] using normalizedRealSinh_pos x

#print axioms Manuscript15.trueDirichletFredholmProfile_eq_normalizedRealSinh
#print axioms Manuscript15.trueDirichletFredholmProfile_eq_eulerian_all_real
#print axioms Manuscript15.trueDirichletFredholmProfile_even
#print axioms Manuscript15.normalizedRealSinh_pos
#print axioms Manuscript15.trueDirichletFredholmProfile_re_pos

end Manuscript15
