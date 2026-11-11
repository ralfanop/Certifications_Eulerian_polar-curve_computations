import SpecialImaginaryPoint.V14119Priority3ComplexDirichletSinhEntire

/-!
# Priority 3 — exact real sinc identity from the genuine CFC-S1 Dirichlet Fredholm determinant

For any nonzero real x, the true UNIVERSAL trace-class Fredholm
determinant of the genuine l² Dirichlet inverse spectral model
at the negative real shift -x² is sin(x)/x.

The result is a nontrivial analytic continuation of the certified
hyperbolic identity det(I+x² A_D⁻¹)=sinh(x)/x:
    det(I-x² A_D⁻¹)=sin(x)/x.
The proof uses the established ENTIRE complex Fredholm identity,
the exact sinh(i x)=i sin(x) identity, and cancellation of i.
The x=0 normalization is separately certified globally.

No identification of the l² spectral model with an L²(0,1)
differential realization is asserted.
-/

noncomputable section

namespace Manuscript14Priority3.DirichletImaginarySinc

open Filter Topology
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalDirichletSinh
open Manuscript14Priority3.ComplexDirichletSinhEntire

/-- True universal Fredholm spectral inverse evaluated on the
negative real axis equals the EXACT complex sine quotient. -/
theorem universal_dirichlet_negative_sin_quotient_complex
    (x : ℝ) (hx : x ≠ 0) :
    fredholmDet inverseTraceClass (-((x : ℂ) ^ 2)) =
      Complex.sin (x : ℂ) / (x : ℂ) := by
  have h := universal_dirichlet_sinh_entire_identity
    ((x : ℂ) * Complex.I)
  rw [Complex.sinh_mul_I] at h
  have hi : ((x : ℂ) * Complex.I) ^ 2 =
      -((x : ℂ) ^ 2) := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hi] at h
  have hcancel :
      (x : ℂ) * fredholmDet inverseTraceClass (-((x : ℂ) ^ 2)) =
        Complex.sin (x : ℂ) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    calc
      ((x : ℂ) * fredholmDet inverseTraceClass (-((x : ℂ) ^ 2))) *
          Complex.I =
        ((x : ℂ) * Complex.I) *
          fredholmDet inverseTraceClass (-((x : ℂ) ^ 2)) := by ring
      _ = Complex.sin (x : ℂ) * Complex.I := h
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  apply (eq_div_iff hxC).2
  rw [mul_comm]
  exact hcancel

/-- Manuscript-facing REAL sinc identity of the genuine universal
Dirichlet inverse Fredholm determinant for every nonzero x. -/
theorem universal_dirichlet_negative_real_sinc
    (x : ℝ) (hx : x ≠ 0) :
    fredholmDet inverseTraceClass (-((x : ℂ) ^ 2)) =
      ((Real.sin x / x : ℝ) : ℂ) := by
  rw [universal_dirichlet_negative_sin_quotient_complex x hx]
  norm_cast

#print axioms Manuscript14Priority3.DirichletImaginarySinc.universal_dirichlet_negative_sin_quotient_complex
#print axioms Manuscript14Priority3.DirichletImaginarySinc.universal_dirichlet_negative_real_sinc

end Manuscript14Priority3.DirichletImaginarySinc
