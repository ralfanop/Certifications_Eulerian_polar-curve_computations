import Manuscript15.DirichletFredholmAllReal
import SpecialImaginaryPoint.Section67ScalarCertificate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Separation.Basic

/-!
# Manuscript 15: genuine Dirichlet Fredholm logarithmic derivative and Langevin trace

The previous kernel-checked construction defines the *actual* universal
CFC Schatten-S₁ Hilbert-compression Fredholm determinant of the
Dirichlet inverse spectral operator T_D on complex ℓ², and proves

  D(x) = det_F(I+x²T_D) = sinh(x)/x, x ≠ 0,
  D(0) = 1, and Re D(x) > 0 for all real x.

This module establishes the analytic/logarithmic-derivative consequences
for the REAL-PARAMETER profile of that genuine operator determinant:
  d/dx log(Re D(x)) = coth(x) - 1/x = L(x)   (x ≠ 0).

For x > 0 we combine this with the separately certified scalar
Dirichlet resolvent sum identity L(x) = 2 x T_D(x). Hence the scalar
summable resolvent trace equals (2x)⁻¹ times the logarithmic derivative
of a true infinite-dimensional trace-class Hilbert-operator Fredholm
determinant.

The existing TD(x) here is the rigorously defined scalar spectral
series of Manuscript14Section67. This does NOT yet claim a new
trace-of-operator-resolvent statement on L²(0,1), nor prove a unitary
equivalence with a differential realization.
-/

noncomputable section
namespace Manuscript15

open Filter Topology

/-- The real part of the genuine Dirichlet trace-class Fredholm
determinant is differentiable away from x=0, with the exact
derivative of the normalized sinh quotient. -/
theorem trueDirichletFredholmProfile_re_hasDerivAt
    (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (trueDirichletFredholmProfile y).re)
      ((Real.cosh x * x - Real.sinh x) / x ^ 2) x := by
  have hevent :
      (fun y : ℝ => (trueDirichletFredholmProfile y).re) =ᶠ[𝓝 x]
        (fun y : ℝ => Real.sinh y / y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [trueDirichletFredholmProfile_eq_normalizedRealSinh,
      normalizedRealSinh, hy]
  have hq :
      HasDerivAt (fun y : ℝ => Real.sinh y / y)
        ((Real.cosh x * x - Real.sinh x) / x ^ 2) x := by
    convert (Real.hasDerivAt_sinh x).fun_div (hasDerivAt_id x) hx using 1
    all_goals ring
  exact hq.congr_of_eventuallyEq hevent

/-- The logarithmic derivative of the REAL PART of the genuine
operator Fredholm determinant is exactly the classical Langevin
function, at all nonzero real parameters. -/
theorem trueDirichletFredholmProfile_log_hasDerivAt
    (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt
      (fun y : ℝ => Real.log (trueDirichletFredholmProfile y).re)
      (Manuscript14Section67.Lval x) x := by
  have hD : (trueDirichletFredholmProfile x).re =
      Real.sinh x / x := by
    rw [trueDirichletFredholmProfile_eq_normalizedRealSinh]
    simp [normalizedRealSinh, hx]
  have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
  have hval :
      ((Real.cosh x * x - Real.sinh x) / x ^ 2) /
        (trueDirichletFredholmProfile x).re =
          Manuscript14Section67.Lval x := by
    rw [hD]
    dsimp [Manuscript14Section67.Lval]
    field_simp [hx, hs]
    <;> ring
  have hpositive := trueDirichletFredholmProfile_re_pos x
  exact ((trueDirichletFredholmProfile_re_hasDerivAt x hx).log
    hpositive.ne').congr_deriv hval

/-- The exact logarithmic DERIVATIVE of the genuine CFC-S₁ operator
Fredholm determinant profile equals Langevin away from zero. -/
theorem trueDirichletFredholmProfile_log_deriv_eq_Langevin
    (x : ℝ) (hx : x ≠ 0) :
    deriv (fun y : ℝ => Real.log (trueDirichletFredholmProfile y).re) x =
      Manuscript14Section67.Lval x :=
  (trueDirichletFredholmProfile_log_hasDerivAt x hx).deriv

/-- For x>0, the logarithmic derivative of the genuine operator
Fredholm profile equals 2x times the actual summable scalar spectral
Dirichlet resolvent series (not an asserted differential-operator trace). -/
theorem trueDirichletFredholmProfile_log_deriv_eq_spectral_trace
    (x : ℝ) (hx : 0 < x) :
    deriv (fun y : ℝ => Real.log (trueDirichletFredholmProfile y).re) x =
      2 * x * Manuscript14Section67.TD x := by
  calc
    deriv (fun y : ℝ =>
        Real.log (trueDirichletFredholmProfile y).re) x =
          Manuscript14Section67.Lval x :=
      trueDirichletFredholmProfile_log_deriv_eq_Langevin x hx.ne'
    _ = 2 * x * Manuscript14Section67.TD x :=
      Manuscript14Section67.trace_master x hx

#print axioms Manuscript15.trueDirichletFredholmProfile_re_hasDerivAt
#print axioms Manuscript15.trueDirichletFredholmProfile_log_hasDerivAt
#print axioms Manuscript15.trueDirichletFredholmProfile_log_deriv_eq_Langevin
#print axioms Manuscript15.trueDirichletFredholmProfile_log_deriv_eq_spectral_trace

end Manuscript15
