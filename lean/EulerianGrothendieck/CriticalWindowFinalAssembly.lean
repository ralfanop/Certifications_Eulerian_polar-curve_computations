import CriticalWindowFockDomination
import CriticalWindowAnalyticRemainder
import CriticalWindowGammaVacuum

/-!
M12 §9 — vertical assembly of the *actual* quartic critical-window integral.
This file keeps the genuine original sine-profile Fock norm, and changes the
two real integration variables, rather than defining a replacement integral.
The next obligations are to identify the resulting integrand with the already
certified actual-MGF profile and invoke dominated convergence. No assumptions
about the asymptotic limit are inserted.
-/

namespace M12CriticalAssembly

open MeasureTheory Filter
open scoped Topology

/-- The actual squared Fock integrand for r_E(z) = sin(z/2)/(z/2).
The value at zero is the analytic continuation already certified in #507. -/
noncomputable def originalKernel (M : ℕ) (alpha x y : ℝ) : ℝ :=
  Real.exp (-alpha * (x^2+y^2)) *
    ‖M12FockDomination.fockProfile ((x : ℂ)+(y : ℂ)*Complex.I)‖^(2*M)

/-- The literal plane integral in the author's Fock norm theorem, §9. -/
noncomputable def originalFockNorm (M : ℕ) (alpha : ℝ) : ℝ :=
  (alpha / Real.pi) * ∫ x : ℝ, ∫ y : ℝ, originalKernel M alpha x y

/-- Full-line Lebesgue substitution by any positive dilation. -/
theorem line_dilation (g : ℝ → ℝ) (a : ℝ) (ha : 0 < a) :
    (∫ y : ℝ, g y) = a * ∫ x : ℝ, g (a*x) := by
  have h : (∫ x : ℝ, g (a*x)) = a⁻¹ * ∫ y : ℝ, g y := by
    simpa only [abs_of_pos (inv_pos.mpr ha), smul_eq_mul] using
      (Measure.integral_comp_mul_left g a)
  rw [h]
  field_simp [ne_of_gt ha]

/-- Actual two-dimensional anisotropic change of variables. The Jacobian
is a*b, established by two Mathlib Lebesgue changes of variables. -/
theorem plane_dilation (f : ℝ → ℝ → ℝ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ, ∫ y : ℝ, f x y) =
      (a*b) * ∫ w : ℝ, ∫ u : ℝ, f (a*w) (b*u) := by
  calc
    (∫ x : ℝ, ∫ y : ℝ, f x y) =
        a * ∫ w : ℝ, ∫ y : ℝ, f (a*w) y :=
      line_dilation (fun x => ∫ y : ℝ, f x y) a ha
    _ = a * ∫ w : ℝ, b * (∫ u : ℝ, f (a*w) (b*u)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with w
      exact line_dilation (fun y => f (a*w) y) b hb
    _ = a * (b * (∫ w : ℝ, ∫ u : ℝ, f (a*w) (b*u))) := by
      rw [integral_const_mul]
    _ = (a*b) * (∫ w : ℝ, ∫ u : ℝ, f (a*w) (b*u)) := by ring

/-- Exact Jacobian identity for the genuine Fock norm. No limiting
approximation is involved. -/
theorem originalFockNorm_plane_dilation (M : ℕ) (alpha a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    originalFockNorm M alpha =
      (alpha / Real.pi) * (a*b) *
        (∫ w : ℝ, ∫ u : ℝ, originalKernel M alpha (a*w) (b*u)) := by
  unfold originalFockNorm
  rw [plane_dilation (originalKernel M alpha) a b ha hb]
  ring

/-- The physical anisotropic dilation has the exact Jacobian 6*e³. -/
theorem critical_jacobian (e : ℝ) :
    (Real.sqrt 6 * e^2) * (Real.sqrt 6 * e) = 6*e^3 := by
  have hs : (Real.sqrt (6:ℝ))^2 = 6 := Real.sq_sqrt (by norm_num)
  calc
    _ = (Real.sqrt 6)^2 * e^3 := by ring
    _ = 6*e^3 := by rw [hs]

/-- This is the exact normalization of the *original* Fock plane
integral. The equality M*e⁴=1 is the anisotropic scaling condition;
for the asymptotic sequence take e=M^(-1/4). -/
theorem normalized_originalFockNorm (M : ℕ) (e lam : ℝ)
    (he : 0 < e) (hM : (M:ℝ)*e^4 = 1) :
    e * originalFockNorm M ((1/12+lam*e^2)*(M:ℝ)) =
      (6*(1/12+lam*e^2)/Real.pi) *
        (∫ w : ℝ, ∫ u : ℝ,
          originalKernel M ((1/12+lam*e^2)*(M:ℝ))
            ((Real.sqrt 6 * e^2)*w) ((Real.sqrt 6 * e)*u)) := by
  let a : ℝ := Real.sqrt 6 * e^2
  let b : ℝ := Real.sqrt 6 * e
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : a*b = 6*e^3 := critical_jacobian e
  rw [originalFockNorm_plane_dilation M _ a b ha hb]
  rw [hab]
  have hcoef : e * (((1/12+lam*e^2)*(M:ℝ))/Real.pi) * (6*e^3) =
      6*(1/12+lam*e^2)/Real.pi := by
    calc
      _ = (6*(1/12+lam*e^2)/Real.pi) * ((M:ℝ)*e^4) := by ring
      _ = _ := by rw [hM, mul_one]
  calc
    _ = (e * (((1/12+lam*e^2)*(M:ℝ))/Real.pi) * (6*e^3)) *
      (∫ w : ℝ, ∫ u : ℝ,
        originalKernel M ((1/12+lam*e^2)*(M:ℝ)) (a*w) (b*u)) := by ring
    _ = _ := by rw [hcoef]

end M12CriticalAssembly

#print axioms M12CriticalAssembly.line_dilation
#print axioms M12CriticalAssembly.plane_dilation
#print axioms M12CriticalAssembly.originalFockNorm_plane_dilation
#print axioms M12CriticalAssembly.critical_jacobian
#print axioms M12CriticalAssembly.normalized_originalFockNorm
