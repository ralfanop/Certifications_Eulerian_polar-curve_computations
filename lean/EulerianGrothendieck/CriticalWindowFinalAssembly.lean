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


/-- Numerical identity that converts the sine-profile scaling into the
standardized uniform MGF scaling, without approximate constants. -/
theorem root_ratio :
    Real.sqrt 6 / (2 * Real.sqrt 3) = 1 / Real.sqrt 2 := by
  have h2 : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt (3:ℝ))^2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 : (Real.sqrt (6:ℝ))^2 = 6 := Real.sq_sqrt (by norm_num)
  have hsquares : (Real.sqrt 6 * Real.sqrt 2)^2 =
      (2*Real.sqrt 3)^2 := by
    calc
      _ = (Real.sqrt 6)^2*(Real.sqrt 2)^2 := by ring
      _ = (6:ℝ)*2 := by rw [h6, h2]
      _ = (2*Real.sqrt 3)^2 := by rw [mul_pow, h3]; norm_num
  have hroots : Real.sqrt 6 * Real.sqrt 2 = 2*Real.sqrt 3 :=
    (sq_eq_sq₀ (by positivity) (by positivity)).mp hsquares
  have hn2 : Real.sqrt (2:ℝ) ≠ 0 := by positivity
  have hn3 : Real.sqrt (3:ℝ) ≠ 0 := by positivity
  field_simp [hn2, hn3]
  exact hroots

/-- Actual complex profile at the anisotropically rescaled Fock point is
exactly the genuine complex MGF m(q), with q=(e*u-i*e²*w)/sqrt(2). -/
theorem actual_profile_scaled (e u w : ℝ) :
    M12FockDomination.fockProfile
        (((Real.sqrt 6 * e^2 * w : ℝ) : ℂ) +
         ((Real.sqrt 6 * e * u : ℝ) : ℂ)*Complex.I) =
    M12ComplexMGF.mgf
        (((u*e/Real.sqrt 2 : ℝ) : ℂ) +
         ((-w*e^2/Real.sqrt 2 : ℝ) : ℂ)*Complex.I) := by
  have hs3 : ((Real.sqrt (3:ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show Real.sqrt (3:ℝ) ≠ 0 by positivity)
  have hsratio : (Real.sqrt (6:ℝ) : ℂ) /
      (2*(Real.sqrt (3:ℝ) : ℂ)) = 1/(Real.sqrt (2:ℝ) : ℂ) := by
    exact_mod_cast root_ratio
  rw [M12FockDomination.fockProfile_eq_mgf]
  congr 1
  calc
    -(((((Real.sqrt 6 * e^2 * w : ℝ) : ℂ) +
       ((Real.sqrt 6 * e * u : ℝ) : ℂ)*Complex.I)/2)*Complex.I)/
       (Real.sqrt 3 : ℂ) =
       ((Real.sqrt 6 : ℂ)/(2*(Real.sqrt 3 : ℂ))) * ((e*u : ℝ) : ℂ) -
       ((Real.sqrt 6 : ℂ)/(2*(Real.sqrt 3 : ℂ))) *
         ((e^2*w : ℝ) : ℂ)*Complex.I := by
      push_cast
      field_simp [hs3]
      ring
    _ = ((u*e/Real.sqrt 2 : ℝ) : ℂ) +
          ((-w*e^2/Real.sqrt 2 : ℝ) : ℂ)*Complex.I := by
      rw [hsratio]
      push_cast
      ring

/-- The transformed *original* sine Fock kernel agrees pointwise with the
already certified actual-MGF scaled integrand; no surrogate profile. -/
theorem actual_originalKernel_scaled (M : ℕ) (e lam u w : ℝ) :
    originalKernel M ((1/12+lam*e^2)*(M:ℝ))
      ((Real.sqrt 6*e^2)*w) ((Real.sqrt 6*e)*u) =
      M12FockDomination.scaledIntegrand M e lam u w := by
  have hs : (Real.sqrt (6:ℝ))^2 = 6 := Real.sq_sqrt (by norm_num)
  have hgauss :
      -((1/12+lam*e^2)*(M:ℝ)) *
        ((((Real.sqrt 6*e^2)*w)^2)+(((Real.sqrt 6*e)*u)^2)) =
      -6*(1/12+lam*e^2)*(M:ℝ)*(u^2*e^2+w^2*e^4) := by
    calc
      _ = -((1/12+lam*e^2)*(M:ℝ)) *
          ((Real.sqrt 6)^2*(e^4*w^2+e^2*u^2)) := by ring
      _ = _ := by rw [hs]; ring
  unfold originalKernel M12FockDomination.scaledIntegrand
  rw [actual_profile_scaled, hgauss]

/-- The exact, *genuine* Fock-normalization equation in the same scaled
integrand to which #507's global envelope applies. -/
theorem normalized_Fock_eq_actual_scaled_integrand
    (M : ℕ) (e lam : ℝ)
    (he : 0 < e) (hM : (M:ℝ)*e^4=1) :
    e * originalFockNorm M ((1/12+lam*e^2)*(M:ℝ)) =
      (6*(1/12+lam*e^2)/Real.pi) *
        (∫ w : ℝ, ∫ u : ℝ, M12FockDomination.scaledIntegrand M e lam u w) := by
  rw [normalized_originalFockNorm M e lam he hM]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with w
  apply integral_congr_ae
  filter_upwards [] with u
  exact actual_originalKernel_scaled M e lam u w

end M12CriticalAssembly

#print axioms M12CriticalAssembly.line_dilation
#print axioms M12CriticalAssembly.plane_dilation
#print axioms M12CriticalAssembly.originalFockNorm_plane_dilation
#print axioms M12CriticalAssembly.critical_jacobian
#print axioms M12CriticalAssembly.normalized_originalFockNorm

#print axioms M12CriticalAssembly.root_ratio
#print axioms M12CriticalAssembly.actual_profile_scaled
#print axioms M12CriticalAssembly.actual_originalKernel_scaled
#print axioms M12CriticalAssembly.normalized_Fock_eq_actual_scaled_integrand
