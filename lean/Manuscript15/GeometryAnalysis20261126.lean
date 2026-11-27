import Mathlib

/-! M15 §§9–11, frozen EQ499_508_SEPARATE edition, 25 November 2026.
Actual local derivatives, fundamental-form contractions, flux-norm
inequalities under the stated conservation hypotheses, and geometric
integrals. The Maxwell continuum existence and spectral-cluster theorems
are separate obligations. -/

open MeasureTheory Set
noncomputable section
namespace Manuscript15.GeometryAnalysis20261126

-- §9, eq:ridge-surface and prop:ridge-metric.
theorem immersion_x_derivative (R Phi : ℝ → ℝ) (x theta r Rp q : ℝ)
    (hR : HasDerivAt R Rp x) (hPhi : HasDerivAt Phi q x) :
    HasDerivAt (fun t => R t*r*Real.cos (theta+Phi t))
      (Rp*r*Real.cos (theta+Phi x)-R x*r*q*Real.sin (theta+Phi x)) x ∧
    HasDerivAt (fun t => R t*r*Real.sin (theta+Phi t))
      (Rp*r*Real.sin (theta+Phi x)+R x*r*q*Real.cos (theta+Phi x)) x := by
  have hA : HasDerivAt (fun t => theta+Phi t) q x := by
    exact hPhi.const_add theta
  constructor
  · convert (hR.mul_const r).mul hA.cos using 1 <;> first | rfl | ring | (funext z; try simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring) | (try simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring)
  · convert (hR.mul_const r).mul hA.sin using 1 <;> first | rfl | ring | (funext z; try simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring) | (try simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring)

theorem immersion_theta_derivative (r : ℝ → ℝ) (theta R phi rp : ℝ)
    (hr : HasDerivAt r rp theta) :
    HasDerivAt (fun t => R*r t*Real.cos (t+phi))
      (R*rp*Real.cos (theta+phi)-R*r theta*Real.sin (theta+phi)) theta ∧
    HasDerivAt (fun t => R*r t*Real.sin (t+phi))
      (R*rp*Real.sin (theta+phi)+R*r theta*Real.cos (theta+phi)) theta := by
  have hA : HasDerivAt (fun t : ℝ => t+phi) 1 theta :=
    (hasDerivAt_id theta).add_const phi
  constructor
  · convert (hr.const_mul R).mul hA.cos using 1 <;> first | rfl | ring | (funext z; try simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring) | (try simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring)
  · convert (hr.const_mul R).mul hA.sin using 1 <;> first | rfl | ring | (funext z; try simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring) | (try simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring)

-- Actual second x derivatives of the differentiated immersion, not merely
-- formal symbols for the first derivative.
theorem immersion_x_second_derivative
    (R Rp Phi q : ℝ → ℝ) (x theta r Rpp qp : ℝ)
    (hR : HasDerivAt R (Rp x) x) (hRp : HasDerivAt Rp Rpp x)
    (hPhi : HasDerivAt Phi (q x) x) (hq : HasDerivAt q qp x) :
    HasDerivAt
      (fun t => Rp t*r*Real.cos (theta+Phi t)-R t*r*q t*Real.sin (theta+Phi t))
      ((Rpp-R x*(q x)^2)*r*Real.cos (theta+Phi x)-
        (2*Rp x*q x+R x*qp)*r*Real.sin (theta+Phi x)) x ∧
    HasDerivAt
      (fun t => Rp t*r*Real.sin (theta+Phi t)+R t*r*q t*Real.cos (theta+Phi t))
      ((Rpp-R x*(q x)^2)*r*Real.sin (theta+Phi x)+
        (2*Rp x*q x+R x*qp)*r*Real.cos (theta+Phi x)) x := by
  have hA : HasDerivAt (fun t => theta+Phi t) (q x) x := by
    exact hPhi.const_add theta
  have hB := (hR.mul_const r).mul hq
  constructor
  · convert ((hRp.mul_const r).mul hA.cos).sub (hB.mul hA.sin) using 1 <;> first | rfl | (funext z; simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring) | (simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring)
  · convert ((hRp.mul_const r).mul hA.sin).add (hB.mul hA.cos) using 1 <;> first | rfl | (funext z; simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring) | (simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring)

-- Contractions with the unnormalised normal in the rotating frame.
theorem second_form_xx (R Rp Rpp Zp Zpp r rp q qp : ℝ) :
    (Zp*r)*((Rpp-R*q^2)*r)+(-Zp*rp)*((2*Rp*q+R*qp)*r)
      -r*(Rp*r-R*q*rp)*Zpp =
    Zp*((Rpp-R*q^2)*r^2-(2*Rp*q+R*qp)*r*rp)
      -r*(Rp*r-R*q*rp)*Zpp := by ring

theorem second_form_xtheta (R Rp Zp r rp q : ℝ) :
    (Zp*r)*(Rp*rp-R*r*q)+(-Zp*rp)*(Rp*r+R*rp*q) =
    -Zp*R*q*(r^2+rp^2) := by ring

theorem second_form_thetatheta (R Zp r rp rpp : ℝ) :
    (Zp*r)*(R*(rpp-r))+(-Zp*rp)*(2*R*rp) =
    -Zp*R*(r^2+2*rp^2-r*rpp) := by ring

theorem neck_gaussian (a k : ℝ) (ha : 0 < a) :
    (a^2*(1-k^2)*(-13*a^2/12)-(-a^2*k)^2)/a^6 =
    (k^2-13)/(12*a^2) := by
  field_simp [ha.ne'] <;> ring

theorem neck_mean (a k : ℝ) (ha : 0 < a) :
    (a^2*(1-k^2)*a^2-2*(-a^2*k)*(a^2*k)+
      (-13*a^2/12)*(a^2*(1+k^2)))/(2*a^5) =
    -(1+k^2)/(24*a) := by
  field_simp [ha.ne'] <;> ring

-- §10, prop:m15-transmission-eigenchannels.
section Flux
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem flux_difference (T : E →ₗ[ℂ] F) (R : E →ₗ[ℂ] G)
    (hflux : ∀ x, ‖T x‖^2+‖R x‖^2=‖x‖^2) (x y : E) :
    ‖x-y‖^2=‖T x-T y‖^2+‖R x-R y‖^2 := by
  simpa only [map_sub] using (hflux (x-y)).symm

theorem flux_rayleigh_bounds (T : E →ₗ[ℂ] F) (R : E →ₗ[ℂ] G)
    (hflux : ∀ x, ‖T x‖^2+‖R x‖^2=‖x‖^2) (x : E)
    (hx : ‖x‖=1) : 0 ≤ ‖T x‖^2 ∧ ‖T x‖^2 ≤ 1 := by
  have h := hflux x
  rw [hx, one_pow] at h
  exact ⟨sq_nonneg _, by linarith [sq_nonneg ‖R x‖]⟩

theorem transmission_lower_norm (T : E →ₗ[ℂ] F) (p : ℝ) (hp : 0 < p)
    (hmin : ∀ x, p*‖x‖^2 ≤ ‖T x‖^2) (x : E) :
    Real.sqrt p*‖x‖ ≤ ‖T x‖ := by
  have hsq : (Real.sqrt p*‖x‖)^2 = p*‖x‖^2 := by
    rw [mul_pow, Real.sq_sqrt hp.le]
  have hA : 0 ≤ Real.sqrt p*‖x‖ := by positivity
  have hB : 0 ≤ ‖T x‖ := norm_nonneg _
  have h := hmin x
  by_contra! hn
  have hpos : 0 < (Real.sqrt p*‖x‖-‖T x‖)*(Real.sqrt p*‖x‖+‖T x‖) :=
    mul_pos (sub_pos.mpr hn) (by linarith)
  nlinarith

theorem transmission_recovery_bound (T : E →ₗ[ℂ] F) (p : ℝ) (hp : 0 < p)
    (hmin : ∀ x, p*‖x‖^2 ≤ ‖T x‖^2) (x y : E) :
    ‖x-y‖ ≤ (1/Real.sqrt p)*‖T x-T y‖ := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  calc
    ‖x-y‖ ≤ ‖T (x-y)‖/Real.sqrt p :=
      (le_div_iff₀ hs).2 (by
        simpa only [mul_comm] using transmission_lower_norm T p hp hmin (x-y))
    _ = _ := by rw [map_sub]; ring

theorem transmission_recovery_sharp (T : E →ₗ[ℂ] F) (p K : ℝ) (hp : 0 < p)
    (x : E) (hx : ‖x‖=1) (hTx : ‖T x‖=Real.sqrt p)
    (hK : ∀ y, ‖y‖ ≤ K*‖T y‖) : 1/Real.sqrt p ≤ K := by
  have h := hK x
  rw [hx, hTx] at h
  exact (div_le_iff₀ (Real.sqrt_pos.2 hp)).2 h
end Flux

theorem selectivity_interval (pmin pmax : ℝ)
    (h0 : 0 ≤ pmin) (hord : pmin ≤ pmax) (h1 : pmax ≤ 1) :
    0 ≤ pmax-pmin ∧ pmax-pmin ≤ 1 := by
  constructor <;> linarith

-- §10, local regularisation: actual polynomial value and derivative jets.
def rounded (c0 c2 c4 t : ℝ) : ℝ := c0+c2*t^2+c4*t^4

theorem rounded_deriv (c0 c2 c4 t : ℝ) :
    HasDerivAt (rounded c0 c2 c4) (2*c2*t+4*c4*t^3) t := by
  unfold rounded
  have h := ((hasDerivAt_id t).pow 2 |>.const_mul c2).add
    ((hasDerivAt_id t).pow 4 |>.const_mul c4)
  convert h.const_add c0 using 1 <;> first | rfl | (funext z; simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring) | (simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring)

theorem rounded_matching (d f fp fpp : ℝ) (hd : d ≠ 0) :
    let c4 := (fpp+fp/d)/(8*d^2)
    let c2 := -fp/(2*d)-2*c4*d^2
    let c0 := f-c2*d^2-c4*d^4
    rounded c0 c2 c4 d = f ∧
    2*c2*d+4*c4*d^3 = -fp ∧
    2*c2+12*c4*d^2 = fpp := by
  dsimp [rounded]
  constructor
  · ring
  constructor <;> field_simp [hd] <;> ring

def smoothingPrimitive (t : ℝ) : ℝ := 3*t/8-t^2/2+t^3/4-t^5/40

theorem smoothing_primitive_deriv (t : ℝ) :
    HasDerivAt smoothingPrimitive ((1-t)^3*(t+3)/8) t := by
  unfold smoothingPrimitive
  have h1 := ((hasDerivAt_id t).const_mul (3:ℝ)).div_const 8
  have h2 := ((hasDerivAt_id t).pow 2).div_const 2
  have h3 := ((hasDerivAt_id t).pow 3).div_const 4
  have h5 := ((hasDerivAt_id t).pow 5).div_const 40
  convert ((h1.sub h2).add h3).sub h5 using 1 <;> first | rfl | (funext z; simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring) | (simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring)

theorem smoothing_integral :
    (∫ t in (0:ℝ)..1, (1-t)^3*(t+3)/8) = 1/10 := by
  have h : (∫ t in (0:ℝ)..1, (1-t)^3*(t+3)/8) =
      smoothingPrimitive 1-smoothingPrimitive 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _
      exact smoothing_primitive_deriv t
    · exact (by fun_prop : Continuous (fun t : ℝ => (1-t)^3*(t+3)/8)).intervalIntegrable 0 1
  rw [h]
  norm_num [smoothingPrimitive]

-- §11, prop:grav-hyd-comparison: genuine deltoid parameterisation.
def deltoidX (b t : ℝ) : ℝ := b*(2*Real.cos t+Real.cos (2*t))
def deltoidY (b t : ℝ) : ℝ := b*(2*Real.sin t-Real.sin (2*t))

theorem deltoid_derivatives (b t : ℝ) :
    HasDerivAt (deltoidX b) (-2*b*(Real.sin t+Real.sin (2*t))) t ∧
    HasDerivAt (deltoidY b) (2*b*(Real.cos t-Real.cos (2*t))) t := by
  unfold deltoidX deltoidY
  have h := (hasDerivAt_id t).const_mul (2:ℝ)
  constructor
  · convert (((Real.hasDerivAt_cos t).const_mul 2).add h.cos).const_mul b using 1 <;>
      first | rfl | (funext z; simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring) | (simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring)
  · convert (((Real.hasDerivAt_sin t).const_mul 2).sub h.sin).const_mul b using 1 <;>
      first | rfl | (funext z; simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring) | (simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring)

theorem deltoid_speed_squared (b t : ℝ) :
    (-2*b*(Real.sin t+Real.sin (2*t)))^2+
      (2*b*(Real.cos t-Real.cos (2*t)))^2 =
    8*b^2*(1-Real.cos (3*t)) := by
  have h1 := Real.sin_sq_add_cos_sq t
  have h2 := Real.sin_sq_add_cos_sq (2*t)
  have hc : Real.cos (3*t) = Real.cos t*Real.cos (2*t)-Real.sin t*Real.sin (2*t) := by
    rw [show 3*t=t+2*t by ring, Real.cos_add]
  linear_combination 4*b^2*h1+4*b^2*h2+8*b^2*hc

theorem deltoid_area_density (b t : ℝ) :
    (deltoidX b t*(2*b*(Real.cos t-Real.cos (2*t)))-
      deltoidY b t*(-2*b*(Real.sin t+Real.sin (2*t))))/2 =
    b^2*(1-Real.cos (3*t)) := by
  unfold deltoidX deltoidY
  have h1 := Real.sin_sq_add_cos_sq t
  have h2 := Real.sin_sq_add_cos_sq (2*t)
  have hc : Real.cos (3*t) = Real.cos t*Real.cos (2*t)-Real.sin t*Real.sin (2*t) := by
    rw [show 3*t=t+2*t by ring, Real.cos_add]
  linear_combination 2*b^2*h1-b^2*h2+b^2*hc

def deltoidAreaPrimitive (b t : ℝ) : ℝ := b^2*(t-Real.sin (3*t)/3)

theorem deltoid_area_primitive_deriv (b t : ℝ) :
    HasDerivAt (deltoidAreaPrimitive b) (b^2*(1-Real.cos (3*t))) t := by
  unfold deltoidAreaPrimitive
  have h := ((hasDerivAt_id t).const_mul (3:ℝ)).sin.div_const 3
  convert ((hasDerivAt_id t).sub h).const_mul (b^2) using 1 <;> first | rfl | (funext z; simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring) | (simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring)

theorem deltoid_signed_area_integral (b : ℝ) :
    (∫ t in (0:ℝ)..(2*Real.pi),
      (deltoidX b t*deriv (deltoidY b) t-deltoidY b t*deriv (deltoidX b) t)/2) =
    2*Real.pi*b^2 := by
  have hEq : (fun t : ℝ =>
      (deltoidX b t*deriv (deltoidY b) t-deltoidY b t*deriv (deltoidX b) t)/2) =
      (fun t => b^2*(1-Real.cos (3*t))) := by
    funext t
    rw [(deltoid_derivatives b t).1.deriv, (deltoid_derivatives b t).2.deriv]
    exact deltoid_area_density b t
  rw [hEq]
  have h : (∫ t in (0:ℝ)..(2*Real.pi), b^2*(1-Real.cos (3*t))) =
      deltoidAreaPrimitive b (2*Real.pi)-deltoidAreaPrimitive b 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _
      exact deltoid_area_primitive_deriv b t
    · exact (by fun_prop : Continuous (fun t : ℝ => b^2*(1-Real.cos (3*t)))).intervalIntegrable 0 (2*Real.pi)
  rw [h]
  unfold deltoidAreaPrimitive
  rw [show 3*(2*Real.pi)= (6:ℕ)*Real.pi by push_cast; ring, Real.sin_nat_mul_pi]
  simp <;> ring

end Manuscript15.GeometryAnalysis20261126

#print axioms Manuscript15.GeometryAnalysis20261126.immersion_x_derivative
#print axioms Manuscript15.GeometryAnalysis20261126.immersion_theta_derivative
#print axioms Manuscript15.GeometryAnalysis20261126.immersion_x_second_derivative
#print axioms Manuscript15.GeometryAnalysis20261126.second_form_xx
#print axioms Manuscript15.GeometryAnalysis20261126.second_form_xtheta
#print axioms Manuscript15.GeometryAnalysis20261126.second_form_thetatheta
#print axioms Manuscript15.GeometryAnalysis20261126.neck_gaussian
#print axioms Manuscript15.GeometryAnalysis20261126.neck_mean
#print axioms Manuscript15.GeometryAnalysis20261126.flux_difference
#print axioms Manuscript15.GeometryAnalysis20261126.flux_rayleigh_bounds
#print axioms Manuscript15.GeometryAnalysis20261126.transmission_lower_norm
#print axioms Manuscript15.GeometryAnalysis20261126.transmission_recovery_bound
#print axioms Manuscript15.GeometryAnalysis20261126.transmission_recovery_sharp
#print axioms Manuscript15.GeometryAnalysis20261126.selectivity_interval
#print axioms Manuscript15.GeometryAnalysis20261126.rounded_deriv
#print axioms Manuscript15.GeometryAnalysis20261126.rounded_matching
#print axioms Manuscript15.GeometryAnalysis20261126.smoothing_primitive_deriv
#print axioms Manuscript15.GeometryAnalysis20261126.smoothing_integral
#print axioms Manuscript15.GeometryAnalysis20261126.deltoid_derivatives
#print axioms Manuscript15.GeometryAnalysis20261126.deltoid_speed_squared
#print axioms Manuscript15.GeometryAnalysis20261126.deltoid_area_density
#print axioms Manuscript15.GeometryAnalysis20261126.deltoid_area_primitive_deriv
#print axioms Manuscript15.GeometryAnalysis20261126.deltoid_signed_area_integral
