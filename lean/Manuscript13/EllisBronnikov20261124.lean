import Mathlib

/-! M13 §4.4, Proposition 4.11 and Corollary 4.12.
Source TeX SHA256 e1414a23a860176025abd230843567c0fe9075d090f4e12dbecdad10d66d14e1.
First analytic checkpoint: actual scalar radius and potential, radial derivative,
Fourier parameter differentiation on the closed-form Cauchy transform,
and the actual Eulerian Fourier-average quadrature.
Not a proof of the full Fourier identity, geometric operator, or trace-class theorem.
-/
namespace Manuscript13.EllisBronnikov20261124

noncomputable section

def radius (a u : ℝ) : ℝ := Real.sqrt (u^2 + a^2)
def potential (a u : ℝ) : ℝ := a^2 / (u^2 + a^2)^2

theorem radius_pos (a u : ℝ) (ha : 0 < a) : 0 < radius a u := by
  unfold radius
  apply Real.sqrt_pos.2
  positivity

theorem radius_sq (a u : ℝ) : radius a u ^ 2 = u^2 + a^2 := by
  unfold radius
  exact Real.sq_sqrt (by positivity)

theorem potential_pos (a u : ℝ) (ha : 0 < a) : 0 < potential a u := by
  unfold potential
  positivity

theorem radius_derivative (a u : ℝ) (ha : 0 < a) :
    HasDerivAt (radius a) (u / radius a u) u := by
  have h : 0 < u^2 + a^2 := by positivity
  have hd : HasDerivAt (fun x : ℝ => x^2 + a^2) (2*u) u := by
    convert ((hasDerivAt_id u).pow 2).add_const (a^2) using 1
    · funext x
      simp [Pi.pow_apply, add_comm]
    · simp
      <;> ring
  have hs := hd.sqrt (ne_of_gt h)
  convert hs using 1 <;> unfold radius <;> ring

theorem radius_slope_derivative (a u : ℝ) (ha : 0 < a) :
    HasDerivAt (fun x => x / radius a x) (a^2 / radius a u ^ 3) u := by
  have hr := radius_pos a u ha
  have h := (hasDerivAt_id u).div (radius_derivative a u ha) (ne_of_gt hr)
  convert h using 1
  · rfl
  · simp only [id_eq, one_mul]
    field_simp [ne_of_gt hr]
    nlinarith [radius_sq a u]

theorem radial_potential_identity (a u : ℝ) (ha : 0 < a) :
    (a^2 / radius a u ^ 3) / radius a u = potential a u := by
  have hr := radius_pos a u ha
  have h : u^2+a^2 ≠ 0 := by positivity
  unfold potential
  rw [← radius_sq a u]
  field_simp [ne_of_gt hr]
  <;> ring

theorem effective_null_energy_negative (a u G : ℝ) (ha : 0 < a) (hG : 0 < G) :
    -potential a u / (4 * Real.pi * G) < 0 := by
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (potential_pos a u ha)) (by positivity)

def fourierClosed (a q : ℝ) : ℝ :=
  Real.pi / (2*a) * (1+a*|q|) * Real.exp (-a*|q|)

theorem fourierClosed_pos (a q : ℝ) (ha : 0 < a) :
    0 < fourierClosed a q := by
  unfold fourierClosed
  positivity

def avgPrimitive (c t : ℝ) : ℝ := -(2+c*t) * Real.exp (-c*t) / c

theorem avgPrimitive_derivative (c t : ℝ) (hc : c ≠ 0) :
    HasDerivAt (avgPrimitive c) ((1+c*t)*Real.exp (-c*t)) t := by
  have h1 : HasDerivAt (fun x : ℝ => -(2+c*x)) (-c) t := by
    convert (((hasDerivAt_id t).const_mul c).const_add 2).neg using 1
    · funext x
      simp
    · ring
  have h2 : HasDerivAt (fun x : ℝ => -c*x) (-c) t := by
    convert (hasDerivAt_id t).const_mul (-c) using 1
    · rfl
    · ring
  have hd := (h1.mul h2.exp).div_const c
  convert hd using 1
  · rfl
  · field_simp [hc]
    <;> ring

theorem actual_average_integral (c : ℝ) (hc : c ≠ 0) :
    (∫ t in (0:ℝ)..1, (1+c*t)*Real.exp (-c*t)) =
      (2-(2+c)*Real.exp (-c))/c := by
  have hi : IntervalIntegrable (fun t : ℝ => (1+c*t)*Real.exp (-c*t))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => avgPrimitive_derivative c t hc) hi]
  unfold avgPrimitive
  simp
  <;> ring

theorem actual_average_at_zero :
    (∫ t in (0:ℝ)..1, (1+0*t)*Real.exp (-0*t)) = 1 := by simp

theorem trace_prefactor (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) :
    (Real.pi/(2*a)) * (1/(2*Real.pi)) * (Real.pi/κ) =
      Real.pi/(4*a*κ) := by
  field_simp [ne_of_gt ha, ne_of_gt hk, ne_of_gt Real.pi_pos]
  <;> ring

end
end Manuscript13.EllisBronnikov20261124

#print axioms Manuscript13.EllisBronnikov20261124.radius_pos
#print axioms Manuscript13.EllisBronnikov20261124.radius_sq
#print axioms Manuscript13.EllisBronnikov20261124.potential_pos
#print axioms Manuscript13.EllisBronnikov20261124.radius_derivative
#print axioms Manuscript13.EllisBronnikov20261124.radius_slope_derivative
#print axioms Manuscript13.EllisBronnikov20261124.radial_potential_identity
#print axioms Manuscript13.EllisBronnikov20261124.effective_null_energy_negative
#print axioms Manuscript13.EllisBronnikov20261124.fourierClosed_pos
#print axioms Manuscript13.EllisBronnikov20261124.avgPrimitive_derivative
#print axioms Manuscript13.EllisBronnikov20261124.actual_average_integral
#print axioms Manuscript13.EllisBronnikov20261124.actual_average_at_zero
#print axioms Manuscript13.EllisBronnikov20261124.trace_prefactor
