import Mathlib

/-! M13 Proposition 4.11. Actual Lebesgue cosine integrals (the potential
is even), parameter differentiation and a locally uniform integrable bound.
The classical Cauchy cosine transform is an explicit premise of the general
frequency theorem, not an axiom or a replacement for the potential integral.
At zero frequency it is discharged using Mathlib's Cauchy integral.
The complex Fourier identification still requires cancellation of the odd sine part.
-/
open MeasureTheory Filter Set
open scoped Topology
namespace Manuscript13.EllisFourier20261124
noncomputable section

def cauchy (a u : ℝ) : ℝ := (u^2+a^2)⁻¹
def potential (a u : ℝ) : ℝ := a^2/(u^2+a^2)^2
def kernel (q a u : ℝ) : ℝ := Real.cos (q*u) * cauchy a u
def kernelDeriv (q a u : ℝ) : ℝ := -2*a*Real.cos (q*u)/(u^2+a^2)^2
def cauchyTransform (q a : ℝ) : ℝ := ∫ u : ℝ, kernel q a u
def potentialTransform (a q : ℝ) : ℝ := ∫ u : ℝ, potential a u * Real.cos (q*u)

theorem cauchy_integrable (a : ℝ) (ha : 0 < a) :
    Integrable (cauchy a) := by
  have h := (integrable_inv_one_add_mul_sq (b := a⁻¹) (inv_ne_zero (ne_of_gt ha))).const_mul (a^2)⁻¹
  apply h.congr
  filter_upwards [] with u
  unfold cauchy
  have hu : u^2+a^2 ≠ 0 := by positivity
  have hv : 1+(a⁻¹*u)^2 ≠ 0 := by positivity
  field_simp [ne_of_gt ha, hu, hv]
  <;> ring

theorem cauchy_mass (a : ℝ) (ha : 0 < a) :
    (∫ u : ℝ, cauchy a u) = Real.pi/a := by
  have hf : cauchy a = fun u : ℝ => (a^2)⁻¹ * (1+(a⁻¹*u)^2)⁻¹ := by
    funext u
    unfold cauchy
    have hu : u^2+a^2 ≠ 0 := by positivity
    have hv : 1+(a⁻¹*u)^2 ≠ 0 := by positivity
    field_simp [ne_of_gt ha, hu, hv]
    <;> ring
  rw [hf, integral_const_mul, integral_univ_inv_one_add_mul_sq, abs_of_pos (inv_pos.mpr ha)]
  field_simp [ne_of_gt ha]
  <;> ring

theorem kernel_integrable (q a : ℝ) (ha : 0 < a) :
    Integrable (kernel q a) := by
  apply (cauchy_integrable a ha).mono'
  · apply Continuous.aestronglyMeasurable
    unfold kernel cauchy
    have h : ∀ u : ℝ, u^2+a^2 ≠ 0 := fun u => by positivity
    exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
      ((continuous_id.pow 2 |>.add continuous_const).inv₀ h)
  · filter_upwards [] with u
    unfold kernel cauchy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (u^2+a^2)⁻¹)]
    exact mul_le_of_le_one_left (by positivity) (Real.abs_cos_le_one _)

theorem kernel_hasDerivAt (q a u : ℝ) (ha : 0 < a) :
    HasDerivAt (fun x => kernel q x u) (kernelDeriv q a u) a := by
  have h : u^2+a^2 ≠ 0 := by positivity
  have hd : HasDerivAt (fun x : ℝ => u^2+x^2) (2*a) a := by
    convert ((hasDerivAt_id a).pow 2).const_add (u^2) using 1
    · funext x
      simp [Pi.pow_apply]
    · simp <;> ring
  have hd' := (hd.inv h).const_mul (Real.cos (q*u))
  convert hd' using 1
  · rfl
  · unfold kernelDeriv
    ring

/-- An integrable Cauchy majorant for derivatives on a fixed neighbourhood. -/
theorem kernel_deriv_bound (q a x u : ℝ) (ha : 0 < a)
    (hx : x ∈ Ioo (a/2) (2*a)) :
    ‖kernelDeriv q x u‖ ≤ (16/a) * cauchy (a/2) u := by
  have hxpos : 0 < x := by linarith [hx.1]
  have hden : 0 < u^2+x^2 := by positivity
  have hsmall : 0 < u^2+(a/2)^2 := by positivity
  have hsquare : (a/2)^2 ≤ x^2 := by nlinarith [hx.1, mul_nonneg (le_of_lt (show 0 < x-a/2 by linarith [hx.1])) (show 0 ≤ x+a/2 by linarith)]
  have hle : u^2+(a/2)^2 ≤ u^2+x^2 := by linarith
  have hprod : (a/2)^2 * (u^2+(a/2)^2) ≤ (u^2+x^2)^2 := by
    calc
      _ ≤ (u^2+x^2)*(u^2+(a/2)^2) := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg u]) hsmall.le
      _ ≤ _ := by simpa [pow_two] using mul_le_mul_of_nonneg_left hle hden.le
  unfold kernelDeriv cauchy
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonpos (by linarith : -2*x ≤ 0), abs_of_nonneg (sq_nonneg (u^2+x^2))]
  have hn : -(-2*x)*|Real.cos (q*u)| ≤ 4*a := by
    calc
      _ ≤ -(-2*x) := mul_le_of_le_one_right (by linarith) (Real.abs_cos_le_one _)
      _ ≤ _ := by linarith [hx.2]
  calc
    _ ≤ (4*a)/(u^2+x^2)^2 := div_le_div_of_nonneg_right hn (by positivity)
    _ ≤ (4*a)/((a/2)^2*(u^2+(a/2)^2)) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hprod
    _ = _ := by field_simp [ne_of_gt ha, ne_of_gt hsmall] <;> ring

theorem actual_transform_derivative (q a : ℝ) (ha : 0 < a) :
    HasDerivAt (cauchyTransform q) (∫ u : ℝ, kernelDeriv q a u) a := by
  have hs : Ioo (a/2) (2*a) ∈ 𝓝 a := Ioo_mem_nhds (by linarith) (by linarith)
  have hm : ∀ᶠ x in 𝓝 a, AEStronglyMeasurable (kernel q x) volume := by
    filter_upwards [hs] with x hx
    exact (kernel_integrable q x (by linarith [hx.1])).aestronglyMeasurable
  have hdm : AEStronglyMeasurable (kernelDeriv q a) volume := by
    apply Continuous.aestronglyMeasurable
    unfold kernelDeriv
    have hd : ∀ u : ℝ, (u^2+a^2)^2 ≠ 0 := fun u => by positivity
    exact (continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).div
      ((continuous_id.pow 2 |>.add continuous_const).pow 2) hd
  have hb : Integrable (fun u => (16/a)*cauchy (a/2) u) :=
    (cauchy_integrable (a/2) (by positivity)).const_mul _
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm (kernel_integrable q a ha)
    hdm (Filter.Eventually.of_forall (fun u x hx => kernel_deriv_bound q a x u ha hx))
    hb (Filter.Eventually.of_forall (fun u x hx => kernel_hasDerivAt q x u (by linarith [hx.1])))).2

theorem derivative_to_potential (q a : ℝ) (ha : 0 < a) :
    (∫ u : ℝ, kernelDeriv q a u) = (-2/a) * potentialTransform a q := by
  unfold potentialTransform
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  unfold kernelDeriv potential
  have hd : u^2+a^2 ≠ 0 := by positivity
  field_simp [ne_of_gt ha, hd]
  <;> ring

/-- Classical Cauchy transform input, explicitly stated at the real cosine integral. -/
theorem actual_cosine_fourier (a q : ℝ) (ha : 0 < a)
    (hC : ∀ x : ℝ, 0 < x → cauchyTransform q x = Real.pi/x*Real.exp (-x*|q|)) :
    potentialTransform a q = Real.pi/(2*a)*(1+a*|q|)*Real.exp (-a*|q|) := by
  have hd := actual_transform_derivative q a ha
  have h1 : HasDerivAt (fun x : ℝ => Real.pi/x) (-Real.pi/a^2) a := by
    convert (hasDerivAt_const a Real.pi).div (hasDerivAt_id a) (ne_of_gt ha) using 1
    · rfl
    · simp [id_eq] <;> ring
  have h2 : HasDerivAt (fun x : ℝ => -x*|q|) (-|q|) a := by
    convert (hasDerivAt_id a).neg.mul_const |q| using 1
    · funext x
      simp
      <;> ring
    · ring
  have hcl := h1.mul h2.exp
  have heq : cauchyTransform q =ᶠ[𝓝 a] (fun x : ℝ => Real.pi/x*Real.exp (-x*|q|)) := by
    filter_upwards [Ioi_mem_nhds ha] with x hx
    exact hC x hx
  have he := (hd.congr_of_eventuallyEq heq.symm).unique hcl
  rw [derivative_to_potential q a ha] at he
  field_simp [ne_of_gt ha] at he ⊢
  nlinarith [he]

theorem actual_potential_mass (a : ℝ) (ha : 0 < a) :
    (∫ u : ℝ, potential a u) = Real.pi/(2*a) := by
  have h := actual_cosine_fourier a 0 ha (fun x hx => by
    simpa [cauchyTransform, kernel] using cauchy_mass x hx)
  simpa [potentialTransform] using h

end
end Manuscript13.EllisFourier20261124

#print axioms Manuscript13.EllisFourier20261124.cauchy_integrable
#print axioms Manuscript13.EllisFourier20261124.cauchy_mass
#print axioms Manuscript13.EllisFourier20261124.kernel_integrable
#print axioms Manuscript13.EllisFourier20261124.kernel_hasDerivAt
#print axioms Manuscript13.EllisFourier20261124.kernel_deriv_bound
#print axioms Manuscript13.EllisFourier20261124.actual_transform_derivative
#print axioms Manuscript13.EllisFourier20261124.derivative_to_potential
#print axioms Manuscript13.EllisFourier20261124.actual_cosine_fourier
#print axioms Manuscript13.EllisFourier20261124.actual_potential_mass
