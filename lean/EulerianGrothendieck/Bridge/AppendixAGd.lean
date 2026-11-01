import Bridge.AppendixA
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Appendix A (continued): the Gudermannian and Lambertian functions

Manuscript V173, eqs. (288)–(289).

* `gd ψ = arctan(sinh ψ)`; `gd` is strictly increasing, `|gd ψ| < π/2`, and `gd` maps `ℝ` onto
  `(-π/2, π/2)`;
* `gd⁻¹` (defined in `Bridge.AppendixA` as `∫_0^φ sec t dt`) is the inverse of `gd`:
  `gd⁻¹ (gd ψ) = ψ` and `gd (gd⁻¹ φ) = φ` for `|φ| < π/2`;
* `gd⁻¹ φ = log tan(π/4 + φ/2)` for `|φ| < π/2`.
-/

open Real intervalIntegral Set

namespace EulerianBridge.AppendixA

theorem gd_eq (ψ : ℝ) : gd ψ = arctan (sinh ψ) := by
  unfold gd
  have hd : ∀ u ∈ uIcc 0 ψ, HasDerivAt (fun u => arctan (sinh u)) (1 / cosh u) u := by
    intro u _
    have h := (hasDerivAt_sinh u).arctan
    convert h using 1
    have hc : 0 < cosh u := cosh_pos u
    rw [show 1 + sinh u ^ 2 = cosh u ^ 2 by rw [cosh_sq]; ring]
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hd]
  · simp
  · apply Continuous.intervalIntegrable
    exact continuous_const.div continuous_cosh (fun u => (cosh_pos u).ne')

theorem gd_strictMono : StrictMono gd := by
  intro a b hab
  rw [gd_eq, gd_eq]
  exact arctan_strictMono (sinh_strictMono hab)

theorem abs_gd_lt (ψ : ℝ) : |gd ψ| < π / 2 := by
  rw [gd_eq, abs_lt]
  exact ⟨neg_pi_div_two_lt_arctan _, arctan_lt_pi_div_two _⟩

theorem range_gd : range gd = Ioo (-(π / 2)) (π / 2) := by
  ext φ
  constructor
  · rintro ⟨ψ, rfl⟩
    exact abs_lt.mp (abs_gd_lt ψ)
  · intro hφ
    obtain ⟨ψ, hψ⟩ := sinh_surjective (tan φ)
    refine ⟨ψ, ?_⟩
    rw [gd_eq, hψ, arctan_tan hφ.1 hφ.2]

theorem sin_gd (ψ : ℝ) : sin (gd ψ) = tanh ψ := by
  rw [gd_eq, sin_arctan, show 1 + sinh ψ ^ 2 = cosh ψ ^ 2 by rw [cosh_sq]; ring,
    sqrt_sq (cosh_pos ψ).le, tanh_eq_sinh_div_cosh]

theorem arctanh_tanh (ψ : ℝ) : arctanh (tanh ψ) = ψ := by
  unfold arctanh
  have hc : 0 < cosh ψ := cosh_pos ψ
  have hq : (1 + tanh ψ) / (1 - tanh ψ) = exp (2 * ψ) := by
    rw [tanh_eq_sinh_div_cosh]
    have h1 : cosh ψ + sinh ψ = exp ψ := cosh_add_sinh ψ
    have h2 : cosh ψ - sinh ψ = exp (-ψ) := cosh_sub_sinh ψ
    have hne : cosh ψ - sinh ψ ≠ 0 := by rw [h2]; exact (exp_pos _).ne'
    rw [show 1 + sinh ψ / cosh ψ = (cosh ψ + sinh ψ) / cosh ψ by field_simp,
      show 1 - sinh ψ / cosh ψ = (cosh ψ - sinh ψ) / cosh ψ by field_simp,
      div_div_div_cancel_right₀ hc.ne', h1, h2, ← exp_sub]
    ring_nf
  rw [hq, log_exp]; ring

/-- `gd⁻¹ ∘ gd = id`. -/
theorem gdInv_gd (ψ : ℝ) : gdInv (gd ψ) = ψ := by
  rw [gdInv_eq_arctanh_sin (abs_gd_lt ψ), sin_gd, arctanh_tanh]

/-- `gd ∘ gd⁻¹ = id` on `(-π/2, π/2)`. -/
theorem gd_gdInv {φ : ℝ} (hφ : |φ| < π / 2) : gd (gdInv φ) = φ := by
  have : φ ∈ range gd := by rw [range_gd]; exact abs_lt.mp hφ
  obtain ⟨ψ, rfl⟩ := this
  rw [gdInv_gd]

/-- Eq. (289): `gd⁻¹ φ = log tan(π/4 + φ/2)` for `|φ| < π/2`. -/
theorem gdInv_eq_log_tan {φ : ℝ} (hφ : |φ| < π / 2) : gdInv φ = log (tan (π / 4 + φ / 2)) := by
  rw [gdInv_eq_arctanh_sin hφ]
  have hφ' := abs_lt.mp hφ
  set u := φ / 2 with hu
  have hφu : φ = 2 * u := by rw [hu]; ring
  have ha0 : 0 < π / 4 + u := by linarith
  have ha1 : π / 4 + u < π / 2 := by linarith
  have htpos : 0 < tan (π / 4 + u) := tan_pos_of_pos_of_lt_pi_div_two ha0 ha1
  have hcos : 0 < cos (π / 4 + u) := cos_pos_of_mem_Ioo ⟨by linarith, ha1⟩
  have hs2 : sin (π / 4) = cos (π / 4) := by rw [sin_pi_div_four, cos_pi_div_four]
  have hcpos : 0 < cos (π / 4) := by rw [cos_pi_div_four]; positivity
  -- tan(π/4+u) = (cos u + sin u)/(cos u - sin u)
  have hcs : 0 < cos u - sin u := by
    have : cos (π / 4 + u) = cos (π / 4) * (cos u - sin u) := by rw [cos_add, hs2]; ring
    rw [this] at hcos; exact pos_of_mul_pos_right hcos hcpos.le
  have htan : tan (π / 4 + u) = (cos u + sin u) / (cos u - sin u) := by
    rw [tan_eq_sin_div_cos, sin_add, cos_add, hs2]
    field_simp
  have hsq : tan (π / 4 + u) ^ 2 = (1 + sin φ) / (1 - sin φ) := by
    rw [htan, div_pow, hφu, sin_two_mul]
    have h1 : (cos u + sin u) ^ 2 = 1 + 2 * sin u * cos u := by nlinarith [sin_sq_add_cos_sq u]
    have h2 : (cos u - sin u) ^ 2 = 1 - 2 * sin u * cos u := by nlinarith [sin_sq_add_cos_sq u]
    rw [h1, h2]
  unfold arctanh
  rw [← hsq, log_pow]
  push_cast
  ring

end EulerianBridge.AppendixA
