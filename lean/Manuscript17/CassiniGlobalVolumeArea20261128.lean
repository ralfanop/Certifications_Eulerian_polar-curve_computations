import Mathlib
import Manuscript17.CassiniGlobalGraph20261128
import Manuscript17.CassiniChartGeometry20261127

noncomputable section
namespace Manuscript17.CassiniGlobalVolumeArea

open Set MeasureTheory intervalIntegral
open Manuscript17.CassiniGlobalGraph
open EulerianCert.CassiniAreaIntegral20261124

def hRad (r : ℝ) := Real.sqrt (1-r^2)
def radialDensity (r : ℝ) := r * hRad r / (1+r^2)^2

theorem hRad_derivative (r : ℝ) (hr : r ∈ Ioo (0:ℝ) 1) :
    HasDerivAt hRad (-r/hRad r) r := by
  have h : 0 < 1-r^2 := by nlinarith [hr.1,hr.2]
  have hd := (hasDerivAt_const r (1:ℝ)).sub (hasDerivAt_pow 2 r)
  have hs := (Real.hasDerivAt_sqrt h.ne').comp r hd
  convert hs using 1
  · rfl
  · simp [hRad]; ring

theorem radial_substitution (r : ℝ) (hr : r ∈ Ioo (0:ℝ) 1) :
    areaDensity (hRad r) * (-r/hRad r) = -radialDensity r := by
  have h : 0 < 1-r^2 := by nlinarith [hr.1,hr.2]
  have hs : hRad r^2 = 1-r^2 := Real.sq_sqrt h.le
  have hp : 0 < hRad r := Real.sqrt_pos.2 h
  unfold areaDensity radialDensity
  rw [show 2-hRad r^2 = 1+r^2 by linarith]
  have hq : 0 < 1+r^2 := by positivity
  field_simp [hp.ne',hq.ne']
  <;> ring

theorem radial_integral :
    (∫ r in (0:ℝ)..1, radialDensity r) =
      1/2-Real.log (1+Real.sqrt 2)/(2*Real.sqrt 2) := by
  have hc : Continuous hRad := by unfold hRad; fun_prop
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (f := hRad) (f' := fun r => -r/hRad r) (g := areaDensity)
    (a := (0:ℝ)) (b := 1) hc.continuousOn
    (fun r hr => hRad_derivative r (by simpa using hr))
    (fun r hr => by
      have hr' : r ∈ Ioo (0:ℝ) 1 := by simpa using hr
      have hp : 0 < hRad r := Real.sqrt_pos.2 (by nlinarith [hr'.1,hr'.2])
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hr'.1]) hp.le)
  have he : (∫ r in (0:ℝ)..1, (areaDensity ∘ hRad) r * (-r/hRad r)) =
      ∫ r in (0:ℝ)..1, -radialDensity r := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro r hr
    exact radial_substitution r hr
  rw [he, intervalIntegral.integral_neg] at h
  have hz : hRad 0 = 1 := by norm_num [hRad]
  have ho : hRad 1 = 0 := by norm_num [hRad]
  rw [hz,ho,intervalIntegral.integral_symm 0 1,areaDensity_integral] at h
  linarith

def polarPoint (p : ℝ × ℝ) : ℝ × ℝ :=
    (p.1*Real.cos p.2,p.1*Real.sin p.2)

theorem polar_radius (p : ℝ × ℝ) :
    (polarPoint p).1^2+(polarPoint p).2^2 = p.1^2 := by
  unfold polarPoint
  dsimp
  linear_combination p.1^2 * (Real.sin_sq_add_cos_sq p.2)

theorem polar_disk (p : ℝ × ℝ) (hp : 0 < p.1) :
    polarPoint p ∈ disk ↔ p.1 < 1 := by
  change (polarPoint p).1^2+(polarPoint p).2^2 < 1 ↔ p.1 < 1
  rw [polar_radius]
  constructor <;> intro h <;> nlinarith

theorem polar_density (p : ℝ × ℝ) (hp : p.1 ∈ Ioo (0:ℝ) 1) :
    p.1 * density (polarPoint p) = radialDensity p.1 := by
  rw [density_formula _ ((polar_disk p hp.1).2 hp.2)]
  unfold radialDensity hRad height
  have he : 1-(polarPoint p).1^2-(polarPoint p).2^2 = 1-p.1^2 := by
    linarith [polar_radius p]
  rw [he]
  have he' : 1+(polarPoint p).1^2+(polarPoint p).2^2 = 1+p.1^2 := by
    linarith [polar_radius p]
  rw [he']
  ring

/-- Actual two-dimensional integral in the global disk, using Mathlib's
polar-coordinate change of variables and Fubini. -/
theorem disk_integral :
    (∫ p in disk, density p) =
      Real.pi*(1-Real.log (1+Real.sqrt 2)/Real.sqrt 2) := by
  classical
  let f : ℝ × ℝ → ℝ := disk.indicator density
  have hf := integral_comp_polarCoord_symm f
  have h1 : (∫ p, f p) = ∫ p in disk, density p := by
    exact integral_indicator disk_measurable
  rw [h1] at hf
  have h2 : (∫ p in polarCoord.target, p.1 • f (polarCoord.symm p)) =
      ∫ p in Ioo (0:ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi, radialDensity p.1 := by
    rw [← MeasureTheory.integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
    rw [← MeasureTheory.integral_indicator polarCoord.open_target.measurableSet]
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro p
    have ht : p ∈ polarCoord.target ↔ 0 < p.1 ∧ -Real.pi < p.2 ∧ p.2 < Real.pi := by rfl
    by_cases hp : p ∈ polarCoord.target
    · have h := ht.mp hp
      rw [Set.indicator_of_mem hp]
      change p.1 * f (polarPoint p) = _
      by_cases hr : p.1 < 1
      · rw [Set.indicator_of_mem (show p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi from ⟨⟨h.1,hr⟩,h.2⟩)]
        dsimp [f]
        rw [Set.indicator_of_mem ((polar_disk p h.1).2 hr)]
        exact polar_density p ⟨h.1,hr⟩
      · rw [Set.indicator_of_notMem (show p ∉ Ioo (0:ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi from fun h' => hr h'.1.2)]
        dsimp [f]
        rw [Set.indicator_of_notMem (fun h' => hr ((polar_disk p h.1).1 h')),mul_zero]
    · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem]
      exact fun h => hp (ht.mpr ⟨h.1.1,h.2⟩)
  rw [h2] at hf
  rw [← hf]
  have hprod := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) radialDensity (fun _ : ℝ => (1:ℝ)) (Ioo 0 1) (Ioo (-Real.pi) Real.pi)
  simp only [mul_one] at hprod
  rw [Measure.volume_eq_prod, hprod]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), radial_integral]
  simp [MeasureTheory.integral_const, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0 ≤ Real.pi - -Real.pi)]
  rw [max_eq_left (by positivity : (0:ℝ) ≤ Real.pi + Real.pi)]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hs]
  <;> ring

#print axioms hRad_derivative
#print axioms radial_substitution
#print axioms radial_integral
#print axioms polar_radius
#print axioms polar_disk
#print axioms polar_density
#print axioms disk_integral
end Manuscript17.CassiniGlobalVolumeArea
