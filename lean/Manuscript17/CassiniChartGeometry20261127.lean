import Mathlib
import EulerianCert.CassiniAreaIntegral20261124

noncomputable section
namespace Manuscript17.CassiniChartGeometry

open Real Set MeasureTheory intervalIntegral
open EulerianCert.CassiniAreaIntegral20261124

/-! Coordinate realization of the regular lobe in altitude and longitude.
The chart excludes pole and equator. The classical conformal curvature law
is used to define the coordinate curvature expression; global manifold
measure identification and metric completion are separate obligations. -/

def scale (u : ℝ) : ℝ := u / (2 - u^2)
def altitude (u : ℝ) : ℝ := Real.sqrt (1-u^2)
def chart (u p : ℝ) : Fin 3 → ℝ :=
  ![altitude u * Real.cos p, altitude u * Real.sin p, u]

def tangentU (u p : ℝ) : Fin 3 → ℝ :=
  ![-u / altitude u * Real.cos p, -u / altitude u * Real.sin p, 1]
def tangentP (u p : ℝ) : Fin 3 → ℝ :=
  ![-altitude u * Real.sin p, altitude u * Real.cos p, 0]
def dot3 (a b : Fin 3 → ℝ) : ℝ := a 0*b 0+a 1*b 1+a 2*b 2

theorem qpos (u : ℝ) (h : u ∈ Ioo (0:ℝ) 1) : 0 < 1-u^2 := by
  have h0 := h.1
  have h1 := h.2
  nlinarith [mul_pos (sub_pos.mpr h1) (show 0 < 1+u by linarith)]

theorem alt_sq (u : ℝ) (h : u ∈ Ioo (0:ℝ) 1) :
    altitude u ^ 2 = 1-u^2 :=
  Real.sq_sqrt (qpos u h).le

theorem alt_pos (u : ℝ) (h : u ∈ Ioo (0:ℝ) 1) : 0 < altitude u :=
  Real.sqrt_pos.2 (qpos u h)

theorem chart_unit (u p : ℝ) (h : u ∈ Ioo (0:ℝ) 1) :
    dot3 (chart u p) (chart u p) = 1 := by
  simp [dot3, chart]
  have hs := Real.sin_sq_add_cos_sq p
  have ha := alt_sq u h
  calc
    altitude u * cos p * (altitude u * cos p) +
        altitude u * sin p * (altitude u * sin p) + u*u
        = altitude u ^ 2 * (sin p ^ 2 + cos p ^ 2) + u^2 := by ring
    _ = 1 := by rw [hs, ha]; ring

theorem round_cross (u p : ℝ) : dot3 (tangentU u p) (tangentP u p) = 0 := by
  simp [dot3, tangentU, tangentP]
  ring

theorem round_pp (u p : ℝ) (h : u ∈ Ioo (0:ℝ) 1) :
    dot3 (tangentP u p) (tangentP u p) = 1-u^2 := by
  simp [dot3, tangentP]
  calc
    (-altitude u * sin p) * (-altitude u * sin p) +
        altitude u * cos p * (altitude u * cos p)
        = altitude u^2 * (sin p^2 + cos p^2) := by ring
    _ = 1-u^2 := by rw [Real.sin_sq_add_cos_sq, alt_sq u h]; ring

theorem round_uu (u p : ℝ) (h : u ∈ Ioo (0:ℝ) 1) :
    dot3 (tangentU u p) (tangentU u p) = 1/(1-u^2) := by
  simp [dot3, tangentU]
  calc
    -u / altitude u * cos p * (-u / altitude u * cos p) +
        -u / altitude u * sin p * (-u / altitude u * sin p) + 1
        = (u^2 / altitude u^2) * (sin p^2+cos p^2)+1 := by ring
    _ = 1/(1-u^2) := by
      rw [Real.sin_sq_add_cos_sq, alt_sq u h]
      field_simp [ne_of_gt (qpos u h)]
      <;> ring

def metricUU (u p : ℝ) : ℝ := scale u ^ 2 * dot3 (tangentU u p) (tangentU u p)
def metricPP (u p : ℝ) : ℝ := scale u ^ 2 * dot3 (tangentP u p) (tangentP u p)
def metricUP (u p : ℝ) : ℝ := scale u ^ 2 * dot3 (tangentU u p) (tangentP u p)

theorem metric_components (u p : ℝ) (h : u ∈ Ioo (0:ℝ) 1) :
    metricUU u p = scale u^2/(1-u^2) ∧
    metricPP u p = scale u^2*(1-u^2) ∧ metricUP u p = 0 := by
  simp [metricUU, metricPP, metricUP, round_uu u p h, round_pp u p h, round_cross, div_eq_mul_inv]

theorem chart_area_density (u p : ℝ) (h : u ∈ Ioo (0:ℝ) 1) :
    Real.sqrt (metricUU u p * metricPP u p - metricUP u p ^ 2) = areaDensity u := by
  obtain ⟨hu,hp,hc⟩ := metric_components u p h
  rw [hu,hp,hc]
  have he : scale u^2 / (1-u^2) * (scale u^2 * (1-u^2)) - (0:ℝ)^2 =
      (scale u^2)^2 := by
    field_simp [ne_of_gt (qpos u h)]
    <;> ring
  rw [he, Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp [scale, areaDensity, div_pow]

/-- Actual derivative of log conformal factor on northern chart. -/
def logFactor (u : ℝ) := Real.log u - Real.log (2-u^2)
def first (u : ℝ) := 1/u + 2*u/(2-u^2)
def second (u : ℝ) := -1/u^2 + 2*(2+u^2)/(2-u^2)^2

theorem hasDerivAt_logFactor (u : ℝ) (h : u ∈ Ioo (0:ℝ) 1) :
    HasDerivAt logFactor (first u) u := by
  have hq : 0 < 2-u^2 := by linarith [qpos u h]
  have hd := ((hasDerivAt_const u (2:ℝ)).sub (hasDerivAt_pow 2 u)).log hq.ne'
  have hl := (hasDerivAt_id u).log h.1.ne'
  convert hl.sub hd using 1
  · rfl
  · simp [first]
    ring

theorem hasDerivAt_first (u : ℝ) (h : u ∈ Ioo (0:ℝ) 1) :
    HasDerivAt first (second u) u := by
  have hq : 0 < 2-u^2 := by linarith [qpos u h]
  have hd := (hasDerivAt_const u (2:ℝ)).sub (hasDerivAt_pow 2 u)
  have hnum := (hasDerivAt_id u).const_mul (2:ℝ)
  have ha := (hasDerivAt_const u (1:ℝ)).div (hasDerivAt_id u) h.1.ne'
  have hb := hnum.div hd hq.ne'
  convert ha.add hb using 1
  · rfl
  · simp [second]
    field_simp [h.1.ne', hq.ne']
    <;> ring

def chartCurvature (u : ℝ) : ℝ :=
  (1-((1-u^2)*deriv (deriv logFactor) u-2*u*deriv logFactor u))/scale u^2

theorem chart_curvature (u : ℝ) (h : u ∈ Ioo (0:ℝ) 1) :
    chartCurvature u = 3+4/u^4 := by
  have hq : 0 < 2-u^2 := by linarith [qpos u h]
  have he : deriv logFactor =ᶠ[nhds u] first := by
    filter_upwards [isOpen_Ioo.mem_nhds h] with v hv
    exact (hasDerivAt_logFactor v hv).deriv
  have hder : deriv (deriv logFactor) u = second u :=
    (he.deriv_eq).trans (hasDerivAt_first u h).deriv
  rw [chartCurvature, hder, (hasDerivAt_logFactor u h).deriv]
  unfold first second scale
  field_simp [h.1.ne', hq.ne']
  <;> ring

/-- Actual interval integral of the longitude-independent metric density. -/
theorem chart_area :
    (∫ u in (0:ℝ)..1, ∫ p in (0:ℝ)..(2*Real.pi), areaDensity u) =
    Real.pi*(1-Real.log (1+Real.sqrt 2)/Real.sqrt 2) := by
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [← intervalIntegral.integral_const_mul]
  exact area_integration

#print axioms qpos
#print axioms alt_sq
#print axioms alt_pos
#print axioms chart_unit
#print axioms round_cross
#print axioms round_pp
#print axioms round_uu
#print axioms metric_components
#print axioms chart_area_density
#print axioms hasDerivAt_logFactor
#print axioms hasDerivAt_first
#print axioms chart_curvature
#print axioms chart_area

end Manuscript17.CassiniChartGeometry
