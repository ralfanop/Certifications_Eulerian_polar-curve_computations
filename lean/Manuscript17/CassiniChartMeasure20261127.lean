import Mathlib
import Manuscript17.CassiniChartGeometry20261127

noncomputable section
namespace Manuscript17.CassiniChartMeasure

open Real Set MeasureTheory intervalIntegral
open Manuscript17.CassiniChartGeometry
open EulerianCert.CassiniAreaIntegral20261124

theorem altitude_derivative (u : ℝ) (h : u ∈ Ioo (0:ℝ) 1) :
    HasDerivAt altitude (-u/altitude u) u := by
  have hd := (hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_pow 2 u)
  have hs := (Real.hasDerivAt_sqrt (qpos u h).ne').comp u hd
  convert hs using 1
  · rfl
  · unfold altitude
    simp
    ring

/-- Coordinatewise differentiation of the actual sphere chart. -/
theorem chart_u_derivative (u p : ℝ) (h : u ∈ Ioo (0:ℝ) 1) (i : Fin 3) :
    HasDerivAt (fun v => chart v p i) (tangentU u p i) u := by
  fin_cases i
  · simpa [chart, tangentU] using (altitude_derivative u h).mul_const (cos p)
  · simpa [chart, tangentU] using (altitude_derivative u h).mul_const (sin p)
  · simpa [chart, tangentU] using (hasDerivAt_id' u)

theorem chart_p_derivative (u p : ℝ) (i : Fin 3) :
    HasDerivAt (fun v => chart u v i) (tangentP u p i) p := by
  fin_cases i
  · simpa [chart, tangentP] using (Real.hasDerivAt_cos p).const_mul (altitude u)
  · simpa [chart, tangentP] using (Real.hasDerivAt_sin p).const_mul (altitude u)
  · simpa [chart, tangentP] using (hasDerivAt_const p u)

theorem metric_positive (u p x y : ℝ) (h : u ∈ Ioo (0:ℝ) 1)
    (hn : x ≠ 0 ∨ y ≠ 0) :
    0 < metricUU u p*x^2 + 2*metricUP u p*x*y + metricPP u p*y^2 := by
  obtain ⟨hu,hp,hc⟩ := metric_components u p h
  have hq := qpos u h
  have hs : 0 < scale u := by
    unfold scale
    exact div_pos h.1 (by linarith)
  rw [hu,hp,hc]
  have h1 : 0 < scale u^2/(1-u^2) := by positivity
  have h2 : 0 < scale u^2*(1-u^2) := by positivity
  rcases hn with hx | hy
  · have hx2 : 0 < x^2 := sq_pos_of_ne_zero hx
    have hxp := mul_pos h1 hx2
    have hyn := mul_nonneg h2.le (sq_nonneg y)
    nlinarith
  · have hy2 : 0 < y^2 := sq_pos_of_ne_zero hy
    have hyp := mul_pos h2 hy2
    have hxn := mul_nonneg h1.le (sq_nonneg x)
    nlinarith

def altitudeMeasure : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Ioc 0 1)).withDensity (fun u => ENNReal.ofReal (areaDensity u))

def longitudeMeasure : Measure ℝ :=
  (volume : Measure ℝ).restrict (Ioc 0 (2*Real.pi))

/-- Weighted coordinate measure, not an assumed intrinsic manifold measure. -/
def coordinateMeasure : Measure (ℝ × ℝ) :=
  altitudeMeasure.prod longitudeMeasure

theorem altitude_mass :
    altitudeMeasure univ = ENNReal.ofReal (1/2-Real.log (1+Real.sqrt 2)/(2*Real.sqrt 2)) := by
  unfold altitudeMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hi : Integrable areaDensity ((volume : Measure ℝ).restrict (Ioc 0 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      areaDensity_intervalIntegrable
  have hn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioc 0 1)] areaDensity :=
    ae_of_all _ fun u => by unfold areaDensity; positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), areaDensity_integral]

theorem longitude_mass :
    longitudeMeasure univ = ENNReal.ofReal (2*Real.pi) := by
  simp [longitudeMeasure, Real.volume_Ioc]

theorem coordinate_mass :
    coordinateMeasure univ =
      ENNReal.ofReal (Real.pi*(1-Real.log (1+Real.sqrt 2)/Real.sqrt 2)) := by
  unfold coordinateMeasure
  have : SFinite longitudeMeasure := by unfold longitudeMeasure; infer_instance
  rw [← Set.univ_prod_univ, Measure.prod_prod, altitude_mass, longitude_mass]
  have hp : 0 ≤ 2*Real.pi := by positivity
  rw [← ENNReal.ofReal_mul' hp]
  congr 1
  have hs : (Real.sqrt 2:ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

/-- The measure on the embedded chart is the genuine pushforward. -/
def embeddedMeasure : Measure (Fin 3 → ℝ) :=
  Measure.map (fun z : ℝ × ℝ => chart z.1 z.2) coordinateMeasure

theorem chart_measurable : Measurable (fun z : ℝ × ℝ => chart z.1 z.2) := by
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> simp [chart, altitude] <;> fun_prop

theorem embedded_mass :
    embeddedMeasure univ =
      ENNReal.ofReal (Real.pi*(1-Real.log (1+Real.sqrt 2)/Real.sqrt 2)) := by
  rw [embeddedMeasure, Measure.map_apply chart_measurable MeasurableSet.univ,
    preimage_univ, coordinate_mass]

#print axioms altitude_derivative
#print axioms chart_u_derivative
#print axioms chart_p_derivative
#print axioms metric_positive
#print axioms altitude_mass
#print axioms longitude_mass
#print axioms coordinate_mass
#print axioms chart_measurable
#print axioms embedded_mass

end Manuscript17.CassiniChartMeasure
