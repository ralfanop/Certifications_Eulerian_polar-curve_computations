import Mathlib
import Manuscript17.CassiniPolynomialLift20261127

noncomputable section
namespace Manuscript17.CassiniMeridian

open Real Set intervalIntegral
open Manuscript17.CassiniPolynomialLift

/-! Latitude parameter s in [0,pi/2]. Exact length density for the
actual pullback metric; the equator is at s=0 and pole at s=pi/2.
The distance induced by infima over all paths is a further construction. -/

def latitude (s p : ℝ) : Fin 3 → ℝ := ![cos s*cos p,cos s*sin p,sin s]
def meridianTangent (s p : ℝ) : Fin 3 → ℝ :=
  ![-sin s*cos p,-sin s*sin p,cos s]
def parallelTangent (s p : ℝ) : Fin 3 → ℝ :=
  ![-cos s*sin p,cos s*cos p,0]

theorem latitude_unit (s p : ℝ) : sphereDot (latitude s p) (latitude s p) = 1 := by
  simp [sphereDot,latitude]
  calc
    cos s*cos p*(cos s*cos p)+cos s*sin p*(cos s*sin p)+sin s*sin s =
      cos s^2*(sin p^2+cos p^2)+sin s^2 := by ring
    _ = 1 := by rw [sin_sq_add_cos_sq]; nlinarith [sin_sq_add_cos_sq s]

theorem meridian_unit (s p : ℝ) : sphereDot (meridianTangent s p) (meridianTangent s p) = 1 := by
  simp [sphereDot,meridianTangent]
  calc
    sin s*cos p*(sin s*cos p)+sin s*sin p*(sin s*sin p)+cos s*cos s =
      sin s^2*(sin p^2+cos p^2)+cos s^2 := by ring
    _ = 1 := by rw [sin_sq_add_cos_sq, mul_one, sin_sq_add_cos_sq]

theorem parallel_square (s p : ℝ) :
    sphereDot (parallelTangent s p) (parallelTangent s p) = cos s^2 := by
  simp [sphereDot,parallelTangent]
  calc
    cos s*sin p*(cos s*sin p)+cos s*cos p*(cos s*cos p) =
      cos s^2*(sin p^2+cos p^2) := by ring
    _ = _ := by rw [sin_sq_add_cos_sq,mul_one]

theorem meridian_orthogonal (s p : ℝ) :
    sphereDot (latitude s p) (meridianTangent s p) = 0 := by
  simp [sphereDot,latitude,meridianTangent]
  linear_combination -(sin s*cos s)*(sin_sq_add_cos_sq p)

theorem parallel_orthogonal (s p : ℝ) :
    sphereDot (latitude s p) (parallelTangent s p) = 0 := by
  simp [sphereDot,latitude,parallelTangent]
  ring

theorem latitude_derivative (s p : ℝ) (i : Fin 3) :
    HasDerivAt (fun a => latitude a p i) (meridianTangent s p i) s := by
  fin_cases i
  · simpa [latitude,meridianTangent] using (Real.hasDerivAt_cos s).mul_const (cos p)
  · simpa [latitude,meridianTangent] using (Real.hasDerivAt_cos s).mul_const (sin p)
  · simpa [latitude,meridianTangent] using Real.hasDerivAt_sin s

theorem longitude_derivative (s p : ℝ) (i : Fin 3) :
    HasDerivAt (fun a => latitude s a i) (parallelTangent s p i) p := by
  fin_cases i
  · simpa [latitude,parallelTangent,mul_comm] using (Real.hasDerivAt_cos p).const_mul (cos s)
  · simpa [latitude,parallelTangent] using (Real.hasDerivAt_sin p).const_mul (cos s)
  · simpa [latitude,parallelTangent] using hasDerivAt_const p (sin s)

def meridianSpeed (s : ℝ) := sin s/(1+cos s^2)
def parallelSpeed (s : ℝ) := meridianSpeed s*cos s

theorem scale_latitude (s p : ℝ) : t (latitude s p) = meridianSpeed s := by
  simp [t,latitude,meridianSpeed]
  rw [show 2-sin s^2 = 1+cos s^2 by nlinarith [sin_sq_add_cos_sq s]]

theorem meridianSpeed_nonneg (s : ℝ) (hs : s ∈ Icc (0:ℝ) (π/2)) :
    0 ≤ meridianSpeed s := by
  apply div_nonneg
  · exact sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2,pi_pos])
  · positivity

theorem meridian_metric_speed (s p dt : ℝ) (hs : s ∈ Icc (0:ℝ) (π/2)) :
    sqrt (EulerianCert.CassiniFeffermanTangent20261124.B
      (tangent (latitude s p) (meridianTangent s p) dt)
      (tangent (latitude s p) (meridianTangent s p) dt)) = meridianSpeed s := by
  rw [tangent_metric _ _ _ _ _ (latitude_unit s p) (meridian_orthogonal s p)
    (meridian_orthogonal s p),meridian_unit,mul_one,scale_latitude,
    sqrt_sq_eq_abs,abs_of_nonneg (meridianSpeed_nonneg s hs)]

theorem parallel_metric_speed (s p dt : ℝ) (hs : s ∈ Icc (0:ℝ) (π/2)) :
    sqrt (EulerianCert.CassiniFeffermanTangent20261124.B
      (tangent (latitude s p) (parallelTangent s p) dt)
      (tangent (latitude s p) (parallelTangent s p) dt)) = parallelSpeed s := by
  rw [tangent_metric _ _ _ _ _ (latitude_unit s p) (parallel_orthogonal s p)
    (parallel_orthogonal s p),parallel_square,scale_latitude]
  have hc : 0 ≤ cos s := cos_nonneg_of_mem_Icc ⟨by linarith [hs.1,pi_pos],hs.2⟩
  rw [← mul_pow,sqrt_sq_eq_abs,abs_of_nonneg (mul_nonneg (meridianSpeed_nonneg s hs) hc)]
  rfl

theorem primitive_derivative (s : ℝ) :
    HasDerivAt (fun a => -arctan (cos a)) (meridianSpeed s) s := by
  have h := ((Real.hasDerivAt_arctan (cos s)).comp s (Real.hasDerivAt_cos s)).neg
  convert h using 1
  · funext a
    simp
  · simp [meridianSpeed]
    ring

theorem meridian_length (s : ℝ) :
    (∫ a in (0:ℝ)..s, meridianSpeed a) = π/4-arctan (cos s) := by
  have hc : Continuous meridianSpeed := by
    unfold meridianSpeed
    exact continuous_sin.div (by fun_prop) (fun x => by positivity)
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => primitive_derivative x) (hc.intervalIntegrable _ _)]
  simp [Real.arctan_one]
  ring

theorem full_meridian_length :
    (∫ a in (0:ℝ)..(π/2), meridianSpeed a) = π/4 := by
  rw [meridian_length,cos_pi_div_two,arctan_zero,sub_zero]

theorem parallel_length (s : ℝ) :
    (∫ p in (0:ℝ)..(2*π), parallelSpeed s) = 2*π*parallelSpeed s := by
  simp [intervalIntegral.integral_const,smul_eq_mul]

theorem meridian_length_tendsto_zero :
    Filter.Tendsto (fun s : ℝ => ∫ a in (0:ℝ)..s, meridianSpeed a)
      (nhds 0) (nhds 0) := by
  simp_rw [meridian_length]
  have hc : Continuous (fun s : ℝ => π/4-arctan (cos s)) := by fun_prop
  simpa [Real.arctan_one] using hc.continuousAt (x:=0).tendsto

theorem parallel_length_tendsto_zero :
    Filter.Tendsto (fun s : ℝ => ∫ p in (0:ℝ)..(2*π), parallelSpeed s)
      (nhds 0) (nhds 0) := by
  simp_rw [parallel_length]
  have hc : Continuous meridianSpeed := by
    unfold meridianSpeed
    exact continuous_sin.div (by fun_prop) (fun x => by positivity)
  have h : Continuous (fun s : ℝ => 2*π*(meridianSpeed s*cos s)) := by fun_prop
  simpa [parallelSpeed,meridianSpeed] using h.continuousAt (x:=0).tendsto

#print axioms latitude_unit
#print axioms meridian_unit
#print axioms parallel_square
#print axioms meridian_orthogonal
#print axioms parallel_orthogonal
#print axioms latitude_derivative
#print axioms longitude_derivative
#print axioms scale_latitude
#print axioms meridianSpeed_nonneg
#print axioms meridian_metric_speed
#print axioms parallel_metric_speed
#print axioms primitive_derivative
#print axioms meridian_length
#print axioms full_meridian_length
#print axioms parallel_length
#print axioms meridian_length_tendsto_zero
#print axioms parallel_length_tendsto_zero
end Manuscript17.CassiniMeridian
