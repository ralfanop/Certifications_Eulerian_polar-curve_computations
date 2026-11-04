import Mathlib
import SpecialImaginaryPoint.SonineBesselSummability

/-!
# Manuscript 14.1 §4 — exact regular value of the Sonine Bessel transforms

The actual Sonine averaging operator fixes the value of every
complex-valued function at z=0. The series-defined J0 and I0
both equal 1 at the origin. Combining these facts with the
unconditional z≠0 formula certifies the regular spherical
sinc and hyperbolic-sinc profiles at every complex point.
-/

namespace Manuscript14Sonine

/-- Evaluation at the origin is preserved by the actual integral. -/
theorem sonineAverageComplex_zero (f : ℂ → ℂ) :
    sonineAverageComplex f 0 = f 0 := by
  simp [sonineAverageComplex, intervalIntegral.integral_const] <;> ring

theorem modifiedBesselSeries_zero : modifiedBesselSeries 0 = 1 := by
  unfold modifiedBesselSeries evenEntireSeries
  rw [tsum_eq_single 0]
  · norm_num [modifiedBesselCoefficient]
  · intro n hn
    have hp : 0 < 2*n := by omega
    simp [zero_pow hp]

theorem ordinaryBesselSeries_zero : ordinaryBesselSeries 0 = 1 := by
  unfold ordinaryBesselSeries evenEntireSeries
  rw [tsum_eq_single 0]
  · norm_num [ordinaryBesselCoefficient, modifiedBesselCoefficient]
  · intro n hn
    have hp : 0 < 2*n := by omega
    simp [zero_pow hp]

noncomputable def complexSphericalSinc (z : ℂ) : ℂ :=
  if z = 0 then 1 else Complex.sin z / z

noncomputable def complexModifiedSphericalSinc (z : ℂ) : ℂ :=
  if z = 0 then 1 else Complex.sinh z / z

/-- Unconditional identity at every z∈ℂ, INCLUDING the regular origin. -/
theorem sonine_ordinaryBessel_spherical_global (z : ℂ) :
    sonineAverageComplex ordinaryBesselSeries z =
      complexSphericalSinc z := by
  by_cases hz : z = 0
  · subst z
    simp [complexSphericalSinc, sonineAverageComplex_zero,
      ordinaryBesselSeries_zero]
  · simp only [complexSphericalSinc, if_neg hz]
    exact sonine_ordinaryBessel_integral_eq_sin_div z hz

/-- Unconditional modified-spherical identity, regular at z=0. -/
theorem sonine_modifiedBessel_spherical_global (z : ℂ) :
    sonineAverageComplex modifiedBesselSeries z =
      complexModifiedSphericalSinc z := by
  by_cases hz : z = 0
  · subst z
    simp [complexModifiedSphericalSinc, sonineAverageComplex_zero,
      modifiedBesselSeries_zero]
  · simp only [complexModifiedSphericalSinc, if_neg hz]
    exact sonine_modifiedBessel_integral_eq_sinh_div z hz

#print axioms Manuscript14Sonine.sonineAverageComplex_zero
#print axioms Manuscript14Sonine.modifiedBesselSeries_zero
#print axioms Manuscript14Sonine.ordinaryBesselSeries_zero
#print axioms Manuscript14Sonine.sonine_ordinaryBessel_spherical_global
#print axioms Manuscript14Sonine.sonine_modifiedBessel_spherical_global

end Manuscript14Sonine
