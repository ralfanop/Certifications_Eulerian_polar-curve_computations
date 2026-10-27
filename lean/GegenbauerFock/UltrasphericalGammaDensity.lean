import GegenbauerFock.UltrasphericalMeasureDensity

/-!
# V007: classical Gamma-normalized ultraspherical density

Pointwise reduction of the certified Beta-pushforward density to the
classical single-power ultraspherical profile, including zero extension
outside the interval. No numerical or recurrence assumptions.
-/

open MeasureTheory

namespace GegenbauerFock.Ultraspherical

/-- Gamma-normalized ultraspherical density extended by zero. -/
noncomputable def gammaDensity (lam u : ℝ) : ℝ :=
  if -1 < u ∧ u < 1 then
    (Real.Gamma (lam + 1) /
      (Real.sqrt Real.pi * Real.Gamma (shape lam))) *
      (1 - u ^ 2) ^ (lam - 1 / 2)
  else 0

/-- On the open support, the affine Beta density reduces to the
Gamma-normalized (1-u²)^(λ-1/2) profile. -/
theorem affineDensity_eq_gamma_on_support
    (lam u : ℝ) (hlam : 0 < lam)
    (hu0 : -1 < u) (hu1 : u < 1) :
    affineDensity lam u =
      (Real.Gamma (lam + 1) /
        (Real.sqrt Real.pi * Real.Gamma (shape lam))) *
        (1 - u ^ 2) ^ (lam - 1 / 2) := by
  let a : ℝ := lam - 1 / 2
  have hp : 0 ≤ (u + 1) / 2 := by linarith
  have hq : 0 ≤ (1 - u) / 2 := by linarith
  have hw : 0 ≤ 1 - u ^ 2 := by
    have h : 0 ≤ (1 - u) * (1 + u) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hproduct :
      ((u + 1) / 2) ^ a * ((1 - u) / 2) ^ a =
        (1 - u ^ 2) ^ a / (4 : ℝ) ^ a := by
    rw [← Real.mul_rpow hp hq]
    have hbase : ((u + 1) / 2) * ((1 - u) / 2) =
        (1 - u ^ 2) / 4 := by ring
    rw [hbase, Real.div_rpow hw (by norm_num : (0 : ℝ) ≤ 4) a]
  have hfour : (4 : ℝ) ^ a = (2 : ℝ) ^ (2 * a) := by
    calc
      (4 : ℝ) ^ a = ((2 : ℝ) ^ (2 : ℝ)) ^ a := by norm_num
      _ = (2 : ℝ) ^ (2 * a) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) 2 a).symm
  have hscale :
      (2 : ℝ) ^ (-2 * lam) * (4 : ℝ) ^ a = 1 / 2 := by
    rw [hfour, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have he : -2 * lam + 2 * a = -1 := by
      dsimp [a]
      ring
    rw [he]
    norm_num
  have hden :
      (2 * Real.Gamma (shape lam) *
        ((2 : ℝ) ^ (-2 * lam) * Real.sqrt Real.pi)) *
          (4 : ℝ) ^ a =
      Real.Gamma (shape lam) * Real.sqrt Real.pi := by
    calc
      _ = (Real.Gamma (shape lam) * Real.sqrt Real.pi) *
            (2 * ((2 : ℝ) ^ (-2 * lam) * (4 : ℝ) ^ a)) := by ring
      _ = Real.Gamma (shape lam) * Real.sqrt Real.pi := by
        rw [hscale]
        ring
  calc
    affineDensity lam u =
        (Real.Gamma (lam + 1) /
          (2 * Real.Gamma (shape lam) *
            ((2 : ℝ) ^ (-2 * lam) * Real.sqrt Real.pi))) *
          (((u + 1) / 2) ^ a * ((1 - u) / 2) ^ a) := by
            simpa only [a] using
              affineDensity_eq_gamma_betaFactors lam u hlam hu0 hu1
    _ = (Real.Gamma (lam + 1) /
          (2 * Real.Gamma (shape lam) *
            ((2 : ℝ) ^ (-2 * lam) * Real.sqrt Real.pi))) *
          ((1 - u ^ 2) ^ a / (4 : ℝ) ^ a) := by
            rw [hproduct]
    _ = (Real.Gamma (lam + 1) /
          (Real.sqrt Real.pi * Real.Gamma (shape lam))) *
          (1 - u ^ 2) ^ a := by
            rw [div_mul_div_comm, hden]
            rw [div_mul_eq_mul_div]
            congr 1
            ring

/-- Equality of both densities at every real point (also endpoints). -/
theorem affineDensity_eq_gammaDensity
    (lam u : ℝ) (hlam : 0 < lam) :
    affineDensity lam u = gammaDensity lam u := by
  by_cases hu : -1 < u ∧ u < 1
  · simpa [gammaDensity, hu] using
      affineDensity_eq_gamma_on_support lam u hlam hu.1 hu.2
  · have hx :
        ¬ (0 < (u + 1) / 2 ∧ (u + 1) / 2 < 1) := by
      intro h
      apply hu
      constructor <;> linarith [h.1, h.2]
    have hpdf :
        ProbabilityTheory.betaPDFReal (shape lam) (shape lam)
          ((u + 1) / 2) = 0 := by
      simp [ProbabilityTheory.betaPDFReal, hx]
    simp [gammaDensity, hu, affineDensity, hpdf]

/-- Exact equality of the true ultraspherical probability measure with
the classical Gamma-normalized Lebesgue density. -/
theorem measure_eq_withDensity_gamma
    (lam : ℝ) (hlam : 0 < lam) :
    measure lam =
      (volume : Measure ℝ).withDensity
        (fun u => ENNReal.ofReal (gammaDensity lam u)) := by
  rw [measure_eq_withDensity_affine lam hlam]
  congr 1
  funext u
  rw [affineDensity_eq_gammaDensity lam u hlam]

#print axioms GegenbauerFock.Ultraspherical.affineDensity_eq_gamma_on_support
#print axioms GegenbauerFock.Ultraspherical.affineDensity_eq_gammaDensity
#print axioms GegenbauerFock.Ultraspherical.measure_eq_withDensity_gamma

end GegenbauerFock.Ultraspherical
