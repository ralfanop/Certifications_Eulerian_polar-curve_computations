import GegenbauerFock.UltrasphericalDensityIntegration

/-!
# V007: affine Jacobian for the Beta-to-ultraspherical coordinate

This is the exact Lebesgue-measure scaling under u = 2x - 1.
It is a necessary ingredient for identifying the Radon--Nikodym
density of the actual pushed-forward Beta law. It is not itself
the complete transformed Beta/Gamma density theorem.
-/

open MeasureTheory

namespace GegenbauerFock.Ultraspherical

/-- The affine Beta-to-ultraspherical map carries Lebesgue measure
to exactly half of Lebesgue measure: the translation preserves
volume, while the dilation by two has Jacobian 1/2. -/
theorem map_volume_betaToInterval :
    Measure.map betaToInterval (volume : Measure ℝ) =
      ENNReal.ofReal (1 / 2 : ℝ) • (volume : Measure ℝ) := by
  have hmul : Measurable (fun x : ℝ => (2 : ℝ) * x) := by
    fun_prop
  have hadd : Measurable (fun y : ℝ => y + (-1 : ℝ)) := by
    fun_prop
  have hcomp :
      betaToInterval =
        (fun y : ℝ => y + (-1 : ℝ)) ∘
          (fun x : ℝ => (2 : ℝ) * x) := by
    funext x
    dsimp [betaToInterval, Function.comp_def]
    ring
  calc
    Measure.map betaToInterval (volume : Measure ℝ) =
        Measure.map (fun y : ℝ => y + (-1 : ℝ))
          (Measure.map (fun x : ℝ => (2 : ℝ) * x) volume) := by
            rw [hcomp, Measure.map_map hadd hmul]
    _ = Measure.map (fun y : ℝ => y + (-1 : ℝ))
          (ENNReal.ofReal (1 / 2 : ℝ) • volume) := by
            rw [Real.map_volume_mul_left (by norm_num : (2 : ℝ) ≠ 0)]
            norm_num
    _ = ENNReal.ofReal (1 / 2 : ℝ) •
          Measure.map (fun y : ℝ => y + (-1 : ℝ)) volume := by
            rw [Measure.map_smul _ hadd.aemeasurable]
    _ = ENNReal.ofReal (1 / 2 : ℝ) • volume := by
          rw [MeasureTheory.map_add_right_eq_self]

#print axioms GegenbauerFock.Ultraspherical.map_volume_betaToInterval

/-- The genuine symmetric Beta pushforward is absolutely continuous with
respect to Lebesgue measure. This is a measure-level result, obtained
from the certified affine Jacobian and the original Beta withDensity;
it does not yet identify the Radon--Nikodym derivative pointwise. -/
theorem measure_absolutelyContinuous_volume (lam : ℝ) :
    measure lam ≪ (volume : Measure ℝ) := by
  have hbeta :
      ProbabilityTheory.betaMeasure (shape lam) (shape lam) ≪
        (volume : Measure ℝ) := by
    unfold ProbabilityTheory.betaMeasure
    exact Measure.withDensity_absolutelyContinuous _ _
  have hmeas : Measurable betaToInterval := by
    unfold betaToInterval
    fun_prop
  have hmap := hbeta.map hmeas
  have hvol :
      Measure.map betaToInterval (volume : Measure ℝ) ≪
        (volume : Measure ℝ) := by
    rw [map_volume_betaToInterval]
    exact Measure.AbsolutelyContinuous.smul_left
      (Measure.AbsolutelyContinuous.rfl) _
  change (ProbabilityTheory.betaMeasure (shape lam) (shape lam)).map
      betaToInterval ≪ (volume : Measure ℝ)
  exact hmap.trans hvol

/-- The transported Beta law has no point masses, for every parameter. -/
theorem measure_singleton_eq_zero (lam u : ℝ) :
    measure lam {u} = 0 := by
  exact (measure_absolutelyContinuous_volume lam) (by simp)

/-- Exact Gamma-duplication normalization of the *affine* Beta density
on its open support, retaining the two Beta coordinate factors. -/
theorem affineDensity_eq_gamma_betaFactors
    (lam u : ℝ) (hlam : 0 < lam)
    (hu0 : -1 < u) (hu1 : u < 1) :
    affineDensity lam u =
      (Real.Gamma (lam + 1) /
        (2 * Real.Gamma (shape lam) *
          ((2 : ℝ) ^ (-2 * lam) * Real.sqrt Real.pi))) *
      (((u + 1) / 2) ^ (lam - 1 / 2) *
        ((1 - u) / 2) ^ (lam - 1 / 2)) := by
  have hshapeG : Real.Gamma (shape lam) ≠ 0 :=
    (Real.Gamma_pos_of_pos (shape_pos lam hlam)).ne'
  have hG : Real.Gamma (lam + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hpow : (2 : ℝ) ^ (-2 * lam) ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hpi : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.2 Real.pi_pos).ne'
  calc
    affineDensity lam u =
        ((1 / ProbabilityTheory.beta (shape lam) (shape lam)) / 2) *
          (((u + 1) / 2) ^ (lam - 1 / 2) *
            ((1 - u) / 2) ^ (lam - 1 / 2)) := by
              rw [affineDensity_eq_beta_weight lam u hu0 hu1]
              ring
    _ = _ := by
      rw [beta_shape_gamma_duplication lam hlam]
      field_simp
      <;> ring

#print axioms GegenbauerFock.Ultraspherical.measure_absolutelyContinuous_volume
#print axioms GegenbauerFock.Ultraspherical.measure_singleton_eq_zero
#print axioms GegenbauerFock.Ultraspherical.affineDensity_eq_gamma_betaFactors

end GegenbauerFock.Ultraspherical
