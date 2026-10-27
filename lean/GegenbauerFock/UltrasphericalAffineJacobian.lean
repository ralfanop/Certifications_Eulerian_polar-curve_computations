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

end GegenbauerFock.Ultraspherical
