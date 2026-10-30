import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

noncomputable section
open Filter
open scoped Topology
namespace EulerianGrothendieck

def criticalQuotient (h : ℝ) : ℝ :=
  Real.sqrt (((1/6 : ℝ) + h) / ((1/12 : ℝ) + h)^2)

theorem criticalQuotient_zero : criticalQuotient 0 = Real.sqrt 24 := by
  norm_num [criticalQuotient]

theorem criticalQuotient_continuous : ContinuousAt criticalQuotient 0 := by
  unfold criticalQuotient
  fun_prop (disch := norm_num)

theorem criticalQuotient_limit :
    Tendsto criticalQuotient (𝓝 (0 : ℝ)) (𝓝 (Real.sqrt 24)) := by
  simpa only [criticalQuotient_zero] using criticalQuotient_continuous.tendsto

theorem critical_radicand_identity (h : ℝ) (hh : (1/12 : ℝ)+h ≠ 0) :
    1 - 1 / (144 * ((1/12 : ℝ)+h)^2) =
      h * (((1/6 : ℝ)+h) / ((1/12 : ℝ)+h)^2) := by
  have hlin : (1 : ℝ) + 12*h ≠ 0 := by
    intro hz
    apply hh
    linarith
  field_simp [hh, hlin]
  <;> ring

theorem critical_coefficient_identity :
    Real.sqrt 24 / (2 * (Real.pi^2+1)) = Real.sqrt 6 / (Real.pi^2+1) := by
  have h : Real.sqrt 24 = 2 * Real.sqrt 6 := by
    have := Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num) (6 : ℝ)
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      convert Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num) using 1 <;> norm_num
    simpa only [show (4 : ℝ) * 6 = 24 by norm_num, h4] using this
  rw [h]
  field_simp
  <;> ring

def criticalVacuum (h : ℝ) : ℝ :=
  Real.sqrt (1 - 1 / (144 * ((1/12 : ℝ)+h)^2))

theorem critical_vacuum_ratio (h : ℝ) (hh : 0 < h) :
    criticalVacuum h / Real.sqrt h = criticalQuotient h := by
  unfold criticalVacuum criticalQuotient
  rw [critical_radicand_identity h (by linarith), Real.sqrt_mul hh.le]
  have hn : Real.sqrt h ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hh)
  field_simp

theorem critical_vacuum_ratio_limit :
    Tendsto (fun h => criticalVacuum h / Real.sqrt h)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (Real.sqrt 24)) := by
  have ht := criticalQuotient_limit.mono_left (show nhdsWithin 0 (Set.Ioi 0) ≤ 𝓝 0 from inf_le_left)
  apply Filter.Tendsto.congr' ?_ ht
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (critical_vacuum_ratio h hh).symm
end EulerianGrothendieck

