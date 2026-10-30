import EulerianGrothendieck.GlobalInfimum
import EulerianGrothendieck.Critical

noncomputable section
namespace EulerianGrothendieck
open Filter
open scoped Topology
set_option maxHeartbeats 1000000

def eulerianLoss (p : ℝ) : ℝ := frameInfimum (Real.sqrt p) eulerianPhase

def eulerianVariationalRatio (p : ℝ) : ℝ := 4/(4-eulerianLoss p)

theorem eulerian_loss_ratio_limit :
    Tendsto (fun p => eulerianLoss p/p) (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (𝓝 (2/(Real.pi^2+1))) := by
  have hs : Tendsto Real.sqrt (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : ContinuousAt Real.sqrt (0:ℝ) := by fun_prop
      simpa using h.tendsto.mono_left (show nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ 𝓝 0 from inf_le_left)
    · filter_upwards [self_mem_nhdsWithin] with p hp
      exact Real.sqrt_pos.mpr hp
  have h := eulerian_frameInfimum_ratio_limit.comp hs
  apply Filter.Tendsto.congr' ?_ h
  filter_upwards [self_mem_nhdsWithin] with p hp
  simp only [Function.comp_apply, Real.sq_sqrt (le_of_lt hp), eulerianLoss]

theorem eulerian_loss_limit :
    Tendsto eulerianLoss (nhdsWithin (0:ℝ) (Set.Ioi 0)) (𝓝 0) := by
  have hi : Tendsto (fun p : ℝ => p) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have ht := eulerian_loss_ratio_limit.mul hi
  simp only [mul_zero] at ht
  apply Filter.Tendsto.congr' ?_ ht
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact div_mul_cancel₀ _ (ne_of_gt hp)

theorem eulerian_variational_ratio_limit :
    Tendsto (fun p => (eulerianVariationalRatio p-1)/p)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (𝓝 (1/(2*(Real.pi^2+1)))) := by
  have hd : Tendsto (fun p => 4-eulerianLoss p)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (𝓝 (4:ℝ)) := by
    simpa using (tendsto_const_nhds (x:=(4:ℝ))).sub eulerian_loss_limit
  have ht := eulerian_loss_ratio_limit.div hd (by norm_num)
  have heq : (2/(Real.pi^2+1))/4=1/(2*(Real.pi^2+1)) := by field_simp <;> ring
  rw [heq] at ht
  apply Filter.Tendsto.congr' ?_ ht
  filter_upwards [self_mem_nhdsWithin,
    eulerian_loss_limit.eventually (eventually_lt_nhds (show (0:ℝ)<4 by norm_num))] with p hp hq
  change (eulerianLoss p/p)/(4-eulerianLoss p) = (eulerianVariationalRatio p-1)/p
  unfold eulerianVariationalRatio
  have hn : 4-eulerianLoss p ≠ 0 := by linarith
  field_simp
  <;> ring

theorem criticalVacuum_pos (h : ℝ) (hh : 0<h) : 0 < criticalVacuum h := by
  unfold criticalVacuum
  apply Real.sqrt_pos.mpr
  rw [critical_radicand_identity h (by linarith)]
  positivity

theorem criticalVacuum_limit :
    Tendsto criticalVacuum (nhdsWithin (0:ℝ) (Set.Ioi 0)) (𝓝 0) := by
  have hc : ContinuousAt criticalVacuum 0 := by
    unfold criticalVacuum
    fun_prop (disch := norm_num)
  have h0 : criticalVacuum 0=0 := by norm_num [criticalVacuum]
  simpa only [h0] using hc.tendsto.mono_left
    (show nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ 𝓝 0 from inf_le_left)

/-- The critical law for the explicit global variational definition. The separate
projection-distance theorem is needed to identify this with the matrix scalar norm. -/
theorem eulerian_variational_critical_law :
    Tendsto (fun h => (eulerianVariationalRatio (criticalVacuum h)-1)/Real.sqrt h)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (𝓝 (Real.sqrt 6/(Real.pi^2+1))) := by
  have hv : Tendsto criticalVacuum (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨criticalVacuum_limit, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact criticalVacuum_pos h hh
  have ht := (eulerian_variational_ratio_limit.comp hv).mul critical_vacuum_ratio_limit
  have heq : (1/(2*(Real.pi^2+1)))*Real.sqrt 24 = Real.sqrt 6/(Real.pi^2+1) := by
    calc
      _ = Real.sqrt 24/(2*(Real.pi^2+1)) := by ring
      _ = _ := critical_coefficient_identity
  rw [heq] at ht
  apply Filter.Tendsto.congr' ?_ ht
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hn := (criticalVacuum_pos h hh).ne'
  simp only [Function.comp_apply]
  field_simp

end EulerianGrothendieck
