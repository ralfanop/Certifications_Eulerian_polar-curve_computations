import EulerianGrothendieck.PhaseCoordinates
import EulerianGrothendieck.QuadraticMinimum
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.Field

noncomputable section
namespace EulerianGrothendieck
open Filter
open scoped Topology
set_option maxHeartbeats 1500000

def frameInfimum (e : ℝ) (z : ℂ) : ℝ :=
  sInf (Set.range (fun ab : ℂ × ℂ => frameDistance e z ab.1 ab.2))

theorem frameDistance_range_bddBelow (e : ℝ) (z : ℂ) :
    BddBelow (Set.range (fun ab : ℂ × ℂ => frameDistance e z ab.1 ab.2)) := by
  refine ⟨0, ?_⟩
  rintro d ⟨⟨a,b⟩,rfl⟩
  exact frameDistance_nonneg e z a b

theorem frameInfimum_nonneg (e : ℝ) (z : ℂ) : 0 ≤ frameInfimum e z := by
  apply le_csInf (Set.range_nonempty _)
  rintro d ⟨⟨a,b⟩,rfl⟩
  exact frameDistance_nonneg e z a b

theorem eulerian_frameDistance_global_lower (e : ℝ) (a b : ℂ)
    (he : 0 < e) (he1 : e ≤ 1/12) :
    (2/(Real.pi^2+1))*e^2-2000*e^3 ≤ frameDistance e eulerianPhase a b := by
  by_cases hlow : frameDistance e eulerianPhase a b ≤ 16*e^2
  · obtain ⟨u,v,y,hu,hv,hy,heq⟩ := frameDistance_sublevel_coordinates e eulerianPhase a b
      he he1 eulerianPhase_unit hlow
    have hr := coordinateDistance_uniform_remainder e eulerianPhase y u v he.le he1
      hu hv hy eulerianPhase_unit
    have hl := mul_le_mul_of_nonneg_left (eulerian_limitingObjective_lower u v y hy) (sq_nonneg e)
    have hb := (abs_le.mp hr).1
    rw [heq]
    nlinarith
  · have hlambda : 2/(Real.pi^2+1) ≤ 2 := by
      apply (div_le_iff₀ (by positivity : 0 < Real.pi^2+1)).mpr
      nlinarith [sq_nonneg Real.pi]
    have hm := mul_le_mul_of_nonneg_right hlambda (sq_nonneg e)
    nlinarith [pow_nonneg he.le 3]

theorem eulerian_frameDistance_trial_upper (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1/12) :
    frameDistance e eulerianPhase
      ((eulerianHalfS:ℂ)+(eulerianHalfC:ℂ)*Complex.I) 1 ≤
      (2/(Real.pi^2+1))*e^2+2000*e^3 := by
  obtain ⟨hy,hl⟩ := eulerian_limitingObjective_trial
  have hr := coordinateDistance_uniform_remainder e eulerianPhase
    ((eulerianHalfS:ℂ)+(eulerianHalfC:ℂ)*Complex.I) 0 0 he he1
    (by norm_num) (by norm_num) hy eulerianPhase_unit
  have heq := frameDistance_coordinates e 0 0 eulerianPhase
    ((eulerianHalfS:ℂ)+(eulerianHalfC:ℂ)*Complex.I) (by norm_num) (by norm_num)
    hy eulerianPhase_unit
  simp only [mul_zero, add_zero, Complex.ofReal_one, one_mul] at heq
  rw [heq]
  rw [hl] at hr
  have hb := (abs_le.mp hr).2
  nlinarith

/-- Uniform estimate for the actual global infimum over all complex pairs. -/
theorem eulerian_frameInfimum_remainder (e : ℝ) (he : 0 < e) (he1 : e ≤ 1/12) :
    |frameInfimum e eulerianPhase-(2/(Real.pi^2+1))*e^2| ≤ 2000*e^3 := by
  have hlow : (2/(Real.pi^2+1))*e^2-2000*e^3 ≤ frameInfimum e eulerianPhase := by
    apply le_csInf (Set.range_nonempty _)
    rintro d ⟨⟨a,b⟩,rfl⟩
    exact eulerian_frameDistance_global_lower e a b he he1
  have hupp : frameInfimum e eulerianPhase ≤ (2/(Real.pi^2+1))*e^2+2000*e^3 := by
    apply (csInf_le (frameDistance_range_bddBelow e eulerianPhase)
      (Set.mem_range.mpr ⟨(((eulerianHalfS:ℂ)+(eulerianHalfC:ℂ)*Complex.I),1),rfl⟩)).trans
    exact eulerian_frameDistance_trial_upper e he.le he1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem eulerian_frameInfimum_ratio_bound (e : ℝ) (he : 0 < e) (he1 : e ≤ 1/12) :
    |frameInfimum e eulerianPhase/e^2-2/(Real.pi^2+1)| ≤ 2000*e := by
  have h := eulerian_frameInfimum_remainder e he he1
  have heq : frameInfimum e eulerianPhase/e^2-2/(Real.pi^2+1) =
      (frameInfimum e eulerianPhase-(2/(Real.pi^2+1))*e^2)/e^2 := by
    field_simp
  rw [heq, abs_div, abs_of_pos (sq_pos_of_pos he)]
  apply (div_le_iff₀ (sq_pos_of_pos he)).mpr
  nlinarith

theorem eulerian_frameInfimum_ratio_limit :
    Tendsto (fun e => frameInfimum e eulerianPhase/e^2)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (𝓝 (2/(Real.pi^2+1))) := by
  have hi : Tendsto (fun e : ℝ => e) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hlo : Tendsto (fun e : ℝ => 2/(Real.pi^2+1)-2000*e)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (2/(Real.pi^2+1))) := by
    simpa using (tendsto_const_nhds (x:=2/(Real.pi^2+1))).sub ((tendsto_const_nhds (x:=(2000:ℝ))).mul hi)
  have hup : Tendsto (fun e : ℝ => 2/(Real.pi^2+1)+2000*e)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (2/(Real.pi^2+1))) := by
    simpa using (tendsto_const_nhds (x:=2/(Real.pi^2+1))).add ((tendsto_const_nhds (x:=(2000:ℝ))).mul hi)
  have hs : ∀ᶠ e : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < e ∧ e ≤ 1/12 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0:ℝ) < 1/12 by norm_num)).filter_mono inf_le_left] with e he hs
    exact ⟨he,hs.le⟩
  have hb : ∀ᶠ e : ℝ in nhdsWithin 0 (Set.Ioi 0),
      2/(Real.pi^2+1)-2000*e ≤ frameInfimum e eulerianPhase/e^2 ∧
      frameInfimum e eulerianPhase/e^2 ≤ 2/(Real.pi^2+1)+2000*e := by
    filter_upwards [hs] with e he
    have h := abs_le.mp (eulerian_frameInfimum_ratio_bound e he.1 he.2)
    constructor <;> linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using hlo) (by simpa using hup)
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)

end EulerianGrothendieck
