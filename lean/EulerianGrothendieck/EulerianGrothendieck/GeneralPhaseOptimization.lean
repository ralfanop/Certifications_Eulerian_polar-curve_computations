import EulerianGrothendieck.GlobalInfimum
import EulerianGrothendieck.ExplicitProjector
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Task H: the global optimum for an arbitrary phase (Theorem 9.15)

For every real `ϑ` and `z = e^{iϑ}` (so that the last frame coordinate carries
`conj z = e^{-iϑ}`, as in Lemma 9.14), and every `0 < p ≤ 1/144`,

  `|4 - g(P(p,ϑ)) - λ(ϑ) p| ≤ 2000 p^{3/2}`,  `λ(ϑ) = min((2/3)cos²(ϑ/2), 2 sin²(ϑ/2))`.

The constant `2000` is uniform in `ϑ`, so in particular `4 - g = λ p + O_ϑ(p^{3/2})`.
The proof localises every sublevel point (no minimiser is preselected), reduces to the
limiting quadratic objective, and minimises that objective for every phase, on both branches
of the minimum and in the degenerate cases `sin(ϑ/2) = 0` or `cos(ϑ/2) = 0`. -/

noncomputable section
open Filter Topology
namespace EulerianGrothendieck
set_option maxHeartbeats 2000000

/-- `λ` in terms of the half-angle coordinates `C = cos(ϑ/2)`, `S = sin(ϑ/2)`. -/
def phaseLambda (C S : ℝ) : ℝ := min ((2/3) * C ^ 2) (2 * S ^ 2)

theorem limitingObjective_halfPhase_identity (C S u v : ℝ) (y : ℂ) (hCS : C^2+S^2=1) :
    limitingObjective (halfPhase C S) u v y =
      u^2 + 3*(v + 2*C*(C*y.re-S*y.im)/3)^2 + (2/3:ℝ)*C^2*(C*y.re-S*y.im)^2 +
        2*S^2*(S*y.re+C*y.im)^2 := by
  have h2 : ((halfPhase C S)*y).re = C*(C*y.re-S*y.im)-S*(S*y.re+C*y.im) := by
    simp only [halfPhase, pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  unfold limitingObjective
  rw [h2]
  linear_combination (-(y.re) * (2*v + y.re*(1 + C^2 + S^2))) * hCS

theorem limitingObjective_general_lower (C S u v : ℝ) (y : ℂ) (hCS : C^2+S^2=1) (hy : ‖y‖=1) :
    phaseLambda C S ≤ limitingObjective (halfPhase C S) u v y := by
  have hy2 : y.re^2+y.im^2=1 := by
    have h := Complex.sq_norm y
    rw [Complex.normSq_apply, hy] at h
    nlinarith
  have hc : (C*y.re-S*y.im)^2+(S*y.re+C*y.im)^2=1 := by
    calc _ = (C^2+S^2)*(y.re^2+y.im^2) := by ring
      _ = 1 := by rw [hCS, hy2]; norm_num
  have hlow := circle_quadratic_lower ((2/3)*C^2) (2*S^2) _ _ hc
  rw [limitingObjective_halfPhase_identity C S u v y hCS]
  unfold phaseLambda
  nlinarith [sq_nonneg u, sq_nonneg (v + 2*C*(C*y.re-S*y.im)/3)]

/-- Trial points on both branches of the minimum. -/
theorem limitingObjective_general_trial (C S : ℝ) (hCS : C^2+S^2=1) :
    ∃ v : ℝ, ∃ y : ℂ, |v| ≤ 4 ∧ ‖y‖ = 1 ∧
      limitingObjective (halfPhase C S) 0 v y = phaseLambda C S := by
  have hC : |C| ≤ 1 := abs_le.mpr ⟨by nlinarith [sq_nonneg S], by nlinarith [sq_nonneg S]⟩
  have hnorm : ∀ a b : ℝ, a^2+b^2 = 1 → ‖(a:ℂ)+(b:ℂ)*Complex.I‖ = 1 := by
    intro a b hab
    have hn : ‖(a:ℂ)+(b:ℂ)*Complex.I‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I, hab]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hn
  rcases le_total ((2/3)*C^2) (2*S^2) with h | h
  · -- first branch: `λ = (2/3) cos²`, trial point `y = C - S i`, `v = -2C/3`
    set y : ℂ := (C:ℂ) + ((-S:ℝ):ℂ)*Complex.I with hy
    have hre : y.re = C := by simp [hy]
    have him : y.im = -S := by simp [hy]
    have hX : C*y.re - S*y.im = 1 := by rw [hre, him]; linear_combination hCS
    have hY : S*y.re + C*y.im = 0 := by rw [hre, him]; ring
    refine ⟨-(2*C/3), y, ?_, hnorm C (-S) (by rw [neg_sq]; exact hCS), ?_⟩
    · rw [abs_neg, abs_div, abs_mul]
      norm_num
      linarith [abs_nonneg C]
    · rw [limitingObjective_halfPhase_identity C S _ _ _ hCS, hX, hY]
      unfold phaseLambda
      rw [min_eq_left h]
      ring
  · -- second branch: `λ = 2 sin²`, trial point `y = S + C i`, `v = 0`
    set y : ℂ := (S:ℂ) + (C:ℂ)*Complex.I with hy
    have hre : y.re = S := by simp [hy]
    have him : y.im = C := by simp [hy]
    have hX : C*y.re - S*y.im = 0 := by rw [hre, him]; ring
    have hY : S*y.re + C*y.im = 1 := by rw [hre, him]; linear_combination hCS
    refine ⟨0, y, by norm_num, hnorm S C (by rw [add_comm]; exact hCS), ?_⟩
    rw [limitingObjective_halfPhase_identity C S _ _ _ hCS, hX, hY]
    unfold phaseLambda
    rw [min_eq_right h]
    ring

theorem phaseLambda_le_two (C S : ℝ) (hCS : C^2+S^2=1) : phaseLambda C S ≤ 2 := by
  unfold phaseLambda
  exact (min_le_right _ _).trans (by nlinarith [sq_nonneg C])

theorem general_frameDistance_global_lower (C S : ℝ) (hCS : C^2+S^2=1) (e : ℝ) (a b : ℂ)
    (he : 0 < e) (he1 : e ≤ 1/12) :
    phaseLambda C S * e^2 - 2000*e^3 ≤ frameDistance e (halfPhase C S) a b := by
  have hz := halfPhase_unit C S hCS
  by_cases hlow : frameDistance e (halfPhase C S) a b ≤ 16*e^2
  · obtain ⟨u,v,y,hu,hv,hy,heq⟩ := frameDistance_sublevel_coordinates e (halfPhase C S) a b
      he he1 hz hlow
    have hr := coordinateDistance_uniform_remainder e (halfPhase C S) y u v he.le he1 hu hv hy hz
    have hl := mul_le_mul_of_nonneg_left (limitingObjective_general_lower C S u v y hCS hy)
      (sq_nonneg e)
    have hb := (abs_le.mp hr).1
    rw [heq]
    nlinarith
  · have hm := mul_le_mul_of_nonneg_right (phaseLambda_le_two C S hCS) (sq_nonneg e)
    nlinarith [pow_nonneg he.le 3]

theorem general_frameDistance_trial_upper (C S : ℝ) (hCS : C^2+S^2=1) (e : ℝ)
    (he : 0 ≤ e) (he1 : e ≤ 1/12) :
    ∃ a b : ℂ, frameDistance e (halfPhase C S) a b ≤ phaseLambda C S * e^2 + 2000*e^3 := by
  have hz := halfPhase_unit C S hCS
  obtain ⟨v, y, hv, hy, hl⟩ := limitingObjective_general_trial C S hCS
  have hr := coordinateDistance_uniform_remainder e (halfPhase C S) y 0 v he he1
    (by norm_num) hv hy hz
  have hv1 : 0 ≤ 1 + e*v := by
    have := (abs_le.mp hv).1; nlinarith
  have heq := frameDistance_coordinates e 0 v (halfPhase C S) y (by norm_num) hv1 hy hz
  refine ⟨((1+e*0:ℝ):ℂ)*y, ((1+e*v:ℝ):ℂ), ?_⟩
  rw [heq]
  rw [hl] at hr
  have hb := (abs_le.mp hr).2
  linarith

/-- The global infimum for an arbitrary phase, with a uniform cubic remainder. -/
theorem general_frameInfimum_remainder (C S : ℝ) (hCS : C^2+S^2=1) (e : ℝ)
    (he : 0 < e) (he1 : e ≤ 1/12) :
    |frameInfimum e (halfPhase C S) - phaseLambda C S * e^2| ≤ 2000*e^3 := by
  have hlow : phaseLambda C S * e^2 - 2000*e^3 ≤ frameInfimum e (halfPhase C S) := by
    apply le_csInf (Set.range_nonempty _)
    rintro d ⟨⟨a,b⟩,rfl⟩
    exact general_frameDistance_global_lower C S hCS e a b he he1
  obtain ⟨a, b, hab⟩ := general_frameDistance_trial_upper C S hCS e he.le he1
  have hup : frameInfimum e (halfPhase C S) ≤ phaseLambda C S * e^2 + 2000*e^3 :=
    (csInf_le (frameDistance_range_bddBelow e _) ⟨(a,b), rfl⟩).trans hab
  rw [abs_le]; constructor <;> linarith

theorem exp_I_eq_halfPhase (θ : ℝ) :
    Complex.exp (θ * Complex.I) = halfPhase (Real.cos (θ/2)) (Real.sin (θ/2)) := by
  unfold halfPhase
  rw [Complex.ofReal_cos, Complex.ofReal_sin]
  have h : Complex.cos ((θ/2 : ℝ) : ℂ) + Complex.sin ((θ/2 : ℝ) : ℂ) * Complex.I =
      Complex.exp (((θ/2 : ℝ) : ℂ) * Complex.I) := (Complex.exp_mul_I _).symm
  rw [h, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `λ(ϑ) = min((2/3)cos²(ϑ/2), 2 sin²(ϑ/2))`. -/
def lambdaPhase (θ : ℝ) : ℝ := phaseLambda (Real.cos (θ/2)) (Real.sin (θ/2))

/-- **Theorem 9.15, arbitrary phase**: `|4 - g(P(p,ϑ)) - λ(ϑ) p| ≤ 2000 p^{3/2}` for
`0 < p ≤ 1/144`, uniformly in the real phase `ϑ`. -/
theorem general_phase_loss (θ : ℝ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1/144) :
    |(4 - explicitFrameScalarNorm (Real.sqrt p) (Complex.exp (θ * Complex.I))) -
      lambdaPhase θ * p| ≤ 2000 * p * Real.sqrt p := by
  have hCS : Real.cos (θ/2) ^ 2 + Real.sin (θ/2) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have he : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have he1 : Real.sqrt p ≤ 1/12 := by
    rw [show (1/12 : ℝ) = Real.sqrt (1/144) by
      rw [show (1/144:ℝ) = (1/12)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hp1
  have h := general_frameInfimum_remainder _ _ hCS (Real.sqrt p) he he1
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp.le
  have hcube : Real.sqrt p ^ 3 = p * Real.sqrt p := by rw [pow_succ, hsq]
  rw [hsq, hcube] at h
  have hid : 4 - explicitFrameScalarNorm (Real.sqrt p) (Complex.exp (θ * Complex.I)) =
      frameInfimum (Real.sqrt p) (halfPhase (Real.cos (θ/2)) (Real.sin (θ/2))) := by
    rw [exp_I_eq_halfPhase, explicitFrameScalarNorm_eq, frame_projection_distance_identity]
  rw [hid, lambdaPhase, mul_assoc]
  exact h

/-- First-order law for every fixed phase: `(4 - g(P(p,ϑ)))/p → λ(ϑ)` as `p ↓ 0`. -/
theorem general_phase_loss_limit (θ : ℝ) :
    Tendsto (fun p => (4 - explicitFrameScalarNorm (Real.sqrt p) (Complex.exp (θ * Complex.I))) / p)
      (𝓝[>] 0) (𝓝 (lambdaPhase θ)) := by
  have hs : Tendsto (fun p : ℝ => 2000 * Real.sqrt p) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun p : ℝ => Real.sqrt p) (𝓝[>] (0:ℝ)) (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
    rw [Real.sqrt_zero] at h1
    simpa using h1.const_mul 2000
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero_norm' _ hs
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0:ℝ) < 1/144 by norm_num)]
    with p hp hp2
  have hp0 : 0 < p := hp
  have h := general_phase_loss θ p hp0 hp2.2.le
  rw [norm_norm, Real.norm_eq_abs]
  rw [show (4 - explicitFrameScalarNorm (Real.sqrt p) (Complex.exp (θ * Complex.I))) / p -
      lambdaPhase θ =
      ((4 - explicitFrameScalarNorm (Real.sqrt p) (Complex.exp (θ * Complex.I))) -
        lambdaPhase θ * p) / p by
    field_simp]
  rw [abs_div, abs_of_pos hp0, div_le_iff₀ hp0]
  linarith

end EulerianGrothendieck
