import EulerianGrothendieck.RescaledObjective

noncomputable section
namespace EulerianGrothendieck
set_option maxHeartbeats 1500000

def halfPhase (C S : ℝ) : ℂ := ((C:ℂ)+(S:ℂ)*Complex.I)^2

theorem halfPhase_unit (C S : ℝ) (h : C^2+S^2=1) : ‖halfPhase C S‖=1 := by
  have hn := Complex.sq_norm ((C:ℂ)+(S:ℂ)*Complex.I)
  rw [Complex.normSq_apply] at hn
  norm_num at hn
  have hu : ‖(C:ℂ)+(S:ℂ)*Complex.I‖=1 := by nlinarith [norm_nonneg ((C:ℂ)+(S:ℂ)*Complex.I)]
  rw [halfPhase, norm_pow, hu, one_pow]

theorem limitingObjective_halfPhase_lower (C S u v : ℝ) (y : ℂ)
    (hCS : C^2+S^2=1) (hdom : 3*S^2 ≤ C^2) (hy : ‖y‖=1) :
    2*S^2 ≤ limitingObjective (halfPhase C S) u v y := by
  let X := C*y.re-S*y.im
  let Y := S*y.re+C*y.im
  have hy2 : y.re^2+y.im^2=1 := by
    have h := Complex.sq_norm y
    rw [Complex.normSq_apply, hy] at h
    nlinarith
  have hc : X^2+Y^2=1 := by
    dsimp [X,Y]
    calc
      _ = (C^2+S^2)*(y.re^2+y.im^2) := by ring
      _ = 1 := by rw [hCS, hy2]; norm_num
  have h1 : y.re = C*X+S*Y := by
    dsimp [X,Y]
    nlinarith [congrArg (fun t : ℝ => t*y.re) hCS]
  have h2 : ((halfPhase C S)*y).re = C*X-S*Y := by
    dsimp [halfPhase, X,Y]
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  have hid : limitingObjective (halfPhase C S) u v y =
      u^2+3*(v+2*C*X/3)^2+(2/3:ℝ)*C^2*X^2+2*S^2*Y^2 := by
    unfold limitingObjective
    rw [h2, h1]
    ring
  rw [hid]
  have hnon : 0 ≤ ((2/3:ℝ)*C^2-2*S^2)*X^2 := mul_nonneg (by nlinarith) (sq_nonneg X)
  have heq := congrArg (fun t : ℝ => 2*S^2*t) hc
  nlinarith [sq_nonneg u, sq_nonneg (v+2*C*X/3)]

theorem limitingObjective_halfPhase_trial (C S : ℝ) (hCS : C^2+S^2=1) :
    ‖(S:ℂ)+(C:ℂ)*Complex.I‖=1 ∧
    limitingObjective (halfPhase C S) 0 0 ((S:ℂ)+(C:ℂ)*Complex.I)=2*S^2 := by
  have hn := Complex.sq_norm ((S:ℂ)+(C:ℂ)*Complex.I)
  rw [Complex.normSq_apply] at hn
  norm_num at hn
  constructor
  · nlinarith [norm_nonneg ((S:ℂ)+(C:ℂ)*Complex.I)]
  · have h : ((halfPhase C S)*((S:ℂ)+(C:ℂ)*Complex.I)).re = -S := by
      dsimp [halfPhase]
      simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
        Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]
      nlinarith [congrArg (fun t : ℝ => S*t) hCS]
    simp only [limitingObjective, h, zero_pow (by decide : (2:ℕ)≠0), zero_add,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring

def eulerianHalfC : ℝ := Real.pi / Real.sqrt (Real.pi^2+1)
def eulerianHalfS : ℝ := 1 / Real.sqrt (Real.pi^2+1)
def eulerianPhase : ℂ := halfPhase eulerianHalfC eulerianHalfS

theorem eulerian_half_parameters :
    eulerianHalfC^2+eulerianHalfS^2=1 ∧
    3*eulerianHalfS^2 ≤ eulerianHalfC^2 ∧
    2*eulerianHalfS^2=2/(Real.pi^2+1) := by
  have hd : 0 < Real.pi^2+1 := by positivity
  have hs := Real.sq_sqrt hd.le
  have hn := (Real.sqrt_pos.mpr hd).ne'
  have hp := Real.pi_gt_three
  unfold eulerianHalfC eulerianHalfS
  rw [div_pow, div_pow, one_pow, hs]
  refine ⟨?_,?_,?_⟩
  · field_simp
  · rw [← mul_div_assoc, mul_one]
    apply (div_le_div_iff_of_pos_right hd).mpr
    nlinarith
  · ring

theorem eulerianPhase_unit : ‖eulerianPhase‖=1 :=
  halfPhase_unit _ _ eulerian_half_parameters.1

theorem eulerian_limitingObjective_lower (u v : ℝ) (y : ℂ) (hy : ‖y‖=1) :
    2/(Real.pi^2+1) ≤ limitingObjective eulerianPhase u v y := by
  rw [← eulerian_half_parameters.2.2]
  exact limitingObjective_halfPhase_lower _ _ u v y eulerian_half_parameters.1
    eulerian_half_parameters.2.1 hy

theorem eulerian_limitingObjective_trial :
    ‖(eulerianHalfS:ℂ)+(eulerianHalfC:ℂ)*Complex.I‖=1 ∧
    limitingObjective eulerianPhase 0 0 ((eulerianHalfS:ℂ)+(eulerianHalfC:ℂ)*Complex.I)=
      2/(Real.pi^2+1) := by
  simpa only [eulerian_half_parameters.2.2] using
    limitingObjective_halfPhase_trial _ _ eulerian_half_parameters.1

end EulerianGrothendieck
