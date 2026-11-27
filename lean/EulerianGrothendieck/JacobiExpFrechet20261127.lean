import EulerianGrothendieck.JacobiDuhamel20261127
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Operator.Mul

/-! M12 Lemma 5.12: real Frechet derivative of the noncommutative
exponential on a Banach algebra, in operator norm, identified with
the actual Bochner integral of left and right multiplication.
The preceding Duhamel difference formula supplies the exact remainder.
No commutativity, finite-dimensionality or directional-only derivative. -/
noncomputable section
open MeasureTheory Set Filter NormedSpace Asymptotics
open scoped Topology
namespace M12ExpFrechet
section General
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

theorem exp_cont : Continuous (exp : R → R) := by
  apply continuous_iff_continuousAt.mpr
  intro A
  exact (analyticAt_exp_of_mem_ball (𝕂 := ℝ) A
    ((expSeries_radius_eq_top ℝ R).symm ▸ edist_lt_top _ _)).continuousAt

def kernel (A C : R) (s : ℝ) : R →L[ℝ] R :=
  ContinuousLinearMap.mulLeftRight ℝ R (exp ((1-s) • A)) (exp (s • C))

theorem kernel_apply (A C X : R) (s : ℝ) :
    kernel A C s X = M12Duhamel.density A C X s := rfl

theorem kernel_joint_cont (A : R) :
    Continuous (Function.uncurry (kernel A)) := by
  unfold Function.uncurry kernel
  have h₁ : Continuous (fun p : R × ℝ => exp ((1-p.2) • A)) :=
    exp_cont.comp ((continuous_const.sub continuous_snd).smul continuous_const)
  have h₂ : Continuous (fun p : R × ℝ => exp (p.2 • p.1)) :=
    exp_cont.comp (continuous_snd.smul continuous_fst)
  exact ((ContinuousLinearMap.mulLeftRight ℝ R).continuous.comp h₁).clm_apply h₂

set_option maxHeartbeats 2000000 in
theorem kernel_cont (A C : R) : Continuous (kernel A C) := by
  have hc : Continuous (fun s : ℝ => (C, s)) := continuous_const.prodMk continuous_id
  have h := (kernel_joint_cont A).comp hc
  change Continuous (fun s : ℝ => kernel A C s) at h
  exact h

def D (A C : R) : R →L[ℝ] R :=
  ∫ s in (0:ℝ)..1, kernel A C s

theorem D_cont (A : R) : Continuous (D A) := by
  unfold D
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (kernel_joint_cont A) 0 1

theorem D_apply (A C X : R) :
    D A C X = ∫ s in (0:ℝ)..1, M12Duhamel.density A C X s := by
  unfold D
  rw [ContinuousLinearMap.intervalIntegral_apply ((kernel_cont A C).intervalIntegrable 0 1)]
  rfl

theorem exp_difference (A C : R) :
    exp C-exp A = D A C (C-A) := by
  rw [D_apply]
  exact M12Duhamel.difference A C

theorem exp_remainder (A X : R) :
    exp (A+X)-exp A-D A A X = (D A (A+X)-D A A) X := by
  rw [exp_difference,add_sub_cancel_left]
  rfl

theorem exp_hasFDerivAt (A : R) :
    HasFDerivAt (exp : R → R) (D A A) A := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hcont : Continuous (fun X : R => ‖D A (A+X)-D A A‖) :=
    (((D_cont A).comp (continuous_const.add continuous_id)).sub continuous_const).norm
  have hn : {X : R | ‖D A (A+X)-D A A‖ < c} ∈ 𝓝 (0:R) := by
    apply (isOpen_lt hcont continuous_const).mem_nhds
    simpa using hc
  filter_upwards [hn] with X hX
  rw [exp_remainder]
  exact ((D A (A+X)-D A A).le_opNorm X).trans
    (mul_le_mul_of_nonneg_right (le_of_lt hX) (norm_nonneg X))

theorem exp_fderiv (A : R) : fderiv ℝ (exp : R → R) A = D A A :=
  (exp_hasFDerivAt A).fderiv

theorem exp_fderiv_apply (A X : R) :
    fderiv ℝ (exp : R → R) A X =
      ∫ s in (0:ℝ)..1, M12Duhamel.density A A X s := by
  rw [exp_fderiv,D_apply]

end General

open M12BilateralJacobi M12JacobiFrechet

theorem jacobi_exp_fderiv (u : Bonds) (m : ℤ) :
    fderiv ℝ (exp : Op → Op) (J u) (bond m) =
      ∫ s in (0:ℝ)..1, M12Duhamel.density (J u) (J u) (bond m) s :=
  exp_fderiv_apply (J u) (bond m)

theorem fourier_exp_fderiv (u : Bonds) (t : ℝ) (m : ℤ) :
    fderiv ℝ (exp : Op → Op) (((t:ℂ)*Complex.I) • J u)
      (((t:ℂ)*Complex.I) • bond m) =
      ∫ s in (0:ℝ)..1, M12Duhamel.density
        (((t:ℂ)*Complex.I) • J u) (((t:ℂ)*Complex.I) • J u)
        (((t:ℂ)*Complex.I) • bond m) s :=
  exp_fderiv_apply _ _

end M12ExpFrechet
#print axioms M12ExpFrechet.exp_cont
#print axioms M12ExpFrechet.kernel_apply
#print axioms M12ExpFrechet.kernel_joint_cont
#print axioms M12ExpFrechet.kernel_cont
#print axioms M12ExpFrechet.D_cont
#print axioms M12ExpFrechet.D_apply
#print axioms M12ExpFrechet.exp_difference
#print axioms M12ExpFrechet.exp_remainder
#print axioms M12ExpFrechet.exp_hasFDerivAt
#print axioms M12ExpFrechet.exp_fderiv
#print axioms M12ExpFrechet.exp_fderiv_apply
#print axioms M12ExpFrechet.jacobi_exp_fderiv
#print axioms M12ExpFrechet.fourier_exp_fderiv
