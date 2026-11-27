import Mathlib

noncomputable section
open MeasureTheory Set
namespace M12EffectiveResidual

/-- The orthonormal adjacent-polynomial cross moment is at most one,
with the actual weighted measure, not an independent cross-moment bound. -/
theorem crossMoment_le_one (μ : Measure ℝ) (p q : ℝ → ℝ)
    (hp : Integrable (fun x => p x ^ 2) μ)
    (hq : Integrable (fun x => q x ^ 2) μ)
    (hp1 : ∫ x, p x ^ 2 ∂μ = 1) (hq1 : ∫ x, q x ^ 2 ∂μ = 1)
    (hpq : AEStronglyMeasurable (fun x => |p x*q x|) μ) :
    Integrable (fun x => |p x*q x|) μ ∧
      (∫ x, |p x*q x| ∂μ) ≤ 1 := by
  have hbound : ∀ x, |p x*q x| ≤ (p x^2+q x^2)/2 := by
    intro x
    rw [abs_mul]
    nlinarith [sq_nonneg (|p x|-|q x|),sq_abs (p x),sq_abs (q x)]
  have hg : Integrable (fun x => (p x^2+q x^2)/2) μ :=
    (hp.add hq).div_const 2
  have hi : Integrable (fun x => |p x*q x|) μ :=
    hg.mono' hpq (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_abs]; exact hbound x)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x, (p x^2+q x^2)/2 ∂μ := integral_mono hi hg hbound
    _ = 1 := by rw [integral_div,integral_add hp hq,hp1,hq1]; norm_num

/-- Exponential tails absorb any prescribed inverse power, by the positive
power-series coefficient of the real exponential. -/
theorem exponential_tail_order (c M : ℝ) (hc : 0 < c) (hM : 0 < M) (N : ℕ) :
    Real.exp (-(c*M)) ≤ (Nat.factorial N : ℝ) / (c*M)^N := by
  have h : (c*M)^N / (Nat.factorial N : ℝ) ≤ Real.exp (c*M) :=
    Real.pow_div_factorial_le_exp (by positivity) N
  have hp : 0 < (c*M)^N := by positivity
  have hf : 0 < (Nat.factorial N : ℝ) := by exact_mod_cast Nat.factorial_pos N
  rw [Real.exp_neg,inv_eq_one_div,div_le_div_iff₀ (Real.exp_pos _) hp]
  exact (div_le_iff₀ hf).mp h |>.trans_eq (by ring)

theorem absorb_polynomial_tail (c M : ℝ) (hc : 0 < c) (hM : 1 ≤ M) (N : ℕ) :
    (M+1)^2 * Real.exp (-(c*M)) ≤
      4*(Nat.factorial (N+2):ℝ)/c^(N+2)/M^N := by
  have hMp : 0 < M := by linarith
  have htail := exponential_tail_order c M hc hMp (N+2)
  calc
    _ ≤ (2*M)^2 * ((Nat.factorial (N+2):ℝ)/(c*M)^(N+2)) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) 2) htail
        (Real.exp_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_pow,pow_add]
      field_simp
      ring

/-- Uniform residual assembly, with explicit constant for the two
endpoint tails. The input is the analytic inner/tail inequality from the
actual Freud integral, not the desired inverse-power conclusion. -/
theorem residual_order (c M A T C R : ℝ) (hc : 0 < c) (hM : 1 ≤ M)
    (hT : 0 ≤ T) (N : ℕ)
    (hR : |R| ≤ A/M^N + T*(M+1)^2*Real.exp (-(c*M)))
    (hC : C = A+T*(4*(Nat.factorial (N+2):ℝ)/c^(N+2))) :
    |R| ≤ C/M^N := by
  rw [hC]
  have h := absorb_polynomial_tail c M hc hM N
  calc
    |R| ≤ A/M^N + T*(M+1)^2*Real.exp (-(c*M)) := hR
    _ ≤ A/M^N + T*(4*(Nat.factorial (N+2):ℝ)/c^(N+2)/M^N) := by
      rw [mul_assoc T]
      exact add_le_add_left (mul_le_mul_of_nonneg_left h hT) _
    _ = _ := by ring

end M12EffectiveResidual

#print axioms M12EffectiveResidual.crossMoment_le_one
#print axioms M12EffectiveResidual.exponential_tail_order
#print axioms M12EffectiveResidual.absorb_polynomial_tail
#print axioms M12EffectiveResidual.residual_order
