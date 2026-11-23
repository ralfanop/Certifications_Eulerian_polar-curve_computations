import UniformLanczos.Rate514ConcreteResidual
import Mathlib

/-!
# M12 Theorem 5.14: the actual averaged Frechet-Jacobi kernel

The manuscript defines B̄_{km} = ∫₀¹ [Df(J(u(τ)))[E_m]]_{k,k-1} dτ,
where u(τ) = (1-τ) hybridBond + τ actualBond.

The classical published finite-compression Daleckii–Krein/Duhamel theory
provides pointwise symmetry, positive-semidefiniteness and polynomial
off-diagonal decay of the *instantaneous* kernel K(τ,k,m), uniformly
for τ∈[0,1]. Here we prove the previously unformalized original
operator step: averaging the actual K along this segment preserves
all three properties, and interchanges the finite window sum and integral.

The only external hypotheses in the key theorem are the cited classical
instantaneous-kernel properties and τ-continuity. In particular,
positivity/decay/symmetry of B̄ are CONCLUSIONS, not premises.
No unknown 'operator certificate' or convergence rate is postulated.
-/

namespace UniformLanczos.Rate514AveragedKernel

open Set MeasureTheory intervalIntegral Finset

/-- The exact averaged (Frechet) kernel on the actual path in §5.8. -/
noncomputable def averageKernel (K : ℝ → ℤ → ℤ → ℝ) (k m : ℤ) : ℝ :=
  ∫ τ in (0 : ℝ)..1, K τ k m

/-- The classical kernel is symmetric on the path; averaging preserves this. -/
theorem averageKernel_symmetric (K : ℝ → ℤ → ℤ → ℝ)
    (hSym : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ k m : ℤ, K τ k m = K τ m k)
    (k m : ℤ) : averageKernel K k m = averageKernel K m k := by
  unfold averageKernel
  apply intervalIntegral.integral_congr
  intro τ hτ
  have hI : τ ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hτ
  exact hSym τ hI k m

/-- Integrable pointwise kernel times a fixed pair of coordinates. -/
private theorem term_integrable (K : ℝ → ℤ → ℤ → ℝ)
    (hCont : ∀ k m : ℤ, Continuous (fun τ : ℝ => K τ k m))
    (x : ℤ → ℝ) (k m : ℤ) :
    IntervalIntegrable (fun τ : ℝ => K τ k m * x k * x m)
      volume (0 : ℝ) 1 := by
  exact (((hCont k m).mul continuous_const).mul continuous_const).intervalIntegrable 0 1

/-- The quadratic form of B̄ equals the integral of the pointwise quadratic
form of K. This requires no assumption on the sign of the average. -/
theorem averageKernel_quadratic_integral (K : ℝ → ℤ → ℤ → ℝ)
    (hCont : ∀ k m : ℤ, Continuous (fun τ : ℝ => K τ k m))
    (W : Finset ℤ) (x : ℤ → ℝ) :
    (∑ k ∈ W, ∑ m ∈ W, averageKernel K k m * x k * x m) =
      ∫ τ in (0 : ℝ)..1,
        ∑ k ∈ W, ∑ m ∈ W, K τ k m * x k * x m := by
  have hterm (k m : ℤ) :
      IntervalIntegrable (fun τ : ℝ => K τ k m * x k * x m)
        volume (0 : ℝ) 1 := term_integrable K hCont x k m
  have hinner (k : ℤ) :
      IntervalIntegrable (fun τ : ℝ => ∑ m ∈ W, K τ k m * x k * x m)
        volume (0 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    apply continuous_finset_sum W
    intro m hm
    exact ((hCont k m).mul continuous_const).mul continuous_const
  rw [intervalIntegral.integral_finset_sum (fun k _ => hinner k)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [intervalIntegral.integral_finset_sum (fun m _ => hterm k m)]
  apply Finset.sum_congr rfl
  intro m hm
  unfold averageKernel
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]

/-- **Actual operator step:** each instantaneous K(τ) is PSD by the
published Daleckii–Krein formula; hence its literal average is PSD. -/
theorem averageKernel_psd (K : ℝ → ℤ → ℤ → ℝ)
    (hCont : ∀ k m : ℤ, Continuous (fun τ : ℝ => K τ k m))
    (hPSD : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ (W : Finset ℤ) (x : ℤ → ℝ),
      0 ≤ ∑ k ∈ W, ∑ m ∈ W, K τ k m * x k * x m)
    (W : Finset ℤ) (x : ℤ → ℝ) :
    0 ≤ ∑ k ∈ W, ∑ m ∈ W, averageKernel K k m * x k * x m := by
  rw [averageKernel_quadratic_integral K hCont W x]
  apply intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  intro τ hτ
  exact hPSD τ hτ W x

/-- Polynomial off-diagonal decay passes to the averaged kernel without
loss of exponent or the coefficient C_f. -/
theorem averageKernel_decay (K : ℝ → ℤ → ℤ → ℝ) {Cf : ℝ}
    (hDecay : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ k m : ℤ,
      |K τ k m| ≤ Cf * ((1 + |(k : ℝ) - (m : ℝ)|) ^ 5)⁻¹)
    (k m : ℤ) :
    |averageKernel K k m| ≤ Cf * ((1 + |(k : ℝ) - (m : ℝ)|) ^ 5)⁻¹ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun τ => K τ k m)
    (C := Cf * ((1 + |(k : ℝ) - (m : ℝ)|) ^ 5)⁻¹)
    (fun τ hτ => by
      rw [Real.norm_eq_abs]
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
      exact hDecay τ ⟨hτ.1.le, hτ.2⟩ k m)
  rw [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at h
  exact h

/-- All matrix hypotheses of the existing energy theorem are now
satisfied by the **averaged** operator, assuming only its classical
instantaneous-kernel properties (not the averaged properties). -/
theorem averageKernel_matrix_certificate
    (K : ℝ → ℤ → ℤ → ℝ) {Cf : ℝ} (hCf : 0 ≤ Cf)
    (hCont : ∀ k m : ℤ, Continuous (fun τ : ℝ => K τ k m))
    (hSym : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ k m, K τ k m = K τ m k)
    (hPSD : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ (W : Finset ℤ) (x : ℤ → ℝ),
      0 ≤ ∑ k ∈ W, ∑ m ∈ W, K τ k m * x k * x m)
    (hDecay : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ k m,
      |K τ k m| ≤ Cf * ((1 + |(k : ℝ) - (m : ℝ)|) ^ 5)⁻¹)
    (W : Finset ℤ) :
    (∀ k ∈ W, ∀ m ∈ W, averageKernel K k m = averageKernel K m k) ∧
    (∀ x : ℤ → ℝ, 0 ≤ ∑ k ∈ W, ∑ m ∈ W, averageKernel K k m * x k * x m) ∧
    (∀ k m : ℤ,
      |averageKernel K k m| ≤ Cf * ((1 + |(k : ℝ) - (m : ℝ)|) ^ 5)⁻¹) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk m hm
    exact averageKernel_symmetric K hSym k m
  · exact averageKernel_psd K hCont hPSD W
  · exact averageKernel_decay K hDecay

end UniformLanczos.Rate514AveragedKernel

#print axioms UniformLanczos.Rate514AveragedKernel.averageKernel_symmetric
#print axioms UniformLanczos.Rate514AveragedKernel.averageKernel_quadratic_integral
#print axioms UniformLanczos.Rate514AveragedKernel.averageKernel_psd
#print axioms UniformLanczos.Rate514AveragedKernel.averageKernel_decay
#print axioms UniformLanczos.Rate514AveragedKernel.averageKernel_matrix_certificate
