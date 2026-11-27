import Bridge.Saddle.Corollary
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! M12 Lemma 5.15: arbitrary finite-order integrated Taylor estimate,
with a polynomial-Gaussian majorant on the rescaled inner region.
This lemma does not assume a Taylor remainder bound: it derives it
from the within-derivative estimate using Mathlib's Taylor theorem.
The remaining obligation is deriving all mixed derivative majorants
for the actual rescaled analytic phase. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Nat
namespace EulerianBridge.Saddle.AllOrder20261127

def gaussianMajorant (c : ℝ) (d : ℕ) (z : ℝ) : ℝ :=
  (1+z^(2*d))*Real.exp (-c*z^2)

theorem gaussianMajorant_nonneg (c : ℝ) (d : ℕ) (z : ℝ) :
    0 ≤ gaussianMajorant c d z := by
  unfold gaussianMajorant
  rw [pow_mul]
  positivity

theorem gaussianMajorant_integrable (c : ℝ) (hc : 0 < c) (d : ℕ) :
    Integrable (gaussianMajorant c d) := by
  have h₁ := integrable_exp_neg_mul_sq hc
  have h₂ : Integrable (fun z : ℝ => z^(2*d)*Real.exp (-c*z^2)) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq hc
      (show (-1:ℝ) < ((2*d:ℕ):ℝ) by positivity)
    simpa only [Real.rpow_natCast] using h
  have he : gaussianMajorant c d = fun z =>
      Real.exp (-c*z^2)+z^(2*d)*Real.exp (-c*z^2) := by
    funext z
    unfold gaussianMajorant
    ring
  rw [he]
  exact h₁.add h₂

/-- Pointwise Taylor remainder with a Gaussian envelope, for every n. -/
theorem pointwise_taylor (F : ℝ → ℝ → ℂ) (c ε C : ℝ) (d n : ℕ)
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (z : ℝ)
    (hDiff : ContDiffOn ℝ (n+1) (fun t => F t z) (Icc 0 ε))
    (hD : ∀ t ∈ Icc 0 ε,
      ‖iteratedDerivWithin (n+1) (fun t => F t z) (Icc 0 ε) t‖ ≤ C*gaussianMajorant c d z) :
    ‖F ε z - taylorWithinEval (fun t => F t z) n (Icc 0 ε) 0 ε‖ ≤
      (C*ε^(n+1)/(n.factorial:ℝ))*gaussianMajorant c d z := by
  have h := taylor_mean_remainder_bound hε hDiff ⟨hε,le_rfl⟩ hD
  rw [sub_zero] at h
  calc
    _ ≤ (C*gaussianMajorant c d z)*ε^(n+1)/(n.factorial:ℝ) := h
    _ = _ := by ring

/-- Uniform integrated error on an arbitrary measurable inner region S.
In particular S may depend on epsilon and grow like delta/epsilon.
The constant is independent of S and epsilon. -/
theorem integrated_taylor (F : ℝ → ℝ → ℂ) (c ε C : ℝ) (d n : ℕ)
    (hc : 0 < c) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hF : IntegrableOn (F ε) S)
    (hT : IntegrableOn (fun z =>
      taylorWithinEval (fun t => F t z) n (Icc 0 ε) 0 ε) S)
    (hDiff : ∀ z ∈ S, ContDiffOn ℝ (n+1) (fun t => F t z) (Icc 0 ε))
    (hD : ∀ z ∈ S, ∀ t ∈ Icc 0 ε,
      ‖iteratedDerivWithin (n+1) (fun t => F t z) (Icc 0 ε) t‖ ≤ C*gaussianMajorant c d z) :
    ‖(∫ z in S, F ε z) -
      ∫ z in S, taylorWithinEval (fun t => F t z) n (Icc 0 ε) 0 ε‖ ≤
      (C/(n.factorial:ℝ)*(∫ z, gaussianMajorant c d z))*ε^(n+1) := by
  let G : ℝ → ℝ := gaussianMajorant c d
  let T : ℝ → ℂ := fun z => taylorWithinEval (fun t => F t z) n (Icc 0 ε) 0 ε
  let A : ℝ := C*ε^(n+1)/(n.factorial:ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hG : Integrable G := gaussianMajorant_integrable c hc d
  have hR : IntegrableOn (fun z => F ε z-T z) S := hF.sub hT
  change ‖(∫ z in S, F ε z)-(∫ z in S,T z)‖ ≤ _
  rw [← integral_sub hF hT]
  calc
    _ ≤ ∫ z in S, ‖F ε z-T z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in S, A*G z := by
      apply setIntegral_mono_on hR.norm (hG.const_mul A).integrableOn hS
      intro z hz
      exact pointwise_taylor F c ε C d n hε hC z (hDiff z hz) (hD z hz)
    _ ≤ ∫ z, A*G z :=
      setIntegral_le_integral (hG.const_mul A)
        (Eventually.of_forall fun z => mul_nonneg hA (gaussianMajorant_nonneg c d z))
    _ = _ := by rw [integral_const_mul]; dsimp [A,G]; ring

/-- The reflection cancellation of every odd integrand in the symmetric
rescaled saddle region. -/
theorem odd_integral_zero (g : ℝ → ℂ) (r : ℝ)
    (hodd : ∀ z, g (-z) = -g z) :
    (∫ z in (-r)..r, g z) = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -r) (b := r) g
  rw [neg_neg] at h
  have he : (∫ z in (-r)..r, g (-z)) = -(∫ z in (-r)..r, g z) := by
    simp_rw [hodd,intervalIntegral.integral_neg]
  have hz : -(∫ z in (-r)..r, g z) = ∫ z in (-r)..r, g z := he.symm.trans h
  have hh : (2:ℂ)*(∫ z in (-r)..r, g z) = 0 := by linear_combination -hz
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

/-- The epsilon exponent in Lemma 5.15 is the stated integer power of
h when epsilon is the manuscript's exact epsM. -/
theorem eps_even_power (M N : ℕ) (hM : 1 ≤ M) :
    epsM M^(2*N) = ((M:ℝ)⁻¹)^N := by
  rw [pow_mul]
  have h := epsM_sq hM
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have h' : epsM M^2 = (M:ℝ)⁻¹ := by
    apply (mul_left_cancel₀ hm)
    rw [h,mul_inv_cancel₀ hm]
  rw [h']

end EulerianBridge.Saddle.AllOrder20261127
#print axioms EulerianBridge.Saddle.AllOrder20261127.gaussianMajorant_nonneg
#print axioms EulerianBridge.Saddle.AllOrder20261127.gaussianMajorant_integrable
#print axioms EulerianBridge.Saddle.AllOrder20261127.pointwise_taylor
#print axioms EulerianBridge.Saddle.AllOrder20261127.integrated_taylor
#print axioms EulerianBridge.Saddle.AllOrder20261127.odd_integral_zero
#print axioms EulerianBridge.Saddle.AllOrder20261127.eps_even_power
