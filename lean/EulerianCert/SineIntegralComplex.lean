/-
# Definition 2.1 of the V001 manuscript for complex argument

`Si(z) = ∫₀^z sin ζ / ζ dζ`, `z ∈ ℂ`, the integral taken along the segment `[0, z]`
(`ζ = t z`, `0 ≤ t ≤ 1`), with `sin ζ / ζ` extended by `1` at `ζ = 0`:
  `SiC z = ∫₀¹ z · sincC(t z) dt`, `sincC w = ∑ (−1)^k w^{2k}/(2k+1)!`.
Proved here:
* `sincC w = sin w / w` for `w ≠ 0`, `sincC 0 = 1`;
* Eq. (4), Maclaurin form: `SiC z = ∑ (−1)^k z^{2k+1}/((2k+1)·(2k+1)!)`, and the reciprocal central
  binomial form `∑ (−1)^k z^{2k+1}/((2k+1)² (k!)² C(2k,k))`;
* Eq. (4), hypergeometric form: `SiC z = z · ₁F₂(½; 3/2, 3/2; z₀² z²/2)` with `z₀ = i/√2`;
* `SiC` is entire (complex differentiable on `ℂ`), odd, and real on `ℝ`, where it equals the real
  `Si` of `FourierModes`.
-/
import EulerianCert.SineIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

open Nat intervalIntegral MeasureTheory

noncomputable section

namespace EulerianCert.SineIntegralComplex

open EulerianCert.FourierModes EulerianCert.SineIntegral

/-- The entire extension of `sin w / w`. -/
def sincC (w : ℂ) : ℂ := ∑' k : ℕ, (-1 : ℂ) ^ k * w ^ (2 * k) / ((2 * k + 1)! : ℂ)

lemma norm_term_le (w : ℂ) (k : ℕ) :
    ‖(-1 : ℂ) ^ k * w ^ (2 * k) / ((2 * k + 1)! : ℂ)‖ ≤ ‖w‖ ^ (2 * k) / ((2 * k)! : ℝ) := by
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
    Complex.norm_natCast]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact_mod_cast Nat.factorial_le (by omega)

lemma summable_even (r : ℝ) : Summable (fun k : ℕ => r ^ (2 * k) / ((2 * k)! : ℝ)) :=
  (Real.summable_pow_div_factorial r).comp_injective (fun a b hab => by simpa using hab)

lemma hasSum_sincC (w : ℂ) :
    HasSum (fun k : ℕ => (-1 : ℂ) ^ k * w ^ (2 * k) / ((2 * k + 1)! : ℂ)) (sincC w) :=
  (Summable.of_norm_bounded (summable_even ‖w‖) (norm_term_le w)).hasSum

lemma sincC_of_ne_zero {w : ℂ} (hw : w ≠ 0) : sincC w = Complex.sin w / w := by
  have h := (Complex.hasSum_sin w).div_const w
  refine (hasSum_sincC w).unique ?_
  convert h using 1
  ext k
  rw [pow_succ]
  field_simp

lemma sincC_zero : sincC 0 = 1 := by
  refine (hasSum_sincC 0).unique ?_
  convert hasSum_single (f := fun k : ℕ => (-1 : ℂ) ^ k * (0 : ℂ) ^ (2 * k) / ((2 * k + 1)! : ℂ))
    0 (fun k hk => by simp [zero_pow (by omega : 2 * k ≠ 0)]) using 1
  simp

/-- `Si(z) = ∫₀^z sin ζ/ζ dζ` along the segment `[0, z]`. -/
def SiC (z : ℂ) : ℂ := ∫ t in (0 : ℝ)..1, z * sincC ((t : ℂ) * z)

/-- **Eq. (4)**, Maclaurin series for complex `z`. -/
theorem hasSum_SiC (z : ℂ) :
    HasSum (fun k : ℕ => (-1 : ℂ) ^ k * z ^ (2 * k + 1) / ((2 * k + 1 : ℂ) * ((2 * k + 1)! : ℂ)))
      (SiC z) := by
  unfold SiC
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0)
    (b := 1)
    (F := fun k (t : ℝ) => z * ((-1 : ℂ) ^ k * ((t : ℂ) * z) ^ (2 * k) / ((2 * k + 1)! : ℂ)))
    (f := fun t : ℝ => z * sincC ((t : ℂ) * z))
    (fun k _ => ‖z‖ * (‖z‖ ^ (2 * k) / ((2 * k)! : ℝ)))
    (fun k => (by fun_prop : Continuous fun t : ℝ =>
      z * ((-1 : ℂ) ^ k * ((t : ℂ) * z) ^ (2 * k) / ((2 * k + 1)! : ℂ))).aestronglyMeasurable)
    (fun k => Filter.Eventually.of_forall (fun t ht => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
      refine (norm_term_le _ k).trans ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      exact mul_le_of_le_one_left (norm_nonneg z) ht.2))
    (Filter.Eventually.of_forall (fun _ _ => (summable_even ‖z‖).mul_left ‖z‖))
    (by apply Continuous.intervalIntegrable; exact continuous_const)
    (Filter.Eventually.of_forall (fun t _ => (hasSum_sincC _).mul_left z))
  convert key using 1
  ext k
  have e : (fun t : ℝ => z * ((-1 : ℂ) ^ k * ((t : ℂ) * z) ^ (2 * k) / ((2 * k + 1)! : ℂ))) =
      fun t : ℝ => (z * (-1 : ℂ) ^ k * z ^ (2 * k) / ((2 * k + 1)! : ℂ)) * ((t ^ (2 * k) : ℝ) : ℂ) := by
    ext t; push_cast; ring
  rw [e, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, integral_pow]
  push_cast
  field_simp
  ring

/-- **Eq. (4)**, reciprocal central binomial form for complex `z`. -/
theorem hasSum_SiC_binomial (z : ℂ) :
    HasSum (fun k : ℕ => (-1 : ℂ) ^ k * z ^ (2 * k + 1) /
      ((2 * k + 1 : ℂ) ^ 2 * ((k ! : ℂ)) ^ 2 * ((2 * k).choose k : ℂ))) (SiC z) := by
  convert hasSum_SiC z using 2 with k
  have h := odd_factorial_identity k
  have hC : ((2 * k + 1 : ℂ) ^ 2 * ((k ! : ℂ)) ^ 2 * ((2 * k).choose k : ℂ)) =
      (2 * k + 1 : ℂ) * ((2 * k + 1)! : ℂ) := by exact_mod_cast h.symm
  rw [hC]

/-- **Eq. (4)**, hypergeometric form: `SiC z = z · ₁F₂(½; 3/2, 3/2; z₀² z²/2)`, `z₀ = i/√2`. -/
theorem hasSum_SiC_hypergeometric (z : ℂ) :
    let z₀ : ℂ := Complex.I / (Real.sqrt 2 : ℂ)
    HasSum (fun k : ℕ => z * ((coef k : ℂ) * (z₀ ^ 2 * z ^ 2 / 2) ^ k)) (SiC z) := by
  intro z₀
  have hz0 : z₀ ^ 2 * z ^ 2 / 2 = -(z ^ 2) / 4 := by
    have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    simp only [z₀, div_pow, Complex.I_sq, hs]
    ring
  rw [show (fun k : ℕ => z * ((coef k : ℂ) * (z₀ ^ 2 * z ^ 2 / 2) ^ k)) =
      fun k : ℕ => z * ((coef k : ℂ) * (-(z ^ 2) / 4) ^ k) by rw [hz0]]
  convert hasSum_SiC z using 1
  ext k
  have h1 : coef k = 1 / (2 * k + 1) * (4 ^ k * (k ! : ℝ) / ((2 * k + 1)! : ℝ)) / (k ! : ℝ) := by
    rw [coef, ← poch_ratio k, poch_three_halves k]
    have : ((2 * k + 1)! : ℝ) ≠ 0 := by positivity
    have : ((k ! : ℝ)) ≠ 0 := by positivity
    field_simp
  rw [h1]
  push_cast
  rw [div_pow, neg_pow, ← pow_mul]
  have : ((2 * k + 1)! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have : ((k ! : ℂ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have : (2 * (k : ℂ) + 1) ≠ 0 := by exact_mod_cast (show 2 * k + 1 ≠ 0 by omega)
  field_simp
  ring

/-- `SiC` is odd. -/
theorem SiC_neg (z : ℂ) : SiC (-z) = -SiC z := by
  have h := (hasSum_SiC z).neg
  refine (hasSum_SiC (-z)).unique ?_
  convert h using 1
  ext k
  rw [Odd.neg_pow ⟨k, rfl⟩]
  ring

/-- `SiC` is real on `ℝ` and equals the real sine integral there. -/
theorem SiC_ofReal (x : ℝ) : SiC (x : ℂ) = (Si x : ℂ) := by
  refine (hasSum_SiC x).unique ?_
  have := Complex.hasSum_ofReal.mpr (hasSum_Si x)
  convert this using 1
  ext k
  push_cast
  ring

/-- **`SiC` is entire.** -/
theorem differentiable_SiC : Differentiable ℂ SiC := by
  have e : SiC = fun z => ∑' k : ℕ,
      (-1 : ℂ) ^ k * z ^ (2 * k + 1) / ((2 * k + 1 : ℂ) * ((2 * k + 1)! : ℂ)) := by
    ext z; exact (hasSum_SiC z).tsum_eq.symm
  rw [e]
  intro z0
  set r := ‖z0‖ + 1
  have hU : IsOpen (Metric.ball (0 : ℂ) r) := Metric.isOpen_ball
  have hmem : z0 ∈ Metric.ball (0 : ℂ) r := by simp [r]
  apply (DifferentiableOn.differentiableAt _ (hU.mem_nhds hmem))
  apply Complex.differentiableOn_tsum_of_summable_norm (u := fun k : ℕ => r * (r ^ (2 * k) /
    ((2 * k)! : ℝ))) ((summable_even r).mul_left r) (fun k => by fun_prop) hU
  intro k w hw
  rw [Metric.mem_ball, dist_zero_right] at hw
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul, norm_pow]
  have h1 : ‖w‖ ^ (2 * k + 1) ≤ r ^ (2 * k + 1) := pow_le_pow_left₀ (norm_nonneg _) hw.le _
  have h2 : ((2 * k)! : ℝ) ≤ ‖(2 * (k : ℂ) + 1)‖ * ‖((2 * k + 1)! : ℂ)‖ := by
    have : ‖(2 * (k : ℂ) + 1)‖ = 2 * k + 1 := by
      rw [show (2 * (k : ℂ) + 1) = ((2 * k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast; ring
    rw [this, Complex.norm_natCast]
    have : ((2 * k)! : ℝ) ≤ ((2 * k + 1)! : ℝ) := by exact_mod_cast Nat.factorial_le (by omega)
    nlinarith [(by positivity : (0 : ℝ) ≤ ((2 * k + 1)! : ℝ))]
  rw [pow_succ] at h1
  calc ‖w‖ ^ (2 * k + 1) / (‖(2 * (k : ℂ) + 1)‖ * ‖((2 * k + 1)! : ℂ)‖)
      ≤ r ^ (2 * k) * r / ((2 * k)! : ℝ) := by
        rw [pow_succ]
        apply div_le_div₀ (by positivity) (by rwa [← pow_succ, ← pow_succ]) (by positivity) h2
    _ = r * (r ^ (2 * k) / ((2 * k)! : ℝ)) := by ring

end EulerianCert.SineIntegralComplex
