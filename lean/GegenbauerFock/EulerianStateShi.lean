import GegenbauerFock.GegenbauerIntrinsicEntireBochnerEvaluation
import GegenbauerFock.UltrasphericalGammaDensity
import GegenbauerFock.ShiSeries
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Manuscript 13, Proposition 6.6: the Eulerian state and the hyperbolic sine integral

For `λ = 1/2` the ultraspherical law is the uniform law `du/2` on `(-1,1)`
(`gammaDensity_half`, `integral_half`). Let `𝟏` be the constant unit vector of `H_{1/2}`. Then

* `C_one_eq_rE`: the entire representative of `C_{1/2,α} 𝟏` is the Eulerian profile
  `r_E(z) = 2 sin(z/2)/z` (`r_E(0) = 1`);
* `C_one_norm_sq_hasSum`: `‖C_{1/2,α} 𝟏‖² = ∑ₖ 1/(16^k α^{2k} (2k)! (2k+1)²)`;
* `C_one_norm_sq_eq_shi`: `‖C_{1/2,α} 𝟏‖² = 4α Shi(1/(4α))`.

The Hilbert–Schmidt identity `‖C_{1/2,α}‖²_HS = ₁F₁(1/2; 3/2; 1/(4α))` of the same proposition is
Theorem 6.4 at `λ = 1/2`, already certified (`C_intrinsicEntire_HS_energy_eq_kummer`).
-/

noncomputable section

open MeasureTheory Complex GegenbauerFock.GeneralUltrasphericalFock
open scoped NNReal ENNReal

namespace GegenbauerFock.EulerianState

theorem half_pos' : (0 : ℝ) < 1 / 2 := by norm_num

local notation "ν" => Ultraspherical.measure (1 / 2 : ℝ)

instance : IsProbabilityMeasure ν := Ultraspherical.probability (1 / 2) half_pos'

/-- At `λ = 1/2` the Gamma-normalized density is `1/2` on `(-1,1)`. -/
theorem gammaDensity_half (u : ℝ) :
    Ultraspherical.gammaDensity (1 / 2) u =
      Set.indicator (Set.Ioo (-1 : ℝ) 1) (fun _ => (1 / 2 : ℝ)) u := by
  unfold Ultraspherical.gammaDensity Ultraspherical.shape
  by_cases h : -1 < u ∧ u < 1
  · rw [if_pos h, Set.indicator_of_mem (show u ∈ Set.Ioo (-1 : ℝ) 1 from h)]
    have hG : Real.Gamma (1 / 2 + 1) = 1 / 2 * Real.sqrt Real.pi := by
      rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    have hpi : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.2 Real.pi_pos
    rw [hG, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.Gamma_one, sub_self, Real.rpow_zero]
    field_simp
  · rw [if_neg h, Set.indicator_of_notMem (show u ∉ Set.Ioo (-1 : ℝ) 1 from h)]

/-- Integrals against `ν_{1/2}` are half the Lebesgue integrals over `[-1,1]`. -/
theorem integral_half (g : ℝ → ℂ) :
    ∫ u, g u ∂ν = (1 / 2 : ℂ) * ∫ u in (-1 : ℝ)..1, g u := by
  rw [Ultraspherical.measure_eq_withDensity_gamma _ half_pos']
  have hfun : (fun u => ENNReal.ofReal (Ultraspherical.gammaDensity (1 / 2) u)) =
      fun u => ((Real.toNNReal (Ultraspherical.gammaDensity (1 / 2) u) : ℝ≥0) : ℝ≥0∞) := rfl
  have hmeas : Measurable fun u => Real.toNNReal (Ultraspherical.gammaDensity (1 / 2) u) := by
    have : (fun u => Real.toNNReal (Ultraspherical.gammaDensity (1 / 2) u)) =
        fun u => Real.toNNReal (Set.indicator (Set.Ioo (-1 : ℝ) 1) (fun _ => (1 / 2 : ℝ)) u) :=
      funext fun u => by rw [gammaDensity_half]
    rw [this]
    exact (measurable_const.indicator measurableSet_Ioo).real_toNNReal
  rw [hfun, integral_withDensity_eq_integral_smul hmeas]
  have hpt : (fun u => Real.toNNReal (Ultraspherical.gammaDensity (1 / 2) u) • g u) =
      Set.indicator (Set.Ioo (-1 : ℝ) 1) (fun u => (1 / 2 : ℂ) * g u) := by
    funext u
    rw [gammaDensity_half]
    by_cases hu : u ∈ Set.Ioo (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, NNReal.smul_def, Complex.real_smul]
      norm_num
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
      simp
  rw [hpt, integral_indicator measurableSet_Ioo, integral_const_mul,
    intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]

/-- The Eulerian profile `r_E(z) = sin(z/2)/(z/2)`, extended by `1` at `0`. -/
def rE (z : ℂ) : ℂ := if z = 0 then 1 else 2 * Complex.sin (z / 2) / z

/-- The constant unit vector of `H_{1/2}`. -/
def one : Lp ℂ 2 ν := Lp.const 2 ν (1 : ℂ)

/-- `C_{1/2,α} 𝟏 = r_E`, pointwise for the entire representative. -/
theorem C_one_eq_rE (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    GaussianArea.entireRepresentative alpha
      (C_intrinsicEntire (1 / 2) alpha half_pos' ha one) z = rE z := by
  rw [C_intrinsicEntire_pointwiseBochner]
  have hc : (one : ℝ → ℂ) =ᵐ[ν] fun _ => (1 : ℂ) := Lp.coeFn_const 2 ν (1 : ℂ)
  rw [integral_congr_ae (hc.mono fun u hu => by
      show (one : ℝ → ℂ) u * Complex.exp (I * z * (u : ℂ) / 2) =
        Complex.exp (I * z * (u : ℂ) / 2)
      rw [hu, one_mul]), integral_half]
  unfold rE
  by_cases hz : z = 0
  · subst hz; simp; norm_num
  · rw [if_neg hz]
    have hc0 : I * z / 2 ≠ 0 := by simp [hz, I_ne_zero]
    have h := integral_exp_mul_complex (a := (-1 : ℝ)) (b := 1) hc0
    have hfun : (fun u : ℝ => Complex.exp (I * z * (u : ℂ) / 2)) =
        fun u : ℝ => Complex.exp (I * z / 2 * (u : ℂ)) := by
      funext u; ring_nf
    rw [hfun, h, Complex.sin]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring_nf

/-- The `n`-th moment of `ν_{1/2}`: `∫ uⁿ dν = (1 - (-1)^{n+1}) / (2(n+1))`. -/
theorem moment_half (n : ℕ) :
    ∫ u, (u : ℂ) ^ n ∂ν = (((1 - (-1 : ℝ) ^ (n + 1)) / (2 * (n + 1)) : ℝ) : ℂ) := by
  rw [integral_half]
  have : ∫ u in (-1 : ℝ)..1, (u : ℂ) ^ n = ((∫ u in (-1 : ℝ)..1, u ^ n : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]; push_cast; rfl
  rw [this, integral_pow]
  push_cast
  field_simp
  ring

/-- The `n`-th Fock coordinate of `C 𝟏` is `complexWeight α n` times the `n`-th moment. -/
theorem C_one_coeff (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    C (1 / 2) alpha half_pos' ha one n =
      WeightedMoments.complexWeight alpha n * ∫ u, (u : ℂ) ^ n ∂ν := by
  rw [C_coefficient]
  simp only [WeightedMoments.coefficient, ContinuousLinearMap.smul_apply, innerSL_apply,
    smul_eq_mul]
  congr 1
  rw [MeasureTheory.L2.inner_def]
  have hm := (WeightedMoments.monomial_memLp ν (ae_abs_le_one (1 / 2)) n).coeFn_toLp
  have hc : (one : ℝ → ℂ) =ᵐ[ν] fun _ => (1 : ℂ) := Lp.coeFn_const 2 ν (1 : ℂ)
  refine integral_congr_ae ?_
  filter_upwards [hm, hc] with u h1 h2
  simp only [WeightedMoments.monomial] at h1 ⊢
  rw [h1, h2]
  simp [← Complex.ofReal_pow, Complex.conj_ofReal]

theorem C_one_coeff_norm_sq (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    ‖C (1 / 2) alpha half_pos' ha one n‖ ^ 2 =
      WeightedMoments.squareWeight alpha n * ((1 - (-1 : ℝ) ^ (n + 1)) / (2 * (n + 1))) ^ 2 := by
  rw [C_one_coeff, norm_mul, mul_pow, WeightedMoments.complexWeight_norm_sq alpha ha, moment_half,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The terms of the Eulerian state series. -/
def stateTerm (alpha : ℝ) (k : ℕ) : ℝ :=
  1 / (16 ^ k * alpha ^ (2 * k) * ((2 * k).factorial : ℝ) * (2 * k + 1) ^ 2)

/-- `‖C_{1/2,α} 𝟏‖² = ∑ₖ 1/(16^k α^{2k} (2k)! (2k+1)²)`. -/
theorem C_one_norm_sq_hasSum (alpha : ℝ) (ha : 0 < alpha) :
    HasSum (stateTerm alpha)
      (‖C_intrinsicEntire (1 / 2) alpha half_pos' ha one‖ ^ 2) := by
  rw [C_intrinsicEntire_norm]
  have h := lp.hasSum_norm (p := 2) (by norm_num) (C (1 / 2) alpha half_pos' ha one)
  have h2 : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
  simp only [h2, Real.rpow_natCast] at h
  simp only [C_one_coeff_norm_sq alpha ha] at h
  have hodd : ∀ n ∉ Set.range (fun k : ℕ => 2 * k),
      WeightedMoments.squareWeight alpha n * ((1 - (-1 : ℝ) ^ (n + 1)) / (2 * (n + 1))) ^ 2 = 0 := by
    intro n hn
    obtain ⟨k, rfl⟩ : Odd n := by
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ho
      · exact absurd ⟨k, show 2 * k = n by omega⟩ hn
      · exact ho
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]
    norm_num
  rw [← (mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0)).hasSum_iff hodd] at h
  convert h using 1
  funext k
  simp only [Function.comp, stateTerm, WeightedMoments.squareWeight]
  rw [show 2 * k + 1 = 2 * k + 1 from rfl, pow_succ, pow_mul]
  norm_num
  push_cast
  have hα : alpha ≠ 0 := ha.ne'
  rw [pow_mul, show (alpha⁻¹ * (1 / 4)) ^ 2 = (alpha ^ 2)⁻¹ * 16⁻¹ by field_simp; ring,
    mul_pow, inv_pow, inv_pow]
  field_simp

/-- The same series is `4α Shi(1/(4α))`. -/
theorem stateTerm_hasSum_shi (alpha : ℝ) (ha : 0 < alpha) :
    HasSum (stateTerm alpha) (4 * alpha * Shi.Shi (1 / (4 * alpha))) := by
  have h := (Shi.hasSum_shi (1 / (4 * alpha))).mul_left (4 * alpha)
  convert h using 1
  funext k
  simp only [stateTerm]
  rw [Nat.factorial_succ]
  push_cast
  have hα : alpha ≠ 0 := ha.ne'
  have hp : (1 / (4 * alpha)) ^ (2 * k + 1) =
      1 / (4 * alpha) * (((alpha ^ 2) ^ k)⁻¹ * (16 ^ k)⁻¹) := by
    rw [pow_succ, pow_mul, mul_comm]
    congr 1
    rw [show (1 / (4 * alpha)) ^ 2 = (alpha ^ 2)⁻¹ * 16⁻¹ by field_simp; ring,
      mul_pow, inv_pow, inv_pow]
  rw [hp]
  field_simp
  ring

/-- **Proposition 6.6** (13): `‖r_E‖²_α = ‖C_{1/2,α} 𝟏‖² = 4α Shi(1/(4α))`. -/
theorem C_one_norm_sq_eq_shi (alpha : ℝ) (ha : 0 < alpha) :
    ‖C_intrinsicEntire (1 / 2) alpha half_pos' ha one‖ ^ 2 =
      4 * alpha * Shi.Shi (1 / (4 * alpha)) :=
  (C_one_norm_sq_hasSum alpha ha).unique (stateTerm_hasSum_shi alpha ha)

theorem proposition_6_6 (alpha : ℝ) (ha : 0 < alpha) :
    (∀ z, GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire (1 / 2) alpha half_pos' ha one) z = rE z) ∧
      ‖one‖ = 1 ∧
      HasSum (stateTerm alpha) (‖C_intrinsicEntire (1 / 2) alpha half_pos' ha one‖ ^ 2) ∧
      ‖C_intrinsicEntire (1 / 2) alpha half_pos' ha one‖ ^ 2 =
        4 * alpha * Shi.Shi (1 / (4 * alpha)) := by
  refine ⟨C_one_eq_rE alpha ha, ?_, C_one_norm_sq_hasSum alpha ha, C_one_norm_sq_eq_shi alpha ha⟩
  have hP := Ultraspherical.probability (1 / 2 : ℝ) half_pos'
  rw [one_div] at hP
  simp [one, Lp.norm_const]

#print axioms GegenbauerFock.EulerianState.C_one_eq_rE
#print axioms GegenbauerFock.EulerianState.proposition_6_6

end GegenbauerFock.EulerianState
