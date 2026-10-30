import EulerianGrothendieck.GaussianFockBridge
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # Task A, part 2: the vacuum vector and the vacuum probability

We work in `L²(μ_α)`, `μ_α = (α/π) e^{-α|z|²} dA(z)` (`fockMeasure α`), whose inner product
is the Fock inner product.  The vacuum is the constant function `1`.

Main results (namespace `EulerianGrothendieck.Fock`):
* `fockMeasure_univ`: `μ_α` is a probability measure, so `‖vacuum‖ = 1`;
* `inner_vacuum_fockState`: `⟪1, r_E^M⟫ = ∫ r_E^M dμ_α = 1`;
* `fockState_norm_sq`: `‖r_E^M‖² = E exp(S_M T_M/α)`;
* `fock_vacuum_probability`: for the normalised state `ψ = r_E^M/‖r_E^M‖`,
  the squared norm of the orthogonal projection onto the vacuum line equals
  `1/E exp(S_M T_M/α)`;
* `fock_vacuum_all_orders`: at `α = c M`, `c > 1/12`, this vacuum probability has the
  certified all-order expansion of `raw_uniform_vacuum_all_orders`. -/

noncomputable section
open scoped BigOperators ComplexConjugate NNReal ENNReal
open MeasureTheory ProbabilityTheory Finset Complex

namespace EulerianGrothendieck.Fock

/-- The Fock weight `dμ_α(z) = (α/π) e^{-α|z|²} dA(z)`. -/
def fockMeasure (α : ℝ) : Measure ℂ :=
  volume.withDensity (fun z => ((Real.toNNReal (fockDensity α z) : ℝ≥0) : ℝ≥0∞))

theorem measurable_fockDensity_nnreal (α : ℝ) :
    Measurable (fun z => Real.toNNReal (fockDensity α z)) :=
  (continuous_fockDensity α).measurable.real_toNNReal

theorem integral_fockMeasure {α : ℝ} (hα : 0 ≤ α) (g : ℂ → ℂ) :
    ∫ z, g z ∂fockMeasure α = ∫ z, (fockDensity α z : ℂ) * g z := by
  rw [fockMeasure, integral_withDensity_eq_integral_smul (measurable_fockDensity_nnreal α)]
  congr 1
  funext z
  rw [NNReal.smul_def, Real.coe_toNNReal _ (fockDensity_nonneg hα z), Complex.real_smul]

theorem integral_fockMeasure_real {α : ℝ} (hα : 0 ≤ α) (g : ℂ → ℝ) :
    ∫ z, g z ∂fockMeasure α = ∫ z, g z * fockDensity α z := by
  rw [fockMeasure, integral_withDensity_eq_integral_smul (measurable_fockDensity_nnreal α)]
  congr 1
  funext z
  rw [NNReal.smul_def, Real.coe_toNNReal _ (fockDensity_nonneg hα z), smul_eq_mul, mul_comm]

theorem integrable_fockDensity {α : ℝ} (hα : 0 < α) : Integrable (fockDensity α) := by
  simpa using integrable_exp_abs_im_mul_fockDensity hα 0

theorem integral_fockDensity {α : ℝ} (hα : 0 < α) : ∫ z, fockDensity α z = 1 := by
  have h := gaussian_pairing hα 0 0
  simp only [ofReal_zero, mul_zero, sub_zero, Complex.exp_zero, one_mul, zero_div] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

theorem fockMeasure_univ {α : ℝ} (hα : 0 < α) : fockMeasure α Set.univ = 1 := by
  rw [fockMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h := ofReal_integral_eq_lintegral_ofReal (integrable_fockDensity hα)
    (Filter.Eventually.of_forall (fockDensity_nonneg hα.le))
  have h2 : ∫⁻ z, ((Real.toNNReal (fockDensity α z) : ℝ≥0) : ℝ≥0∞) =
      ∫⁻ z, ENNReal.ofReal (fockDensity α z) := rfl
  rw [h2, ← h, integral_fockDensity hα, ENNReal.ofReal_one]

instance fockMeasure_isFinite (α : ℝ) : IsFiniteMeasure (fockMeasure α) := by
  rcases lt_or_ge 0 α with hα | hα
  · exact ⟨by rw [fockMeasure_univ hα]; exact ENNReal.one_lt_top⟩
  · have h0 : (fun z => ((Real.toNNReal (fockDensity α z) : ℝ≥0) : ℝ≥0∞)) = 0 := by
      funext z
      have : fockDensity α z ≤ 0 := by
        unfold fockDensity
        exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hα Real.pi_pos.le)
          (Real.exp_pos _).le
      simp [Real.toNNReal_of_nonpos this]
    have : fockMeasure α = 0 := by rw [fockMeasure, h0, withDensity_zero]
    rw [this]
    infer_instance

theorem fockMeasure_isProbability {α : ℝ} (hα : 0 < α) : IsProbabilityMeasure (fockMeasure α) :=
  ⟨fockMeasure_univ hα⟩

theorem continuous_rE : Continuous rE := by
  unfold rE
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun z (t : ℝ) => cexp (I * (t:ℂ) * z)) (by fun_prop) _ _

theorem norm_rE_pow_sq_le (z : ℂ) (M : ℕ) : ‖rE z ^ M‖ ^ 2 ≤ Real.exp (M * |z.im|) := by
  rw [norm_pow, ← pow_mul]
  calc ‖rE z‖ ^ (M * 2) ≤ Real.exp (|z.im| / 2) ^ (M * 2) :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_rE_le z) _
    _ = Real.exp (M * |z.im|) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- `r_E^M ∈ L²(μ_α)`. -/
theorem memLp_rE_pow {α : ℝ} (hα : 0 < α) (M : ℕ) :
    MemLp (fun z => rE z ^ M) 2 (fockMeasure α) := by
  have hc : Continuous (fun z => rE z ^ M) := continuous_rE.pow M
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  rw [fockMeasure, integrable_withDensity_iff_integrable_smul (measurable_fockDensity_nnreal α)]
  refine (integrable_exp_abs_im_mul_fockDensity hα M).mono' ?_ (Filter.Eventually.of_forall
    (fun z => ?_))
  · exact ((continuous_real_toNNReal.comp (continuous_fockDensity α)).smul
      (hc.norm.pow 2)).aestronglyMeasurable
  · rw [NNReal.smul_def, Real.coe_toNNReal _ (fockDensity_nonneg hα.le z), smul_eq_mul,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (fockDensity_nonneg hα.le z) (sq_nonneg _)),
      mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_rE_pow_sq_le z M) (fockDensity_nonneg hα.le z)

/-- The vacuum vector: the constant function `1` of `L²(μ_α)`. -/
def vacuum (α : ℝ) : Lp ℂ 2 (fockMeasure α) := (memLp_const (1:ℂ)).toLp (fun _ => (1:ℂ))

/-- The Fock state `r_E^M` as an element of `L²(μ_α)` (for `α ≤ 0` a junk value). -/
def fockState (α : ℝ) (M : ℕ) : Lp ℂ 2 (fockMeasure α) :=
  if hα : 0 < α then (memLp_rE_pow hα M).toLp (fun z => rE z ^ M) else 0

theorem fockState_coe {α : ℝ} (hα : 0 < α) (M : ℕ) :
    (fockState α M : ℂ → ℂ) =ᵐ[fockMeasure α] fun z => rE z ^ M := by
  rw [fockState, dif_pos hα]
  exact (memLp_rE_pow hα M).coeFn_toLp

theorem vacuum_coe (α : ℝ) : (vacuum α : ℂ → ℂ) =ᵐ[fockMeasure α] fun _ => (1:ℂ) :=
  (memLp_const (1:ℂ)).coeFn_toLp

theorem norm_vacuum {α : ℝ} (hα : 0 < α) : ‖vacuum α‖ = 1 := by
  haveI := fockMeasure_isProbability hα
  have h : inner ℂ (vacuum α) (vacuum α) = 1 := by
    rw [L2.inner_def]
    rw [integral_congr_ae (g := fun _ => (1:ℂ)) (by
      filter_upwards [vacuum_coe α] with z hz
      rw [hz]; simp)]
    simp
  have h2 : ‖vacuum α‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), h]
    exact Complex.one_re
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2

/-- `⟪1, r_E^M⟫_{μ_α} = 1`. -/
theorem inner_vacuum_fockState {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (M : ℕ) {α : ℝ} (hα : 0 < α) :
    inner ℂ (vacuum α) (fockState α M) = 1 := by
  rw [L2.inner_def]
  rw [integral_congr_ae (g := fun z => rE z ^ M) (by
    filter_upwards [vacuum_coe α, fockState_coe hα M] with z h1 h2
    rw [h1, h2]; simp)]
  rw [integral_fockMeasure hα.le]
  have hS : Measurable (fun ω => ∑ i ∈ range M, U i ω) :=
    Finset.measurable_fun_sum (range M) (fun i _ => hU i)
  have hB := EulerianGrothendieck.uniform_sum_ae_bound U hU hlaw M
  have hfub := gaussian_fubini (X := fun ω => ∑ i ∈ range M, U i ω) (Y := fun _ => (0:ℝ)) hS
    measurable_const ((M:ℝ)/2) hB (Filter.Eventually.of_forall (fun _ => by
      simp only [abs_zero]; positivity)) hα
  simp only [ofReal_zero, mul_zero, sub_zero, zero_div, Complex.exp_zero, integral_const,
    measureReal_univ_eq_one, one_smul] at hfub
  have hchar : ∀ z : ℂ, (∫ ω, cexp (I * z * ((∑ i ∈ range M, U i ω : ℝ) : ℂ)) ∂μ) = rE z ^ M :=
    fun z => sum_charFun U hU hind hlaw z M
  simp_rw [hchar] at hfub
  calc ∫ z, (fockDensity α z : ℂ) * rE z ^ M = ∫ z, rE z ^ M * (fockDensity α z : ℂ) := by
        congr 1; funext z; ring
    _ = 1 := hfub

/-- `‖r_E^M‖²_{μ_α} = E exp(S_M T_M/α)`. -/
theorem fockState_norm_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (M : ℕ) {α : ℝ} (hα : 0 < α) :
    ‖fockState α M‖ ^ 2 =
      ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / α) ∂μ.prod μ := by
  rw [← fock_norm_eq_probability_integral U hU hind hlaw M hα, norm_sq_eq_re_inner (𝕜 := ℂ),
    L2.inner_def]
  rw [integral_congr_ae (g := fun z => ((‖rE z ^ M‖ ^ 2 : ℝ) : ℂ)) (by
    filter_upwards [fockState_coe hα M] with z h
    rw [h, inner_self_eq_norm_sq_to_K]
    norm_cast)]
  rw [integral_complex_ofReal, integral_fockMeasure_real hα.le]
  exact Complex.ofReal_re _

/-- The normalised state `ψ = r_E^M/‖r_E^M‖`. -/
def normalizedFockState (α : ℝ) (M : ℕ) : Lp ℂ 2 (fockMeasure α) :=
  ((‖fockState α M‖ : ℂ)⁻¹) • fockState α M

/-- **Theorem 9.2, vacuum probability.**  The squared norm of the projection of the normalised
state onto the vacuum line is `1/N_{E,M}(α)`, `N_{E,M}(α) = E exp(S_M T_M/α)`. -/
theorem fock_vacuum_probability {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (M : ℕ) {α : ℝ} (hα : 0 < α) :
    ‖normalizedFockState α M‖ = 1 ∧
    ‖inner ℂ (vacuum α) (normalizedFockState α M)‖ ^ 2 =
      1 / ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / α) ∂μ.prod μ ∧
    ‖(ℂ ∙ vacuum α).starProjection (normalizedFockState α M)‖ ^ 2 =
      1 / ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / α) ∂μ.prod μ := by
  have h1 := inner_vacuum_fockState U hU hind hlaw M hα
  have hN := fockState_norm_sq U hU hind hlaw M hα
  have hne : fockState α M ≠ 0 := by
    intro h0; rw [h0, inner_zero_right] at h1; exact zero_ne_one h1
  have hpos : 0 < ‖fockState α M‖ := norm_pos_iff.mpr hne
  have hn0 : ((‖fockState α M‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hnorm : ‖normalizedFockState α M‖ = 1 := by
    rw [normalizedFockState, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
  have hinner : ‖inner ℂ (vacuum α) (normalizedFockState α M)‖ ^ 2 = 1 / ‖fockState α M‖ ^ 2 := by
    rw [normalizedFockState, inner_smul_right, h1, mul_one, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpos, inv_pow, one_div]
  refine ⟨hnorm, by rw [hinner, hN], ?_⟩
  rw [Submodule.starProjection_unit_singleton ℂ (norm_vacuum hα), norm_smul, norm_vacuum hα, mul_one,
    hinner, hN]

/-- The Fock vacuum probability `p_{E,M}(α) = ‖P_vac ψ‖²`, defined intrinsically in `L²(μ_α)`. -/
def fockVacuumProbability (α : ℝ) (M : ℕ) : ℝ :=
  ‖(ℂ ∙ vacuum α).starProjection (normalizedFockState α M)‖ ^ 2

/-- At the scale `α = c M` with `c > 1/12`, the intrinsic Fock vacuum probability satisfies the
certified all-order expansion (constant independent of `M`). -/
theorem fock_vacuum_all_orders {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (c : ℝ) (hc : 1/12 < c) (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 →
      |fockVacuumProbability (c * M) M -
        ∑ r ∈ range (R+1), uniformVacuumCoefficient (1/(12*c)) r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1) := by
  obtain ⟨K, hK, hrem⟩ := EulerianGrothendieck.raw_uniform_vacuum_all_orders U hU hind hlaw c hc R
  refine ⟨K, hK, fun M hM => ?_⟩
  have hMpos : (0:ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hα : 0 < c * M := mul_pos (by linarith) hMpos
  rw [fockVacuumProbability, (fock_vacuum_probability U hU hind hlaw M hα).2.2]
  exact hrem M hM

/-- Likewise for the Fock norm itself. -/
theorem fock_norm_all_orders {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (c : ℝ) (hc : 1/12 < c) (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 →
      |‖fockState (c * M) M‖ ^ 2 -
        ∑ r ∈ range (R+1), uniformNormCoefficient (1/(12*c)) r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1) := by
  obtain ⟨K, hK, hrem⟩ := EulerianGrothendieck.raw_uniform_kernel_all_orders U hU hind hlaw c hc R
  refine ⟨K, hK, fun M hM => ?_⟩
  have hMpos : (0:ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hα : 0 < c * M := mul_pos (by linarith) hMpos
  rw [fockState_norm_sq U hU hind hlaw M hα]
  exact hrem M hM

end EulerianGrothendieck.Fock
