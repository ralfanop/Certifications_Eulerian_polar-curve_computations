import Bridge.Fock3b
import Bridge.Ladder5

/-!
# Proposition 3.2: the kernel integrals converge in the Hilbert-space norm

For `t ∈ ℝ` let `k_t = K_α(·, -it/α) = e^{it·} ∈ L²(μ_α)`. The map `t ↦ k_t` is continuous into
`L²(μ_α)`, hence Bochner integrable on compact intervals, and as elements of `L²(μ_α)`
`∫_{-1/2}^{1/2} k_t dt = r_E` and `∫_{1/2}^{3/2} k_t dt = G_E` (eqs. (21)–(22)).
-/

open MeasureTheory Complex Set Filter Topology intervalIntegral
open scoped ComplexConjugate

namespace EulerianBridge.Fock3

open EulerianGrothendieck.Fock EulerianBridge.Ladder

variable {α : ℝ}

abbrev Hα (α : ℝ) := ↥(Lp ℂ 2 (fockMeasure α))

theorem memLp_of_expBdd (hα : 0 < α) {f : ℂ → ℂ} (hf : ExpBdd f) : MemLp f 2 (fockMeasure α) := by
  obtain ⟨hc, C, K, hb⟩ := hf
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  rw [fockMeasure, integrable_withDensity_iff_integrable_smul (measurable_fockDensity_nnreal α)]
  refine ((integrable_exp_norm hα (2 * K)).const_mul (C ^ 2)).mono' ?_ (Eventually.of_forall (fun z => ?_))
  · exact ((continuous_real_toNNReal.comp (continuous_fockDensity α)).smul
      (hc.norm.pow 2)).aestronglyMeasurable
  · rw [NNReal.smul_def, Real.coe_toNNReal _ (fockDensity_nonneg hα.le z), smul_eq_mul,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (fockDensity_nonneg hα.le z) (sq_nonneg _)), mul_comm]
    have hsq : ‖f z‖ ^ 2 ≤ C ^ 2 * Real.exp (2 * K * ‖z‖) := by
      calc ‖f z‖ ^ 2 ≤ (C * Real.exp (K * ‖z‖)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hb z) 2
        _ = C ^ 2 * Real.exp (2 * K * ‖z‖) := by
            rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    calc ‖f z‖ ^ 2 * fockDensity α z ≤ C ^ 2 * Real.exp (2 * K * ‖z‖) * fockDensity α z :=
          mul_le_mul_of_nonneg_right hsq (fockDensity_nonneg hα.le z)
      _ = C ^ 2 * (Real.exp (2 * K * ‖z‖) * fockDensity α z) := by ring

/-- The coherent vector `k_t = e^{it·}`. -/
noncomputable def kvec (hα : 0 < α) (t : ℝ) : Hα α :=
  (memLp_of_expBdd hα (ExpBdd.cexp_lin (I * t))).toLp (fun z => cexp (I * t * z))

theorem kvec_coe (hα : 0 < α) (t : ℝ) : (kvec hα t : ℂ → ℂ) =ᵐ[fockMeasure α] fun z => cexp (I * t * z) :=
  (memLp_of_expBdd hα (ExpBdd.cexp_lin (I * t))).coeFn_toLp

theorem kvec_eq_kernel (hα : 0 < α) (t : ℝ) (z : ℂ) : cexp (I * t * z) = K α z (-(I * t / α)) :=
  (kernel_point α hα.ne' z t).symm

theorem inner_kvec (hα : 0 < α) (t t' : ℝ) :
    (inner ℂ (kvec hα t) (kvec hα t') : ℂ) = cexp ((t':ℂ) * t / α) := by
  rw [L2.inner_def]
  rw [MeasureTheory.integral_congr_ae (g := fun z => conj (cexp (I * t * z)) * cexp (I * t' * z)) (by
    filter_upwards [kvec_coe hα t, kvec_coe hα t'] with z h1 h2
    rw [h1, h2, RCLike.inner_apply]; ring)]
  rw [integral_fockMeasure hα.le, ← gaussian_pairing hα t' t]
  congr 1; funext z
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have : conj (I * (t:ℂ) * z) = -(I * conj z * t) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [this]
  ring_nf

theorem norm_sub_kvec_sq (hα : 0 < α) (t t' : ℝ) :
    ‖kvec hα t - kvec hα t'‖ ^ 2 = Real.exp (t ^ 2 / α) - 2 * Real.exp (t * t' / α) + Real.exp (t' ^ 2 / α) := by
  have h := @norm_sub_sq ℂ _ _ _ _ (kvec hα t) (kvec hα t')
  rw [h, ← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ, inner_kvec, inner_kvec, inner_kvec]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_div, ← Complex.ofReal_exp, RCLike.re_to_complex,
    Complex.ofReal_re]
  rw [show t * t / α = t ^ 2 / α by ring, show t' * t' / α = t' ^ 2 / α by ring,
    show t' * t / α = t * t' / α by ring]

theorem continuous_kvec (hα : 0 < α) : Continuous (kvec hα) := by
  rw [Metric.continuous_iff]
  intro t ε hε
  have hf : Continuous (fun t' : ℝ => Real.exp (t ^ 2 / α) - 2 * Real.exp (t * t' / α) + Real.exp (t' ^ 2 / α)) := by
    fun_prop
  have h0 : Real.exp (t ^ 2 / α) - 2 * Real.exp (t * t / α) + Real.exp (t ^ 2 / α) = 0 := by
    rw [show t * t / α = t ^ 2 / α by ring]; ring
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.mp hf t (ε ^ 2) (by positivity)
  refine ⟨δ, hδ, fun t' ht' => ?_⟩
  have := hδε t' ht'
  rw [Real.dist_eq, h0, sub_zero] at this
  rw [dist_eq_norm, norm_sub_rev]
  have hsq := norm_sub_kvec_sq hα t t'
  have hnn : 0 ≤ ‖kvec hα t - kvec hα t'‖ := norm_nonneg _
  have hlt : ‖kvec hα t - kvec hα t'‖ ^ 2 < ε ^ 2 := by
    rw [hsq]; exact lt_of_abs_lt this
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt

/-- `⟨∫_a^b k_t dt, g⟩ = ⟨F, g⟩` where `F(z) = ∫_a^b e^{itz} dt`, for all `g`; hence the Bochner
integral equals `F` in `L²(μ_α)`. -/
theorem bochner_kernel (hα : 0 < α) {a b : ℝ} (hab : a ≤ b) (F : ℂ → ℂ)
    (hF : ∀ z, F z = ∫ t in a..b, cexp (I * t * z)) (hFm : MemLp F 2 (fockMeasure α)) :
    ∫ t in a..b, kvec hα t = hFm.toLp F := by
  apply ext_inner_right ℂ
  intro g
  have hint : IntervalIntegrable (kvec hα) volume a b := (continuous_kvec hα).intervalIntegrable a b
  rw [intervalIntegral.integral_of_le hab, ← inner_conj_symm, ← integral_inner hint.1, ← integral_conj]
  simp_rw [inner_conj_symm]
  set μ := fockMeasure α
  haveI : IsFiniteMeasure μ := fockMeasure_isFinite α
  set c := max |a| |b|
  -- the dominating function `e^{c|z|} |g z|` is `μ`-integrable
  have hE : MemLp (fun z : ℂ => ((Real.exp (c * ‖z‖) : ℝ) : ℂ)) 2 μ := by
    refine memLp_of_expBdd hα ⟨by fun_prop, 1, c, fun z => ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
  have hdomz : Integrable (fun z => ((Real.exp (c * ‖z‖) : ℝ) : ℂ) * (g : ℂ → ℂ) z) μ :=
    hE.integrable_mul (Lp.memLp g)
  have hbt : ∀ t ∈ Ioc a b, ∀ z : ℂ, ‖cexp (I * t * z)‖ ≤ Real.exp (c * ‖z‖) := by
    intro t ht z
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (I * (t:ℂ) * z).re = -(t * z.im) := by simp [Complex.mul_re]
    rw [hre]
    have hct : |t| ≤ c := by
      rcases le_total 0 t with h | h
      · rw [abs_of_nonneg h]; exact (le_abs_self _ |>.trans' ht.2).trans (le_max_right _ _)
      · rw [abs_of_nonpos h]
        have : -t ≤ -a := by linarith [ht.1]
        exact this.trans ((neg_le_abs a).trans (le_max_left _ _))
    calc -(t * z.im) ≤ |t * z.im| := neg_le_abs _
      _ = |t| * |z.im| := abs_mul _ _
      _ ≤ c * ‖z‖ := mul_le_mul hct (Complex.abs_im_le_norm z) (abs_nonneg _) ((abs_nonneg _).trans hct)
  have hH : Integrable (Function.uncurry fun (t : ℝ) (z : ℂ) => conj (cexp (I * t * z)) * (g : ℂ → ℂ) z)
      ((volume.restrict (Ioc a b)).prod μ) := by
    have hdom := (integrable_const (1:ℝ) (μ := volume.restrict (Ioc a b))).mul_prod hdomz.norm
    refine hdom.mono' ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ (Lp.aestronglyMeasurable g).comp_snd
      exact (Continuous.aestronglyMeasurable (by fun_prop))
    · have hae : ∀ᵐ q ∂((volume.restrict (Ioc a b)).prod μ), q.1 ∈ Ioc a b :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
      filter_upwards [hae] with q hq
      show ‖conj (cexp (I * q.1 * q.2)) * (g : ℂ → ℂ) q.2‖ ≤ 1 * ‖((Real.exp (c * ‖q.2‖) : ℝ) : ℂ) * (g : ℂ → ℂ) q.2‖
      rw [norm_mul, Complex.norm_conj, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (hbt q.1 hq q.2) (norm_nonneg _)
  have hL : ∀ t, (inner ℂ (kvec hα t) g : ℂ) = ∫ z, conj (cexp (I * t * z)) * (g : ℂ → ℂ) z ∂μ := by
    intro t
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [kvec_coe hα t] with z hz
    rw [hz, RCLike.inner_apply]; ring
  simp_rw [hL]
  rw [integral_integral_swap hH]
  refine integral_congr_ae ?_
  filter_upwards [hFm.coeFn_toLp] with z hz
  rw [hz, RCLike.inner_apply, hF z, intervalIntegral.integral_of_le hab, ← integral_conj,
    MeasureTheory.integral_mul_const]
  ring

/-- Proposition 3.2: `∫_{-1/2}^{1/2} k_t dt = r_E` in `L²(μ_α)` (Bochner integral). -/
theorem bochner_rE (hα : 0 < α) : ∫ t in (-1/2:ℝ)..(1/2), kvec hα t = (memLp_rE hα).toLp rE :=
  bochner_kernel hα (by norm_num) rE (fun z => by unfold rE; rfl) (memLp_rE hα)

/-- Proposition 3.2: `∫_{1/2}^{3/2} k_t dt = G_E` in `L²(μ_α)` (Bochner integral). -/
theorem bochner_GE (hα : 0 < α) : ∫ t in (1/2:ℝ)..(3/2), kvec hα t = (memLp_GE hα).toLp GE :=
  bochner_kernel hα (by norm_num) GE (fun z => (GE_kernel α hα.ne' z).1) (memLp_GE hα)

end EulerianBridge.Fock3
