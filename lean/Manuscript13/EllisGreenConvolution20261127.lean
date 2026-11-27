import Mathlib
import Manuscript13.EllisGreenKernel20261127
open MeasureTheory Set Filter SchwartzMap FourierTransform
open ContinuousLinearMap
open scoped FourierTransform Convolution Topology ENNReal
namespace Manuscript13.EllisGreenConvolution20261127
noncomputable section
open Manuscript13.EllisComplexResolvent20261127
open Manuscript13.EllisGreenKernel20261127

theorem green_integrable (κ : ℝ) (hk : 0 < κ) : Integrable (green κ) := by
  have hp := positive_integrable κ 0 hk
  have hn := negative_integrable κ 0 hk
  have hu := hn.union hp
  rw [Iic_union_Ioi] at hu
  have h : integrand κ 0 = green κ := by
    funext t
    simp [integrand]
  rw [h] at hu
  simpa using hu

theorem green_bound (κ : ℝ) (hk : 0 < κ) (t : ℝ) :
    ‖green κ t‖ ≤ 1/(2*κ) := by
  rw [green, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg t])

theorem green_memLp (κ : ℝ) (hk : 0 < κ) : MemLp (green κ) 2 volume := by
  have hi := green_integrable κ hk
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).2
  apply (hi.norm.const_mul (1/(2*κ))).mono'
  · exact (hi.aestronglyMeasurable.norm.pow 2)
  · filter_upwards [] with x
    rw [Real.norm_of_nonneg (sq_nonneg _), pow_two]
    exact mul_le_mul_of_nonneg_right (green_bound κ hk x) (norm_nonneg _)

theorem green_fourier (κ : ℝ) (hk : 0 < κ) (ξ : ℝ) :
    𝓕 (green κ) ξ = multiplier κ ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← green_fourier_integral κ ξ hk]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold integrand
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

/-- Compatibility of the ordinary integral Fourier transform and the L² transform on
their common L¹∩L² domain, via the distribution embedding and Schwartz test functions. -/
theorem fourier_integral_agreement (f : H) (hf : Integrable (fun x : ℝ => f x)) :
    (fun x => fourier f x) =ᵐ[volume] (𝓕 (fun x : ℝ => f x)) := by
  have hc : Continuous (𝓕 (fun x : ℝ => f x)) := by
    first
    | exact hf.continuous_fourier
    | exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hf
    | exact?
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (fourier f)).locallyIntegrable (by norm_num)) hc.locallyIntegrable
  intro t ht hs
  have hs' : HasCompactSupport (Complex.ofRealCLM ∘ t) := hs.comp_left rfl
  have ht' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ t) := by fun_prop
  let φ := hs'.toSchwartzMap ht'
  have he := congrArg (fun z : TemperedDistribution ℝ ℂ => z φ)
    (Lp.fourier_toTemperedDistribution_eq f)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at he
  calc
    _ = ∫ x : ℝ, φ x • fourier f x := by rfl
    _ = ∫ x : ℝ, (𝓕 φ) x • f x := he.symm
    _ = ∫ x : ℝ, φ x • (𝓕 (fun y : ℝ => f y)) x := by
      rw [SchwartzMap.fourier_coe]
      first
      | exact VectorFourier.integral_fourierIntegral_smul_eq_flip
          Real.continuous_fourierChar (innerSL ℝ).continuous₂ φ.integrable hf
      | exact?
    _ = _ := by rfl

def conv (κ : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  green κ ⋆[ContinuousLinearMap.mul ℂ ℂ] f

theorem conv_integral (κ : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    conv κ f x = ∫ t : ℝ, green κ (x-t) * f t := convolution_mul_swap

theorem conv_row_mem (κ : ℝ) (hk : 0 < κ) (x : ℝ) :
    MemLp (fun t => green κ (x-t)) 2 volume := by
  exact (green_memLp κ hk).comp_measurePreserving (volume.measurePreserving_sub_left x)

def convRow (κ : ℝ) (hk : 0 < κ) (x : ℝ) : H :=
  (conv_row_mem κ hk x).toLp _

theorem conv_row_pair (κ : ℝ) (hk : 0 < κ) (x : ℝ) (f : H) :
    conv κ (fun t => f t) x = inner ℂ (convRow κ hk x) f := by
  rw [conv_integral,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(conv_row_mem κ hk x).coeFn_toLp] with t ht
  have hrow : convRow κ hk x t = green κ (x-t) := ht
  rw [hrow]
  simp [green, RCLike.inner_apply, mul_comm]

theorem conv_input_continuous (κ : ℝ) (hk : 0 < κ) (x : ℝ) :
    Continuous (fun f : H => conv κ (fun t => f t) x) := by
  simpa only [conv_row_pair κ hk x] using (innerSL ℂ (convRow κ hk x)).continuous

theorem conv_schwartz_integrable (κ : ℝ) (hk : 0 < κ) (f : 𝓢(ℝ,ℂ)) :
    Integrable (conv κ f) :=
  (green_integrable κ hk).integrable_convolution f.integrable

theorem conv_schwartz_mem (κ : ℝ) (hk : 0 < κ) (f : 𝓢(ℝ,ℂ)) :
    MemLp (conv κ f) 2 volume := by
  have hi := conv_schwartz_integrable κ hk f
  let C := (1/(2*κ)) * ∫ t : ℝ, ‖f t‖
  have hb (x : ℝ) : ‖conv κ f x‖ ≤ C := by
    rw [conv_integral]
    apply (norm_integral_le_integral_norm _).trans
    unfold C
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun t => norm_nonneg _
    · exact f.integrable.norm.const_mul _
    · filter_upwards [] with t
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (green_bound κ hk _) (norm_nonneg _)
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).2
  apply (hi.norm.const_mul C).mono'
  · exact hi.aestronglyMeasurable.norm.pow 2
  · filter_upwards [] with x
    rw [Real.norm_of_nonneg (sq_nonneg _),pow_two]
    exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

theorem conv_schwartz_fourier (κ : ℝ) (hk : 0 < κ) (f : 𝓢(ℝ,ℂ)) (ξ : ℝ) :
    𝓕 (conv κ f) ξ = multiplier κ ξ * 𝓕 (f : ℝ → ℂ) ξ := by
  rw [conv, Real.fourier_mul_convolution_eq (green_integrable κ hk) f.integrable,green_fourier κ hk]

theorem resolvent_schwartz_conv (κ : ℝ) (hk : 0 < κ) (f : 𝓢(ℝ,ℂ)) :
    (fun x => freeResolvent κ hk (f.toLp 2) x) =ᵐ[volume]
      (fun x => conv κ (fun t => f.toLp 2 t) x) := by
  let g := (conv_schwartz_mem κ hk f).toLp _
  have hg : (fun x => g x) =ᵐ[volume] conv κ f :=
    (conv_schwartz_mem κ hk f).coeFn_toLp
  have hgi : Integrable (fun x => g x) :=
    (conv_schwartz_integrable κ hk f).congr hg.symm
  have hf : (fun x => f.toLp 2 x) =ᵐ[volume] (f : ℝ → ℂ) := f.coeFn_toLp 2 volume
  have hfi : Integrable (fun x => f.toLp 2 x) := f.integrable.congr hf.symm
  have he : g = freeResolvent κ hk (f.toLp 2) := by
    apply fourier.injective
    apply Lp.ext
    filter_upwards [fourier_integral_agreement g hgi, fourier_integral_agreement (f.toLp 2) hfi,
      freeResolvent_fourier_ae κ hk (f.toLp 2)] with x h1 h2 h3
    rw [h1,h3,h2,Real.fourier_congr_ae hg,Real.fourier_congr_ae hf,conv_schwartz_fourier κ hk f]
  rw [← he]
  filter_upwards [hg] with x hx
  rw [hx,conv_integral,conv_integral]
  apply integral_congr_ae
  filter_upwards [hf] with t ht
  rw [ht]

/-- Density of Schwartz functions and convergence in measure give the full L² identity;
each convolution evaluation is a continuous Hilbert-space functional. -/
theorem resolvent_convolution_ae (κ : ℝ) (hk : 0 < κ) (f : H) :
    (fun x => freeResolvent κ hk f x) =ᵐ[volume]
      (fun x => ∫ t : ℝ, green κ (x-t) * f t) := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top
  obtain ⟨s,hs⟩ : ∃ s : ℕ → 𝓢(ℝ,ℂ),
      Tendsto (fun n => (s n).toLp 2) atTop (𝓝 f) := by
    first | exact hd.exists_seq_tendsto f | exact?
  have hr : Tendsto (fun n => freeResolvent κ hk ((s n).toLp 2)) atTop
      (𝓝 (freeResolvent κ hk f)) :=
    (freeResolvent κ hk).continuous.continuousAt.tendsto.comp hs
  obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hr).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂volume, ∀ n : ℕ,
      freeResolvent κ hk ((s n).toLp 2) x = conv κ (fun t => (s n).toLp 2 t) x :=
    ae_all_iff.mpr (fun n => resolvent_schwartz_conv κ hk (s n))
  filter_upwards [hae,hall] with x hx hy
  have hc := (conv_input_continuous κ hk x).continuousAt.tendsto.comp (hs.comp hns.tendsto_atTop)
  have hsame : (fun n => freeResolvent κ hk ((s (ns n)).toLp 2) x) =
      (fun n => conv κ (fun t => (s (ns n)).toLp 2 t) x) := funext (fun n => hy (ns n))
  rw [hsame] at hx
  exact (tendsto_nhds_unique hx hc).trans (conv_integral κ (fun t => f t) x)

end
end Manuscript13.EllisGreenConvolution20261127
#print axioms Manuscript13.EllisGreenConvolution20261127.green_integrable
#print axioms Manuscript13.EllisGreenConvolution20261127.green_bound
#print axioms Manuscript13.EllisGreenConvolution20261127.green_memLp
#print axioms Manuscript13.EllisGreenConvolution20261127.green_fourier
#print axioms Manuscript13.EllisGreenConvolution20261127.fourier_integral_agreement
#print axioms Manuscript13.EllisGreenConvolution20261127.conv
#print axioms Manuscript13.EllisGreenConvolution20261127.conv_integral
#print axioms Manuscript13.EllisGreenConvolution20261127.conv_row_mem
#print axioms Manuscript13.EllisGreenConvolution20261127.convRow
#print axioms Manuscript13.EllisGreenConvolution20261127.conv_row_pair
#print axioms Manuscript13.EllisGreenConvolution20261127.conv_input_continuous
#print axioms Manuscript13.EllisGreenConvolution20261127.conv_schwartz_integrable
#print axioms Manuscript13.EllisGreenConvolution20261127.conv_schwartz_mem
#print axioms Manuscript13.EllisGreenConvolution20261127.conv_schwartz_fourier
#print axioms Manuscript13.EllisGreenConvolution20261127.resolvent_schwartz_conv
#print axioms Manuscript13.EllisGreenConvolution20261127.resolvent_convolution_ae
