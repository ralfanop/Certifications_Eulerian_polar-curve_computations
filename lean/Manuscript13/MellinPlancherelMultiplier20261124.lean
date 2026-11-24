import Mathlib
import Manuscript13.MellinRindler20261124
import Manuscript13.MellinL2LogJacobian20261124

/-! M13 Theorem 4.14: actual L² Fourier-Plancherel equivalence,
bounded multiplication operators and the norm of the Rindler multiplier.
Mathlib uses cycles (exp(-2π i x ξ)); the manuscript uses angular
frequency, hence the full-line cutoff is ±1/(4π).
The integral kernel identification and unbounded dilation generator
are separate obligations. -/
open MeasureTheory Set
open scoped ENNReal
namespace Manuscript13.MellinPlancherelMultiplier20261124
noncomputable section
open Manuscript13.MellinRindler20261124 (multiplier multiplier_pos multiplier_bound multiplier_attains)
open Manuscript13.MellinL2LogJacobian20261124 (expMeasure logUnitary bandMeasure rindler_essential_bound)

abbrev H (μ : Measure ℝ) := Lp ℂ 2 μ

def mellinFourier : H expMeasure ≃ₗᵢ[ℂ] H volume :=
  logUnitary.trans (Lp.fourierTransformₗᵢ ℝ ℂ)

theorem mellin_norm (f : H expMeasure) : ‖mellinFourier f‖ = ‖f‖ :=
  mellinFourier.norm_map f

theorem mellin_inverse (f : H expMeasure) :
    mellinFourier.symm (mellinFourier f) = f :=
  mellinFourier.symm_apply_apply f

theorem mellin_surjective : Function.Surjective mellinFourier :=
  mellinFourier.surjective

theorem mul_mem {μ : Measure ℝ} (m : ℝ → ℂ) (hm : Measurable m)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : H μ) :
    MemLp (fun x => m x * f x) 2 μ := by
  apply (Lp.memLp ((C : ℂ) • f)).mono
  · exact hm.aestronglyMeasurable.mul f.aestronglyMeasurable
  · filter_upwards [hb, Lp.coeFn_smul (C : ℂ) f] with x hx he
    rw [norm_mul]
    change (((C : ℂ) • f) x) = (C : ℂ) * f x at he
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

def mulFun {μ : Measure ℝ} (m : ℝ → ℂ) (hm : Measurable m)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : H μ) : H μ :=
  (mul_mem m hm C hC hb f).toLp _

theorem mulFun_ae {μ : Measure ℝ} (m : ℝ → ℂ) (hm : Measurable m)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : H μ) :
    (fun x => mulFun m hm C hC hb f x) =ᵐ[μ] (fun x => m x * f x) :=
  (mul_mem m hm C hC hb f).coeFn_toLp

theorem mulFun_bound {μ : Measure ℝ} (m : ℝ → ℂ) (hm : Measurable m)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : H μ) :
    ‖mulFun m hm C hC hb f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mulFun_ae m hm C hC hb f, hb] with x hx hbx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hbx (norm_nonneg _)

def mulLinear {μ : Measure ℝ} (m : ℝ → ℂ) (hm : Measurable m)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) : H μ →ₗ[ℂ] H μ where
  toFun := mulFun m hm C hC hb
  map_add' f g := by
    apply Lp.ext
    filter_upwards [mulFun_ae m hm C hC hb (f+g), mulFun_ae m hm C hC hb f,
      mulFun_ae m hm C hC hb g, Lp.coeFn_add f g,
      Lp.coeFn_add (mulFun m hm C hC hb f) (mulFun m hm C hC hb g)] with x hfg hf hg hadd hout
    rw [hfg, hout]
    change (f+g) x = f x + g x at hadd
    change m x * (f+g) x = mulFun m hm C hC hb f x + mulFun m hm C hC hb g x
    rw [hadd, hf, hg, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [mulFun_ae m hm C hC hb (c • f), mulFun_ae m hm C hC hb f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (mulFun m hm C hC hb f)] with x hcf hf hsm hout
    change mulFun m hm C hC hb (c • f) x = (c • mulFun m hm C hC hb f) x
    rw [hcf, hout]
    change (c • f) x = c * f x at hsm
    change m x * (c • f) x = c * mulFun m hm C hC hb f x
    rw [hsm, hf]
    ring

def mulOperator {μ : Measure ℝ} (m : ℝ → ℂ) (hm : Measurable m)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) : H μ →L[ℂ] H μ :=
  (mulLinear m hm C hC hb).mkContinuous C (mulFun_bound m hm C hC hb)

theorem mulOperator_ae {μ : Measure ℝ} (m : ℝ → ℂ) (hm : Measurable m)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : H μ) :
    (fun x => mulOperator m hm C hC hb f x) =ᵐ[μ] (fun x => m x * f x) :=
  mulFun_ae m hm C hC hb f

theorem mulOperator_norm_le {μ : Measure ℝ} (m : ℝ → ℂ) (hm : Measurable m)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) :
    ‖mulOperator m hm C hC hb‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (mulFun_bound m hm C hC hb)

/-- Test on the indicator of a finite positive-measure strict superlevel set. -/
theorem mulOperator_norm_lower {μ : Measure ℝ} (m : ℝ → ℂ) (hm : Measurable m)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C)
    (b : ℝ) (hb0 : 0 ≤ b) (s : Set ℝ) (hs : MeasurableSet s)
    (hfin : μ s ≠ ⊤) (hpos : μ s ≠ 0)
    (hlow : ∀ x ∈ s, b ≤ ‖m x‖) :
    b ≤ ‖mulOperator m hm C hC hb‖ := by
  let f : H μ := indicatorConstLp 2 hs hfin (1 : ℂ)
  have hf : (fun x => f x) =ᵐ[μ] s.indicator (fun _ => (1 : ℂ)) :=
    indicatorConstLp_coeFn
  have hf0 : f ≠ 0 := by
    intro hz
    have hz' := Lp.eq_zero_iff_ae_eq_zero.mp hz
    have ha : ∀ᵐ x ∂μ, x ∉ s := by
      filter_upwards [hf, hz'] with x hfx hzx
      intro hx
      have he : f x = 1 := by simpa [Set.indicator_of_mem hx] using hfx
      have he' : f x = 0 := hzx
      rw [he] at he'
      exact one_ne_zero he'
    have hzμ : μ s = 0 := by
      simpa using (ae_iff.mp ha)
    exact hpos hzμ
  have hnorm : 0 < ‖f‖ := norm_pos_iff.mpr hf0
  have htest : b * ‖f‖ ≤ ‖mulOperator m hm C hC hb f‖ := by
    have h := Lp.norm_le_norm_of_ae_le (f := (b : ℂ) • f)
      (g := mulOperator m hm C hC hb f) (by
        filter_upwards [hf, Lp.coeFn_smul (b : ℂ) f,
          mulOperator_ae m hm C hC hb f] with x hx hc ht
        change (((b : ℂ) • f) x) = (b : ℂ)*f x at hc
        rw [hc, ht, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]
        by_cases hxs : x ∈ s
        · exact mul_le_mul_of_nonneg_right (hlow x hxs) (norm_nonneg _)
        · have hfz : f x = 0 := by simpa [Set.indicator_of_notMem hxs] using hx
          simp [hfz])
    have heq : ‖(b : ℂ) • f‖ = b * ‖f‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]
    rw [← heq]
    exact h
  exact le_of_mul_le_mul_right (htest.trans (ContinuousLinearMap.le_opNorm _ f)) hnorm

theorem rindler_ae_bound (n : ℤ) :
    ∀ᵐ x ∂bandMeasure, ‖(multiplier n x : ℂ)‖ ≤ Real.exp (Real.pi*|(n : ℝ)|) := by
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with x hx
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (multiplier_pos n x).le]
  exact multiplier_bound n x hx

def rindlerOperator (n : ℤ) : H bandMeasure →L[ℂ] H bandMeasure :=
  mulOperator (fun x => (multiplier n x : ℂ)) (by unfold multiplier; fun_prop)
    (Real.exp (Real.pi*|(n : ℝ)|)) (Real.exp_pos _).le (rindler_ae_bound n)

theorem rindlerOperator_norm (n : ℤ) :
    ‖rindlerOperator n‖ = Real.exp (Real.pi*|(n : ℝ)|) := by
  let C := Real.exp (Real.pi*|(n : ℝ)|)
  have hleast := rindler_essential_bound n (multiplier_bound n) (multiplier_attains n)
  have hle : ‖rindlerOperator n‖ ≤ C := mulOperator_norm_le _ _ _ _ _
  apply le_antisymm hle
  by_contra! hh
  let b := (‖rindlerOperator n‖ + C)/2
  have hb0 : 0 ≤ b := by dsimp [b, C]; positivity
  have hbc : b < C := by dsimp [b]; linarith
  let s : Set ℝ := {x | b < multiplier n x}
  have hs : MeasurableSet s := measurableSet_lt measurable_const (by unfold multiplier; fun_prop)
  have hfin : bandMeasure s ≠ ⊤ := by
    unfold bandMeasure
    rw [Measure.restrict_apply hs]
    apply ne_of_lt
    calc
      volume (s ∩ Icc (-(1/2 : ℝ)) (1/2 : ℝ)) ≤ volume (Icc (-(1/2 : ℝ)) (1/2 : ℝ)) :=
        measure_mono inter_subset_right
      _ < ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hpos : bandMeasure s ≠ 0 := by
    intro hz
    have hAE : ∀ᵐ x ∂bandMeasure, multiplier n x ≤ b := by
      apply ae_iff.mpr
      simpa [s, not_le] using hz
    exact (not_le_of_gt hbc) (hleast.2 hAE)
  have ht := mulOperator_norm_lower (fun x => (multiplier n x : ℂ))
    (by unfold multiplier; fun_prop) C (Real.exp_pos _).le (rindler_ae_bound n)
    b hb0 s hs hfin hpos (by
      intro x hx
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (multiplier_pos n x).le]
      exact le_of_lt hx)
  change b ≤ ‖rindlerOperator n‖ at ht
  dsimp [b] at ht
  linarith

def cyclesBand : Set ℝ := Icc (-(1/(4*Real.pi))) (1/(4*Real.pi))

theorem cyclesBand_angular (x : ℝ) :
    x ∈ cyclesBand ↔ 2*Real.pi*x ∈ Manuscript13.MellinRindler20261124.band := by
  have hp : 0 < Real.pi := Real.pi_pos
  have h2 : 0 < 2*Real.pi := by positivity
  change (-(1/(4*Real.pi)) ≤ x ∧ x ≤ 1/(4*Real.pi)) ↔
    (-(1/2 : ℝ) ≤ 2*Real.pi*x ∧ 2*Real.pi*x ≤ 1/2)
  constructor
  · rintro ⟨hl,hu⟩
    constructor
    · have h := (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).mp
        (show (-1 : ℝ)/(4*Real.pi) ≤ x by simpa [neg_div] using hl)
      nlinarith
    · have h := (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mp hu
      nlinarith
  · rintro ⟨hl,hu⟩
    constructor
    · rw [← neg_div]
      exact (div_le_iff₀ (by positivity : 0 < 4*Real.pi)).mpr (by nlinarith)
    · exact (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mpr (by nlinarith)

def cutoff : ℝ → ℂ := cyclesBand.indicator (fun _ => 1)

theorem cutoff_measurable : Measurable cutoff :=
  measurable_const.indicator measurableSet_Icc

theorem cutoff_bound : ∀ᵐ x ∂(volume : Measure ℝ), ‖cutoff x‖ ≤ (1:ℝ) := by
  filter_upwards [] with x
  by_cases hx : x ∈ cyclesBand <;> simp [cutoff, hx]

def spectralProject : H volume →L[ℂ] H volume :=
  mulOperator cutoff cutoff_measurable 1 zero_le_one cutoff_bound

theorem spectralProject_ae (f : H volume) :
    (fun x => spectralProject f x) =ᵐ[volume] (fun x => cutoff x * f x) :=
  mulOperator_ae _ _ _ _ _ f

theorem spectralProject_idempotent (f : H volume) :
    spectralProject (spectralProject f) = spectralProject f := by
  apply Lp.ext
  filter_upwards [spectralProject_ae f, spectralProject_ae (spectralProject f)] with x hx hy
  rw [hy, hx]
  by_cases h : x ∈ cyclesBand <;> simp [cutoff, h]

theorem spectralProject_norm_le : ‖spectralProject‖ ≤ 1 :=
  mulOperator_norm_le _ _ _ _ _

def mellinProject : H expMeasure →L[ℂ] H expMeasure :=
  mellinFourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (spectralProject.comp mellinFourier.toContinuousLinearEquiv.toContinuousLinearMap)

theorem mellinProject_apply (f : H expMeasure) :
    mellinProject f = mellinFourier.symm (spectralProject (mellinFourier f)) := rfl

theorem mellinProject_idempotent (f : H expMeasure) :
    mellinProject (mellinProject f) = mellinProject f := by
  simp only [mellinProject_apply, LinearIsometryEquiv.apply_symm_apply,
    spectralProject_idempotent]

/-- Angular-frequency cosine kernel, including the removable value. -/
theorem angular_cosine_kernel (x : ℝ) :
    (∫ ξ in (-(1/2 : ℝ))..(1/2 : ℝ), Real.cos (ξ*x)) =
      if x = 0 then 1 else 2*Real.sin (x/2)/x := by
  by_cases hx : x = 0
  · norm_num [hx]
  · have hd : ∀ t : ℝ, HasDerivAt (fun y : ℝ => Real.sin (y*x)/x)
        (Real.cos (t*x)) t := by
      intro t
      have h := ((Real.hasDerivAt_sin (t*x)).comp t
        ((hasDerivAt_id t).mul_const x)).div_const x
      convert h using 1
      all_goals simp [id_eq] <;> field_simp [hx]
    have hi : IntervalIntegrable (fun t : ℝ => Real.cos (t*x)) volume (-(1/2)) (1/2) :=
      (by fun_prop : Continuous (fun t : ℝ => Real.cos (t*x))).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
    simp only [hx, if_false, neg_mul, Real.sin_neg]
    ring_nf

end
end Manuscript13.MellinPlancherelMultiplier20261124
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.mellinFourier
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.mellin_norm
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.mellin_inverse
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.mellin_surjective
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.mul_mem
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.mulFun
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.mulFun_ae
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.mulFun_bound
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.mulLinear
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.mulOperator
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.mulOperator_ae
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.mulOperator_norm_le
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.mulOperator_norm_lower
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.rindler_ae_bound
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.rindlerOperator
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.rindlerOperator_norm
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.cyclesBand_angular

#print axioms Manuscript13.MellinPlancherelMultiplier20261124.cutoff_measurable
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.cutoff_bound
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.spectralProject
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.spectralProject_ae
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.spectralProject_idempotent
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.spectralProject_norm_le
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.mellinProject
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.mellinProject_apply
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.mellinProject_idempotent
#print axioms Manuscript13.MellinPlancherelMultiplier20261124.angular_cosine_kernel
