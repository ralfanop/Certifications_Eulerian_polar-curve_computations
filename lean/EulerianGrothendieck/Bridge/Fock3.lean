import EulerianGrothendieck.FockVacuumProjection
import Bridge.AppendixA
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Section 3: momentum realisation, coherent kernels and exact Fock norms

Manuscript V173, Propositions 3.1–3.3 and eqs. (15)–(18), (21)–(26) and (46).

* Prop. 3.1: `‖ψ_L‖ = 1` and `(F_ħ ψ_L)(p) = √(L/(2πħ)) r_E(pL/ħ)`;
* Prop. 3.2: `r_E(z) = ∫_{-1/2}^{1/2} e^{itz} dt = ∫ K_α(z,-it/α) dt`, the same for
  `G_E(z) = e^{iz} r_E(z)` on `[1/2,3/2]`; `r_E` and `G_E` are entire and lie in `L²(μ_α)`;
* Prop. 3.3: `‖r_E‖² = ∫∫_{[-1/2,1/2]²} e^{ts/α} = ∑_k 1/(2^{4k} α^{2k} (2k)! (2k+1)²)`,
  `‖G_E‖² = ∫∫_{[1/2,3/2]²} e^{ts/α}`, the upper bounds (23), and the closed form (46)
  `‖r_E‖² = 4α ∫_0^{1/2} sinh(t/(2α))/t dt = 4α Shi(1/(4α))`.
-/

open MeasureTheory Complex Set intervalIntegral ProbabilityTheory Filter Topology
open scoped ComplexConjugate

namespace EulerianBridge.Fock3

open EulerianGrothendieck.Fock

/-! ## Proposition 3.1 -/

/-- `ψ_L = L^{-1/2} 1_{[-L/2,L/2]}`. -/
noncomputable def psiL (L : ℝ) (q : ℝ) : ℝ := (Icc (-L/2) (L/2)).indicator (fun _ => 1 / Real.sqrt L) q

theorem psiL_norm {L : ℝ} (hL : 0 < L) : ∫ q, psiL L q ^ 2 = 1 := by
  have : (fun q => psiL L q ^ 2) = (Icc (-L/2) (L/2)).indicator (fun _ => 1 / L) := by
    funext q; unfold psiL
    by_cases hq : q ∈ Icc (-L/2) (L/2)
    · rw [indicator_of_mem hq, indicator_of_mem hq, div_pow, Real.sq_sqrt hL.le]; ring
    · rw [indicator_of_notMem hq, indicator_of_notMem hq]; ring
  rw [this, MeasureTheory.integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc]
  rw [max_eq_left (by linarith)]
  simp only [smul_eq_mul]
  field_simp; ring

/-- The unitary momentum transform `(F_ħψ)(p) = (2πħ)^{-1/2} ∫ e^{-ipq/ħ} ψ(q) dq`. -/
noncomputable def momentum (ħ : ℝ) (ψ : ℝ → ℝ) (p : ℝ) : ℂ :=
  ((2 * Real.pi * ħ) ^ (-(1:ℝ) / 2) : ℝ) * ∫ q : ℝ, cexp (-I * p * q / ħ) * (ψ q : ℂ)

theorem rE_neg (z : ℂ) : rE (-z) = rE z := by
  unfold rE
  have h := intervalIntegral.integral_comp_neg (a := (-1/2:ℝ)) (b := 1/2)
    (fun t : ℝ => cexp (I * (t:ℂ) * -z))
  rw [show -(1/2:ℝ) = -1/2 by ring, show -(-1/2:ℝ) = 1/2 by ring] at h
  rw [← h]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [ofReal_neg]; ring_nf

/-- Proposition 3.1, eq. (17). -/
theorem momentum_psiL {L ħ : ℝ} (hL : 0 < L) (hħ : 0 < ħ) (p : ℝ) :
    momentum ħ (psiL L) p = ((Real.sqrt (L / (2 * Real.pi * ħ)) : ℝ) : ℂ) * rE (p * L / ħ) := by
  unfold momentum
  have hint : ∫ q : ℝ, cexp (-I * p * q / ħ) * ((psiL L q : ℝ) : ℂ)
      = ((1 / Real.sqrt L : ℝ) : ℂ) * ∫ q in (-L/2)..(L/2), cexp (-I * p * q / ħ) := by
    have e : ∀ q : ℝ, cexp (-I * p * q / ħ) * ((psiL L q : ℝ) : ℂ)
        = (Icc (-L/2) (L/2)).indicator
            (fun q : ℝ => ((1 / Real.sqrt L : ℝ) : ℂ) * cexp (-I * p * q / ħ)) q := by
      intro q; unfold psiL
      by_cases hq : q ∈ Icc (-L/2) (L/2)
      · rw [indicator_of_mem hq, indicator_of_mem hq]; ring
      · rw [indicator_of_notMem hq, indicator_of_notMem hq]; simp
    rw [MeasureTheory.integral_congr_ae (Eventually.of_forall e),
      MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul]
  rw [hint]
  have hsub : ∫ q in (-L/2)..(L/2), cexp (-I * p * q / ħ) = (L : ℂ) * rE (p * L / ħ) := by
    have h := intervalIntegral.integral_comp_mul_left (fun q : ℝ => cexp (-I * p * q / ħ)) hL.ne'
      (a := -1/2) (b := 1/2)
    rw [show L * (-1/2) = -L/2 by ring, show L * (1/2) = L/2 by ring] at h
    rw [← smul_inv_smul₀ hL.ne' (∫ q in (-L/2)..(L/2), cexp (-I * p * q / ħ)), ← h,
      Complex.real_smul, ← rE_neg, rE]
    congr 1
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only []
    congr 1; push_cast; field_simp
  rw [hsub]
  have hsq : Real.sqrt (L / (2 * Real.pi * ħ)) = (2 * Real.pi * ħ) ^ (-(1:ℝ) / 2) * (1 / Real.sqrt L) * L := by
    have h2 : 0 < 2 * Real.pi * ħ := by positivity
    rw [Real.sqrt_div hL.le, show (-(1:ℝ) / 2) = -(1/2) by ring, Real.rpow_neg h2.le, ← Real.sqrt_eq_rpow]
    have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
    have hs2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
    field_simp
    nlinarith
  rw [hsq]; push_cast; ring

/-! ## Proposition 3.2 -/

/-- The Gaussian Fock reproducing kernel `K_α(z,w) = e^{α z w̄}`. -/
noncomputable def K (α : ℝ) (z w : ℂ) : ℂ := cexp (α * z * conj w)

theorem kernel_point (α : ℝ) (hα : α ≠ 0) (z : ℂ) (t : ℝ) : K α z (-(I * t / α)) = cexp (I * t * z) := by
  unfold K
  have hα' : (α:ℂ) ≠ 0 := by exact_mod_cast hα
  congr 1
  simp [map_neg, map_div₀, Complex.conj_ofReal, Complex.conj_I]
  field_simp

/-- Eq. (21). -/
theorem rE_kernel (α : ℝ) (hα : α ≠ 0) (z : ℂ) :
    rE z = ∫ t in (-1/2:ℝ)..(1/2), K α z (-(I * t / α)) := by
  unfold rE
  congr 1; funext t; rw [kernel_point α hα]

/-- `G_E(z) = e^{iz} r_E(z)`. -/
noncomputable def GE (z : ℂ) : ℂ := cexp (I * z) * rE z

/-- Eq. (22). -/
theorem GE_kernel (α : ℝ) (hα : α ≠ 0) (z : ℂ) :
    GE z = ∫ t in (1/2:ℝ)..(3/2), cexp (I * t * z) ∧
      GE z = ∫ t in (1/2:ℝ)..(3/2), K α z (-(I * t / α)) := by
  have h1 : GE z = ∫ t in (1/2:ℝ)..(3/2), cexp (I * t * z) := by
    unfold GE rE
    rw [← intervalIntegral.integral_const_mul]
    have := intervalIntegral.integral_comp_add_right (fun t : ℝ => cexp (I * t * z)) (1:ℝ)
      (a := -1/2) (b := 1/2)
    rw [show (-1/2:ℝ) + 1 = 1/2 by norm_num, show (1/2:ℝ) + 1 = 3/2 by norm_num] at this
    rw [← this]
    congr 1; funext t
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  exact ⟨h1, by rw [h1]; congr 1; funext t; rw [kernel_point α hα]⟩

/-- `r_E = dslope (2 sin(·/2)) 0`, hence `r_E` is entire. -/
theorem rE_eq_dslope : rE = dslope (fun z => 2 * Complex.sin (z / 2)) 0 := by
  funext z
  rcases eq_or_ne z 0 with rfl | hz
  · rw [dslope_same, rE_zero]
    have h : HasDerivAt (fun z : ℂ => 2 * Complex.sin (z / 2)) 1 0 := by
      have h0 := ((Complex.hasDerivAt_sin (0 / 2)).comp (0:ℂ) ((hasDerivAt_id (0:ℂ)).div_const 2)).const_mul 2
      convert h0 using 1 <;> simp
    rw [h.deriv]
  · rw [dslope_of_ne _ hz, slope_def_module, rE_eq_sin_div hz]
    simp only [sub_zero, zero_div, Complex.sin_zero, mul_zero, smul_eq_mul]
    field_simp

theorem rE_differentiable : Differentiable ℂ rE := by
  rw [rE_eq_dslope]
  intro z
  have h : DifferentiableOn ℂ (dslope (fun z => 2 * Complex.sin (z / 2)) 0) univ :=
    (differentiableOn_dslope univ_mem).mpr (by fun_prop)
  exact (h z (mem_univ z)).differentiableAt univ_mem

theorem GE_differentiable : Differentiable ℂ GE := by
  unfold GE; exact (by fun_prop : Differentiable ℂ fun z => cexp (I * z)).mul rE_differentiable

theorem norm_GE_sq_le (z : ℂ) : ‖GE z‖ ^ 2 ≤ Real.exp (3 * |z.im|) := by
  unfold GE
  rw [norm_mul, mul_pow, Complex.norm_exp]
  have h1 : (I * z).re = -z.im := by simp [Complex.mul_re]
  rw [h1]
  have h2 := norm_rE_le z
  calc Real.exp (-z.im) ^ 2 * ‖rE z‖ ^ 2 ≤ Real.exp (|z.im|) ^ 2 * Real.exp (|z.im| / 2) ^ 2 := by
        gcongr
        exact neg_le_abs z.im
    _ = Real.exp (3 * |z.im|) := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf

/-- `G_E ∈ L²(μ_α)`. -/
theorem memLp_GE {α : ℝ} (hα : 0 < α) : MemLp GE 2 (fockMeasure α) := by
  have hc : Continuous GE := GE_differentiable.continuous
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  rw [fockMeasure, integrable_withDensity_iff_integrable_smul (measurable_fockDensity_nnreal α)]
  refine (integrable_exp_abs_im_mul_fockDensity hα 3).mono' ?_ (Filter.Eventually.of_forall
    (fun z => ?_))
  · exact ((continuous_real_toNNReal.comp (continuous_fockDensity α)).smul
      (hc.norm.pow 2)).aestronglyMeasurable
  · rw [NNReal.smul_def, Real.coe_toNNReal _ (fockDensity_nonneg hα.le z), smul_eq_mul,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (fockDensity_nonneg hα.le z) (sq_nonneg _)),
      mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_GE_sq_le z) (fockDensity_nonneg hα.le z)

theorem memLp_rE {α : ℝ} (hα : 0 < α) : MemLp rE 2 (fockMeasure α) := by
  simpa using memLp_rE_pow hα 1

/-! ## Proposition 3.3 -/

/-- The uniform law on `[-1/2,1/2]` is a probability measure. -/
instance : IsProbabilityMeasure V033.UniformSum.uniformLaw := by
  constructor
  simp [V033.UniformSum.uniformLaw]
  norm_num

/-- The product law of the pair `(t,s)`. -/
noncomputable abbrev ν : Measure (ℝ × ℝ) := V033.UniformSum.uniformLaw.prod V033.UniformSum.uniformLaw

theorem ae_abs_le_half : ∀ᵐ x ∂V033.UniformSum.uniformLaw, |x| ≤ 1 / 2 := by
  unfold V033.UniformSum.uniformLaw
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall (fun x hx => ?_))
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2]

theorem charFun_uniform (z : ℂ) : ∫ x, cexp (I * z * (x : ℂ)) ∂V033.UniformSum.uniformLaw = rE z :=
  uniform_charFun (μ := V033.UniformSum.uniformLaw) measurable_id (by simp) z

/-- `|r_E(z)|² = E e^{izX - i z̄ Y}` for independent uniform `X, Y`. -/
theorem norm_sq_rE_pair (z : ℂ) :
    ((‖rE z‖ ^ 2 : ℝ) : ℂ) = ∫ p, cexp (I * z * (p.1 : ℂ) - I * conj z * (p.2 : ℂ)) ∂ν := by
  have hconj : conj (rE z) = ∫ x, cexp (-I * conj z * (x : ℂ)) ∂V033.UniformSum.uniformLaw := by
    rw [← charFun_uniform, ← integral_conj]
    congr 1; funext x
    rw [← Complex.exp_conj, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hnorm : ((‖rE z‖ ^ 2 : ℝ) : ℂ) = rE z * conj (rE z) := by
    rw [Complex.mul_conj']; push_cast; ring
  rw [hnorm, hconj]
  conv_lhs => rw [← charFun_uniform]
  rw [← integral_prod_mul]
  congr 1; funext p
  rw [← Complex.exp_add]; congr 1; ring

/-- Prop. 3.3, (24) first equality, in probabilistic form: `‖r_E‖² = E e^{XY/α}`. -/
theorem fock_norm_rE_pair {α : ℝ} (hα : 0 < α) :
    ∫ z : ℂ, ‖rE z‖ ^ 2 * fockDensity α z = ∫ p, Real.exp (p.1 * p.2 / α) ∂ν := by
  have hX : ∀ᵐ p ∂ν, |p.1| ≤ 1 / 2 := Measure.quasiMeasurePreserving_fst.ae ae_abs_le_half
  have hY : ∀ᵐ p ∂ν, |p.2| ≤ 1 / 2 := Measure.quasiMeasurePreserving_snd.ae ae_abs_le_half
  have hfub := gaussian_fubini measurable_fst measurable_snd (1 / 2) hX hY hα
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  have hlhs : ∀ z : ℂ, (((‖rE z‖ ^ 2 * fockDensity α z : ℝ)) : ℂ) =
      (∫ p, cexp (I * z * (p.1 : ℂ) - I * conj z * (p.2 : ℂ)) ∂ν) * (fockDensity α z : ℂ) := by
    intro z; rw [ofReal_mul, norm_sq_rE_pair]
  simp_rw [hlhs]
  rw [hfub]
  congr 1; funext p
  rw [ofReal_exp, ofReal_div, ofReal_mul]

/-- Integrals against the product uniform law are iterated interval integrals. -/
theorem integral_ν (f : ℝ → ℝ → ℝ) (hf : Continuous (Function.uncurry f)) :
    ∫ p, f p.1 p.2 ∂ν = ∫ t in (-1/2:ℝ)..(1/2), ∫ s in (-1/2:ℝ)..(1/2), f t s := by
  rw [integral_prod]
  · unfold V033.UniformSum.uniformLaw
    rw [intervalIntegral.integral_of_le (by norm_num)]
    congr 1; funext t
    rw [intervalIntegral.integral_of_le (by norm_num)]
  · unfold V033.UniformSum.uniformLaw
    rw [Measure.prod_restrict]
    refine (ContinuousOn.integrableOn_compact ((isCompact_Icc (a := (-1/2:ℝ)) (b := 1/2)).prod
      (isCompact_Icc (a := (-1/2:ℝ)) (b := 1/2))) hf.continuousOn).mono_set ?_
    intro p hp; exact ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2⟩⟩

/-- Prop. 3.3, eq. (24), first equality. -/
theorem fock_norm_rE {α : ℝ} (hα : 0 < α) :
    ∫ z : ℂ, ‖rE z‖ ^ 2 * fockDensity α z =
      ∫ t in (-1/2:ℝ)..(1/2), ∫ s in (-1/2:ℝ)..(1/2), Real.exp (t * s / α) := by
  rw [fock_norm_rE_pair hα, integral_ν (fun t s => Real.exp (t * s / α)) (by fun_prop)]

end EulerianBridge.Fock3
