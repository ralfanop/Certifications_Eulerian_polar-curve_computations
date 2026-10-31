import Bridge.PaleyWiener3
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Corollary 3.11 (continued): `P_E` is the Fourier multiplier with symbol `1_{[-1/2,1/2]}`

For `f ∈ L¹ ∩ L²(ℝ)` with `f̂(ξ) = ∫ f(x) e^{-ixξ} dx` (convention (22)), `P_E f = T(f̂|_{[-1/2,1/2]})`.
Also: each integral in (28) converges absolutely (Cauchy–Schwarz).
-/

open MeasureTheory Complex Set Filter Topology
open scoped ComplexConjugate

namespace EulerianBridge.PW

open EulerianGrothendieck.Fock

/-- `f̂` restricted to `(-1/2,1/2]`, as a function on `𝕋`. -/
noncomputable def fhatFun (f : ℝ → ℂ) (θ : UnitAddCircle) : ℂ := ∫ x : ℝ, f x * cexp (-(I * x * rep θ))

theorem norm_fhatFun_le {f : ℝ → ℂ} (θ : UnitAddCircle) : ‖fhatFun f θ‖ ≤ ∫ x : ℝ, ‖f x‖ := by
  unfold fhatFun
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext x
  rw [norm_mul, Complex.norm_exp]
  have : (-(I * (x:ℂ) * (rep θ : ℂ))).re = 0 := by simp [Complex.mul_re]
  rw [this, Real.exp_zero, mul_one]

theorem continuous_fhat {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (fun ξ : ℝ => ∫ x : ℝ, f x * cexp (-(I * x * ξ))) := by
  refine continuous_of_dominated (bound := fun x => ‖f x‖) (fun ξ => ?_) (fun ξ => ?_) hf.norm ?_
  · exact hf.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))
  · refine Eventually.of_forall (fun x => le_of_eq ?_)
    rw [norm_mul, Complex.norm_exp]
    have : (-(I * (x:ℂ) * (ξ : ℂ))).re = 0 := by simp [Complex.mul_re]
    rw [this, Real.exp_zero, mul_one]
  · exact Eventually.of_forall (fun x => by fun_prop)

theorem memLp_fhat {f : ℝ → ℂ} (hf : Integrable f) : MemLp (fhatFun f) 2 μT := by
  refine MemLp.of_bound (C := ∫ x : ℝ, ‖f x‖) ?_ (Eventually.of_forall (fun θ => norm_fhatFun_le θ))
  exact ((continuous_fhat hf).measurable.comp measurable_rep).aestronglyMeasurable

/-- `f̂|_{(-1/2,1/2]} ∈ L²(𝕋)`. -/
noncomputable def fhat {f : ℝ → ℂ} (hf : Integrable f) : GI := (memLp_fhat hf).toLp _

section Plancherel

variable (hP : Plancherel)
include hP

/-- `⟨f, T h⟩_{L²(ℝ)} = (1/2π) ⟨f̂, h⟩` for `f ∈ L¹ ∩ L²` (Fubini). -/
theorem inner_f_Fv {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) (h : GI) :
    (inner ℂ (hf2.toLp f) (Fv hP h) : ℂ) = (1 / (2 * Real.pi)) * inner ℂ (fhat hf1) h := by
  rw [L2.inner_def, L2.inner_def]
  have e1 : ∫ x : ℝ, inner ℂ ((hf2.toLp f : L2R) x) ((Fv hP h : L2R) x)
      = ∫ x : ℝ, conj (f x) * T h x := by
    refine integral_congr_ae ?_
    filter_upwards [hf2.coeFn_toLp, Fv_coe hP h] with x h1 h2
    rw [h1, h2, RCLike.inner_apply]; ring
  have e2 : ∫ θ, inner ℂ ((fhat hf1 : GI) θ) ((h : GI) θ) ∂μT
      = ∫ θ, conj (fhatFun f θ) * h θ ∂μT := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_fhat hf1).coeFn_toLp] with θ h1
    rw [fhat, h1, RCLike.inner_apply]; ring
  rw [e1, e2]
  simp_rw [T_eq_integral, ← MeasureTheory.integral_const_mul]
  -- Fubini
  have hint : Integrable (Function.uncurry fun (x : ℝ) (θ : UnitAddCircle) =>
      conj (f x) * (1 / (2 * Real.pi) * (cexp (I * x * rep θ) * h θ))) (volume.prod μT) := by
    have hh : Integrable (fun θ => (h : UnitAddCircle → ℂ) θ) μT := (Lp.memLp h).integrable one_le_two
    have hprod := (hf1.norm.mul_prod hh.norm)
    refine (hprod.const_mul (1 / (2 * Real.pi))).mono' ?_ (Eventually.of_forall (fun p => ?_))
    · refine (hf1.aestronglyMeasurable.star.comp_fst).mul ?_
      refine aestronglyMeasurable_const.mul ?_
      refine AEStronglyMeasurable.mul ?_ hh.aestronglyMeasurable.comp_snd
      exact ((Continuous.measurable (by fun_prop : Continuous fun q : ℝ × ℝ => cexp (I * q.1 * q.2))).comp
        (measurable_fst.prodMk (measurable_rep.comp measurable_snd))).aestronglyMeasurable
    · rw [Function.uncurry_apply_pair, norm_mul, norm_mul, norm_mul, Complex.norm_exp, RCLike.norm_conj]
      have : (I * (p.1 : ℂ) * (rep p.2 : ℂ)).re = 0 := by simp [Complex.mul_re]
      rw [this, Real.exp_zero, one_mul]
      have hc : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
        rw [show ((1 / (2 * Real.pi)) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [hc]; exact le_of_eq (by ring)
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall (fun θ => ?_))
  show ∫ x : ℝ, conj (f x) * (1 / (2 * Real.pi) * (cexp (I * x * rep θ) * h θ))
    = 1 / (2 * Real.pi) * (conj (fhatFun f θ) * h θ)
  unfold fhatFun
  rw [← integral_conj, ← MeasureTheory.integral_mul_const, ← MeasureTheory.integral_const_mul]
  congr 1; funext x
  rw [map_mul, ← Complex.exp_conj]
  have : conj (-(I * (x:ℂ) * (rep θ : ℂ))) = I * x * rep θ := by
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [this]; ring

/-- Corollary 3.11: `P_E` is the Fourier multiplier with symbol `1_{[-1/2,1/2]}`. -/
theorem PE_multiplier {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    PE hP (hf2.toLp f) = Fv hP (fhat hf1) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := PWsub hP)
    (show Fv hP (fhat hf1) ∈ PWsub hP from ⟨fhat hf1, rfl⟩)
  intro w hw
  obtain ⟨h, rfl⟩ := hw
  change (inner ℂ (hf2.toLp f - Fv hP (fhat hf1)) (Fv hP h) : ℂ) = 0
  rw [inner_sub_left, inner_f_Fv hP hf1 hf2, inner_Fv, sub_self]

/-- The integrals in (28) converge absolutely: `y ↦ r_E(x-y) f(y)` is integrable for `f ∈ L²`. -/
theorem kernel_integrable (f : L2R) (x : ℝ) : Integrable (fun y : ℝ => rE (x - y) * f y) := by
  have hK : MemLp (fun y : ℝ => rE (x - y)) 2 volume := by
    have h := ((hP (kz x)).1).const_mul (2 * Real.pi : ℂ)
    refine h.ae_eq (Eventually.of_forall (fun y => ?_))
    simp only
    rw [← KE_eq_T, KE_eq, Complex.conj_ofReal,
      show (y:ℂ) - x = -((x:ℂ) - y) by ring, EulerianBridge.Fock3.rE_neg]
    have hp : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0:ℝ) < 2 * Real.pi).ne'
    field_simp
  exact hK.integrable_mul (Lp.memLp f)

end Plancherel

end EulerianBridge.PW
