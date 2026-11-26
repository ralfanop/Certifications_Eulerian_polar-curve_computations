import Mathlib
import Manuscript16.RobinDirichletRealisation20261125

/-!
# M16 v16.5 §14.2, Proposition 14.2: the self-adjoint operators `H_D`, `H_R` do not depend on the level `t`

Setting of `RobinDirichletRankOne20261125` (#603): `c = ‖κ‖²`, `β > 0`, `t < c − β²`,
`a = √(c − t)`, `L2 = L²((0,∞); ℂ)`, Dirichlet and Robin Green operators `K_D(a) = KDop`,
`K_R(a) = KRop` (#605), self-adjoint, positive and injective (#606, #607).  The merged module
`RobinDirichletRealisation20261125` (#611) builds `H_D = t + K_D(a)⁻¹`, `H_R = t + K_R(a)⁻¹` at **one**
level `t` and lists as not claimed "independence of `H_D`, `H_R` from the auxiliary level `t`".  This
file proves that independence, so that Proposition 14.2 becomes a statement on one fixed pair of
self-adjoint operators at every level `t < c − β²`:

* Part A (abstract): if `K₁ − K₂ = (t₁ − t₂) K₂ K₁ = (t₁ − t₂) K₁ K₂`, then the graphs
  `{(K₁ f, f + t₁ K₁ f)}` and `{(K₂ g, g + t₂ K₂ g)}` coincide, hence `t₁ + K₁⁻¹ = t₂ + K₂⁻¹` as
  Mathlib `LinearPMap`s (`realisation_eq_of_resolvent_identity`).
* Part B: the uniform bound `‖G_D(z,·)‖_{L²(0,∞)} ≤ C_a` for `z ≥ 0`, hence `|(K_D f)(z)| ≤ C_a ‖f‖` and
  `|(K_R f)(z)| ≤ (C_a + (a−β)⁻¹ ‖v_a‖) ‖f‖` for every `f ∈ L²(0,∞)` and every `z ≥ 0`.
* Part C: for continuous real `g` with `g ∈ L²(0,∞)` and `a, b > 0`, the classical solution
  `u_b = ∫₀^∞ G_D^{(b)}(·,w) g(w) dw` of `−u'' + b² u = g`, `u(0) = 0` is bounded and solves
  `−u'' + a² u = g + (a² − b²) u_b`; by the uniqueness of bounded classical solutions (#603, not
  re-proved) it equals `∫₀^∞ G_D^{(a)}(·,w) (g + (a² − b²) u_b)(w) dw` on `[0,∞)`; the same for the
  Robin kernels (`β < a`, `β < b`).
* Part D: continuous functions are dense in `L²(0,∞)` (Mathlib, the half-line Lebesgue measure is
  weakly regular), so the identity of Part C extends to the operator identities
  `K_D(b) = K_D(a) + (a² − b²) K_D(a) K_D(b)` and `K_R(b) = K_R(a) + (a² − b²) K_R(a) K_R(b)` on all of
  `L²(0,∞)`: the first resolvent identity `K(a) − K(b) = (b² − a²) K(a) K(b)`, and `K(a)`, `K(b)`
  commute.
* Part E: `HD_eq_of_level`, `HR_eq_of_level`: for `a, b > 0` (and `β < a`, `β < b` for Robin) and
  `t + a² = s + b²`, `t + K_D(a)⁻¹ = s + K_D(b)⁻¹` and `t + K_R(a)⁻¹ = s + K_R(b)⁻¹`.
* Manuscript form `prop14_2_level_independence`: fix one level `t₀ < c − β²` and put
  `H_D = HD(a₀, t₀)`, `H_R = HR(a₀, t₀)` (self-adjoint by #611).  For **every** `t < c − β²`:
  `HD(a_t, t) = H_D`, `HR(a_t, t) = H_R`; `(H_D − t)⁻¹ = K_D(a_t)` and `(H_R − t)⁻¹ = K_R(a_t)` on both
  sides; `K(a_t) − K(a₀) = (t − t₀) K(a_t) K(a₀)` for both kernels; and
  `(H_R − t)⁻¹ − (H_D − t)⁻¹ = (a_t − β)⁻¹ |v_{a_t}⟩⟨v_{a_t}|` (#603, #605).

Published results cited, not re-proved: the density of continuous functions in `L²` of a weakly
regular measure (Mathlib `MemLp.exists_boundedContinuous_eLpNorm_sub_le`), Hölder's inequality
(Mathlib `MemLp.integrable_mul`).

Not claimed: that `H_D`, `H_R` coincide with the realisations of `−d²/dz² + c` on the Sobolev domains
`{u ∈ H²(0,∞) : u(0) = 0}` and `{u ∈ H²(0,∞) : u'(0) = −β u(0)}`; essential self-adjointness on the
cores of #610; the spectrum or essential spectrum of `H_D`, `H_R`; Schatten-ideal membership; any
Maxwell or geometric identification; the correspondence with the printed statement of
Proposition 14.2 of `16.tex` (source not in the repository).
-/

namespace Manuscript16.RobinDirichletLevelIndependence

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal ComplexInnerProductSpace
open Manuscript16.RobinDirichletRankOne Manuscript16.RobinDirichletL2Bounded
  Manuscript16.RobinDirichletPositive Manuscript16.RobinDirichletInjective
  Manuscript16.RobinDirichletRealisation

noncomputable section

/-! ### Part A: the first resolvent identity makes `t + K⁻¹` independent of `t` -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- If `K₁ − K₂ = (t₁ − t₂) K₂ K₁ = (t₁ − t₂) K₁ K₂`, the graphs of `t₁ + K₁⁻¹` and `t₂ + K₂⁻¹`
coincide. -/
theorem graphSub_eq_of_resolvent_identity {K₁ K₂ : E →L[ℂ] E} {t₁ t₂ : ℝ}
    (h₁ : K₁ - K₂ = ((t₁ - t₂ : ℝ) : ℂ) • (K₂ ∘L K₁))
    (h₂ : K₁ - K₂ = ((t₁ - t₂ : ℝ) : ℂ) • (K₁ ∘L K₂)) :
    graphSub K₁ t₁ = graphSub K₂ t₂ := by
  have e₁ : ∀ f, K₂ f + ((t₁ - t₂ : ℝ) : ℂ) • K₂ (K₁ f) = K₁ f := fun f => by
    have h := congrArg (fun T : E →L[ℂ] E => T f) h₁
    simp only [_root_.sub_apply, _root_.smul_apply,
      ContinuousLinearMap.comp_apply] at h
    rw [← h]
    abel
  have e₂ : ∀ g, K₁ g - ((t₁ - t₂ : ℝ) : ℂ) • K₁ (K₂ g) = K₂ g := fun g => by
    have h := congrArg (fun T : E →L[ℂ] E => T g) h₂
    simp only [_root_.sub_apply, _root_.smul_apply,
      ContinuousLinearMap.comp_apply] at h
    rw [← h]
    abel
  ext x
  rw [mem_graphSub, mem_graphSub]
  constructor
  · rintro ⟨f, hf1, hf2⟩
    have hK : K₂ (f + ((t₁ - t₂ : ℝ) : ℂ) • K₁ f) = K₁ f := by
      rw [map_add, map_smul, e₁]
    refine ⟨f + ((t₁ - t₂ : ℝ) : ℂ) • K₁ f, hK.trans hf1, ?_⟩
    rw [hK, ← hf2]
    push_cast
    module
  · rintro ⟨g, hg1, hg2⟩
    have hK : K₁ (g - ((t₁ - t₂ : ℝ) : ℂ) • K₂ g) = K₂ g := by
      rw [map_sub, map_smul, e₂]
    refine ⟨g - ((t₁ - t₂ : ℝ) : ℂ) • K₂ g, hK.trans hg1, ?_⟩
    rw [hK, ← hg2]
    push_cast
    module

/-- **`t₁ + K₁⁻¹ = t₂ + K₂⁻¹`** as `LinearPMap`s (same domain, same values) when
`K₁ − K₂ = (t₁ − t₂) K₂ K₁ = (t₁ − t₂) K₁ K₂`. -/
theorem realisation_eq_of_resolvent_identity {K₁ K₂ : E →L[ℂ] E} {t₁ t₂ : ℝ}
    (h₁ : K₁ - K₂ = ((t₁ - t₂ : ℝ) : ℂ) • (K₂ ∘L K₁))
    (h₂ : K₁ - K₂ = ((t₁ - t₂ : ℝ) : ℂ) • (K₁ ∘L K₂)) :
    realisation K₁ t₁ = realisation K₂ t₂ := by
  unfold realisation
  rw [graphSub_eq_of_resolvent_identity h₁ h₂]

/-- If `H = t + K⁻¹`, then `(H − t) K f = f` for every `f` and `K (H − t) u = u` on the domain. -/
theorem resolvent_of_eq {K : E →L[ℂ] E} {t : ℝ} (hK : Function.Injective K)
    {H : E →ₗ.[ℂ] E} (hH : realisation K t = H) :
    (∀ f : E, ∃ h : K f ∈ H.domain, H ⟨K f, h⟩ - (t : ℂ) • K f = f) ∧
    (∀ u : H.domain, K (H u - (t : ℂ) • (u : E)) = u) := by
  subst hH
  exact ⟨fun f => ⟨K_mem_domain hK f, realisation_sub_K hK f⟩, K_realisation_sub hK⟩

end Abstract

/-! ### Part B: uniform pointwise bounds for `K_D f`, `K_R f` -/

variable {a b β : ℝ}

theorem enorm_greenD_le_freeK (ha : 0 < a) {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w) :
    ‖(greenD a z w : ℂ)‖ₑ ≤ freeK a z w := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (greenD_nonneg ha hz hw), freeK]
  exact ENNReal.ofReal_le_ofReal (greenD_le ha z w)

theorem freeK_le (ha : 0 < a) (z w : ℝ) : freeK a z w ≤ ENNReal.ofReal ((2 * a)⁻¹) := by
  rw [freeK]
  apply ENNReal.ofReal_le_ofReal
  have h1 : Real.exp (-a * |z - w|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (z - w)])
  rw [div_eq_mul_inv]
  calc Real.exp (-a * |z - w|) * (2 * a)⁻¹ ≤ 1 * (2 * a)⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr (by linarith))
    _ = (2 * a)⁻¹ := one_mul _

/-- `∫₀^∞ |G_D(z,w)|² dw ≤ a⁻² (2a)⁻¹` for every `z ≥ 0`. -/
theorem lintegral_greenD_sq_le (ha : 0 < a) {z : ℝ} (hz : 0 ≤ z) :
    ∫⁻ w, ‖(greenD a z w : ℂ)‖ₑ ^ 2 ∂μ ≤
      ENNReal.ofReal ((a ^ 2)⁻¹) * ENNReal.ofReal ((2 * a)⁻¹) := by
  calc ∫⁻ w, ‖(greenD a z w : ℂ)‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ w, freeK a z w * ENNReal.ofReal ((2 * a)⁻¹) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
        have hw' : 0 ≤ w := (mem_Ioi.mp hw).le
        rw [sq]
        exact mul_le_mul' (enorm_greenD_le_freeK ha hz hw')
          ((enorm_greenD_le_freeK ha hz hw').trans (freeK_le ha z w))
    _ = (∫⁻ w, freeK a z w ∂μ) * ENNReal.ofReal ((2 * a)⁻¹) :=
        lintegral_mul_const _ (measurable_freeK a).of_uncurry_left
    _ ≤ ENNReal.ofReal ((a ^ 2)⁻¹) * ENNReal.ofReal ((2 * a)⁻¹) :=
        mul_le_mul_of_nonneg_right (row_freeK ha z) zero_le

/-- The constant `C_a = (a⁻² (2a)⁻¹)^{1/2}`. -/
def kerBound (a : ℝ) : ℝ :=
  ((ENNReal.ofReal ((a ^ 2)⁻¹) * ENNReal.ofReal ((2 * a)⁻¹)) ^ (1 / 2 : ℝ)).toReal

/-- `‖G_D(z,·)‖_{L²(0,∞)} ≤ C_a` for every `z ≥ 0`. -/
theorem norm_kD_le (ha : 0 < a) {z : ℝ} (hz : 0 ≤ z) : ‖kD ha z‖ ≤ kerBound a := by
  have hmeas : AEStronglyMeasurable (fun w => (greenD a z w : ℂ)) μ :=
    (Complex.continuous_ofReal.comp (continuous_greenD a z)).aestronglyMeasurable
  rw [kD, Lp.norm_toLp, kerBound]
  apply ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
  rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hmeas, eLpNorm']
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ENNReal.rpow_le_rpow (lintegral_greenD_sq_le ha hz) (by norm_num)

/-- `|(K_D f)(z)| ≤ C_a ‖f‖` for every `f ∈ L²(0,∞)` and every `z ≥ 0`. -/
theorem norm_KD_le (ha : 0 < a) (f : L2) {z : ℝ} (hz : 0 ≤ z) :
    ‖KD ha f z‖ ≤ kerBound a * ‖f‖ := by
  rw [KD]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_kD_le ha hz) (norm_nonneg _))

/-- `|(K_R f)(z)| ≤ (C_a + (a−β)⁻¹ ‖v_a‖) ‖f‖` for every `f ∈ L²(0,∞)` and every `z ≥ 0`. -/
theorem norm_KR_le (ha : 0 < a) (hab : β < a) (f : L2) {z : ℝ} (hz : 0 ≤ z) :
    ‖KR ha β f z‖ ≤ (kerBound a + (a - β)⁻¹ * ‖expVec ha‖) * ‖f‖ := by
  have h := KR_sub_KD ha hab f z
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  have hpos : 0 ≤ (a - β)⁻¹ := inv_nonneg.mpr (by linarith)
  have he : Real.exp (-a * z) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h1 : ‖((((a - β)⁻¹ * Real.exp (-a * z)) : ℝ) : ℂ) * ⟪expVec ha, f⟫‖ ≤
      (a - β)⁻¹ * ‖expVec ha‖ * ‖f‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hpos (Real.exp_pos _).le)]
    calc (a - β)⁻¹ * Real.exp (-a * z) * ‖⟪expVec ha, f⟫‖
        ≤ (a - β)⁻¹ * 1 * (‖expVec ha‖ * ‖f‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left he hpos) (norm_inner_le_norm _ _)
            (norm_nonneg _) (mul_nonneg hpos zero_le_one)
      _ = (a - β)⁻¹ * ‖expVec ha‖ * ‖f‖ := by ring
  calc ‖((((a - β)⁻¹ * Real.exp (-a * z)) : ℝ) : ℂ) * ⟪expVec ha, f⟫ + KD ha f z‖
      ≤ ‖((((a - β)⁻¹ * Real.exp (-a * z)) : ℝ) : ℂ) * ⟪expVec ha, f⟫‖ + ‖KD ha f z‖ :=
        norm_add_le _ _
    _ ≤ (a - β)⁻¹ * ‖expVec ha‖ * ‖f‖ + kerBound a * ‖f‖ := add_le_add h1 (norm_KD_le ha f hz)
    _ = (kerBound a + (a - β)⁻¹ * ‖expVec ha‖) * ‖f‖ := by ring

/-! ### Part C: classical solutions at two levels -/

/-- A real function whose complexification is in `L²(0,∞)` is in `L²(0,∞)`. -/
theorem memLp_real_of_complex {f : ℝ → ℝ} (hf : MemLp (fun w => (f w : ℂ)) 2 μ) :
    MemLp f 2 μ := by
  simpa using hf.re

/-- `e^{−aw} f(w)` is integrable on `(0,∞)` when `f ∈ L²(0,∞)` (Hölder). -/
theorem integrableOn_exp_mul (ha : 0 < a) {f : ℝ → ℝ} (hf : MemLp (fun w => (f w : ℂ)) 2 μ) :
    IntegrableOn (fun w => Real.exp (-a * w) * f w) (Ioi 0) :=
  (memLp_exp_real ha).integrable_mul (memLp_real_of_complex hf)

/-- The datum seen at level `a`: `g + (a² − b²) u_b`, `u_b = solD b g` (Dirichlet). -/
def shiftD (a b : ℝ) (g : ℝ → ℝ) (w : ℝ) : ℝ := g w + (a ^ 2 - b ^ 2) * solD b g w

/-- The datum seen at level `a`: `g + (a² − b²) u_b`, `u_b = solR b β g` (Robin). -/
def shiftR (a b β : ℝ) (g : ℝ → ℝ) (w : ℝ) : ℝ := g w + (a ^ 2 - b ^ 2) * solR b β g w

theorem continuous_solD (hb : 0 < b) {g : ℝ → ℝ} (hg : Continuous g) : Continuous (solD b g) :=
  continuous_iff_continuousAt.mpr fun w => (hasDerivAt_solD hb hg w).continuousAt

theorem continuous_solR (hb : 0 < b) {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (solR b β g) :=
  continuous_iff_continuousAt.mpr fun w => (hasDerivAt_solR hb hg w).continuousAt

theorem continuous_shiftD (hb : 0 < b) {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (shiftD a b g) := by
  unfold shiftD
  exact hg.add (continuous_const.mul (continuous_solD hb hg))

theorem continuous_shiftR (hb : 0 < b) {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (shiftR a b β g) := by
  unfold shiftR
  exact hg.add (continuous_const.mul (continuous_solR hb hg))

/-- `u_b = solD b g ∈ L²(0,∞)`: it is `K_D(b) g` on `[0,∞)`. -/
theorem memLp_solD (hb : 0 < b) {g : ℝ → ℝ} (hg : Continuous g)
    (hL2 : MemLp (fun w => (g w : ℂ)) 2 μ) : MemLp (fun w => (solD b g w : ℂ)) 2 μ := by
  refine (memLp_KD hb (hL2.toLp _)).ae_eq ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact KD_toLp hb hg hL2 (integrableOn_exp_mul hb hL2) (mem_Ioi.mp hz).le

/-- `u_b = solR b β g ∈ L²(0,∞)`: it is `K_R(b) g` on `[0,∞)`. -/
theorem memLp_solR (hb : 0 < b) (hbβ : β < b) {g : ℝ → ℝ} (hg : Continuous g)
    (hL2 : MemLp (fun w => (g w : ℂ)) 2 μ) : MemLp (fun w => (solR b β g w : ℂ)) 2 μ := by
  refine (memLp_KR hb hbβ (hL2.toLp _)).ae_eq ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact KR_toLp hb hbβ hg hL2 (integrableOn_exp_mul hb hL2) (mem_Ioi.mp hz).le

theorem memLp_shiftD (hb : 0 < b) {g : ℝ → ℝ} (hg : Continuous g)
    (hL2 : MemLp (fun w => (g w : ℂ)) 2 μ) :
    MemLp (fun w => (shiftD a b g w : ℂ)) 2 μ := by
  convert hL2.add ((memLp_solD hb hg hL2).const_mul ((a ^ 2 - b ^ 2 : ℝ) : ℂ)) using 1
  funext w
  simp only [shiftD, Pi.add_apply]
  push_cast
  ring

theorem memLp_shiftR (hb : 0 < b) (hbβ : β < b) {g : ℝ → ℝ} (hg : Continuous g)
    (hL2 : MemLp (fun w => (g w : ℂ)) 2 μ) :
    MemLp (fun w => (shiftR a b β g w : ℂ)) 2 μ := by
  convert hL2.add ((memLp_solR hb hbβ hg hL2).const_mul ((a ^ 2 - b ^ 2 : ℝ) : ℂ)) using 1
  funext w
  simp only [shiftR, Pi.add_apply]
  push_cast
  ring

/-- `u_b = solD b g` is bounded on `[0,∞)`. -/
theorem solD_bounded (hb : 0 < b) {g : ℝ → ℝ} (hg : Continuous g)
    (hL2 : MemLp (fun w => (g w : ℂ)) 2 μ) : ∃ M, ∀ z, 0 ≤ z → |solD b g z| ≤ M :=
  ⟨kerBound b * ‖hL2.toLp _‖, fun z hz => by
    have h := norm_KD_le hb (hL2.toLp _) hz
    rwa [KD_toLp hb hg hL2 (integrableOn_exp_mul hb hL2) hz, Complex.norm_real,
      Real.norm_eq_abs] at h⟩

/-- `u_b = solR b β g` is bounded on `[0,∞)`. -/
theorem solR_bounded (hb : 0 < b) (hbβ : β < b) {g : ℝ → ℝ} (hg : Continuous g)
    (hL2 : MemLp (fun w => (g w : ℂ)) 2 μ) : ∃ M, ∀ z, 0 ≤ z → |solR b β g z| ≤ M :=
  ⟨(kerBound b + (b - β)⁻¹ * ‖expVec hb‖) * ‖hL2.toLp _‖, fun z hz => by
    have h := norm_KR_le hb hbβ (hL2.toLp _) hz
    rwa [KR_toLp hb hbβ hg hL2 (integrableOn_exp_mul hb hL2) hz, Complex.norm_real,
      Real.norm_eq_abs] at h⟩

/-- **Dirichlet, two levels.** The classical solution at level `b` is the classical solution at
level `a` with datum `g + (a² − b²) u_b`: `solD b g = solD a (shiftD a b g)` on `[0,∞)`. -/
theorem solD_level_shift (ha : 0 < a) (hb : 0 < b) {g : ℝ → ℝ} (hg : Continuous g)
    (hL2 : MemLp (fun w => (g w : ℂ)) 2 μ) {z : ℝ} (hz : 0 ≤ z) :
    solD b g z = solD a (shiftD a b g) z :=
  dirichlet_solution_unique ha (continuous_shiftD (a := a) hb hg) (v := solD b g) (v' := solD' b g)
    (fun z _ => (hasDerivAt_solD hb hg z).hasDerivWithinAt)
    (fun z _ => by
      convert (hasDerivAt_solD' hb hg z).hasDerivWithinAt (s := Ici 0) using 1
      simp only [shiftD]
      ring)
    (solD_bounded hb hg hL2) (solD_zero b g)
    (solD_bounded ha (continuous_shiftD (a := a) hb hg) (memLp_shiftD (a := a) hb hg hL2)) z hz

/-- **Robin, two levels.** `solR b β g = solR a β (shiftR a b β g)` on `[0,∞)` (`β < a`, `β < b`). -/
theorem solR_level_shift (ha : 0 < a) (hab : β < a) (hb : 0 < b) (hbβ : β < b) {g : ℝ → ℝ}
    (hg : Continuous g) (hL2 : MemLp (fun w => (g w : ℂ)) 2 μ) {z : ℝ} (hz : 0 ≤ z) :
    solR b β g z = solR a β (shiftR a b β g) z :=
  robin_solution_unique ha hab (continuous_shiftR (a := a) hb hg) (v := solR b β g) (v' := solR' b β g)
    (fun z _ => (hasDerivAt_solR hb hg z).hasDerivWithinAt)
    (fun z _ => by
      convert (hasDerivAt_solR' hb hg z).hasDerivWithinAt (s := Ici 0) using 1
      simp only [shiftR]
      ring)
    (solR_bounded hb hbβ hg hL2) (solR_robin hbβ g)
    (solR_bounded ha hab (continuous_shiftR (a := a) hb hg) (memLp_shiftR (a := a) hb hbβ hg hL2)) z hz

/-! ### Part D: the first resolvent identity on `L²(0,∞)` -/

/-- Operator form on continuous data: `K_D(b) g = K_D(a) g + (a² − b²) K_D(a) K_D(b) g`. -/
theorem KDop_level_shift_toLp (ha : 0 < a) (hb : 0 < b) {g : ℝ → ℝ} (hg : Continuous g)
    (hL2 : MemLp (fun w => (g w : ℂ)) 2 μ) :
    KDop hb (hL2.toLp _) = KDop ha (hL2.toLp _) +
      ((a ^ 2 - b ^ 2 : ℝ) : ℂ) • KDop ha (KDop hb (hL2.toLp _)) := by
  have hL2h := memLp_shiftD (a := a) hb hg hL2
  have hH : hL2h.toLp _ = hL2.toLp _ + ((a ^ 2 - b ^ 2 : ℝ) : ℂ) • KDop hb (hL2.toLp _) := by
    apply Lp.ext
    filter_upwards [hL2h.coeFn_toLp, Lp.coeFn_add (hL2.toLp _)
      (((a ^ 2 - b ^ 2 : ℝ) : ℂ) • KDop hb (hL2.toLp _)),
      Lp.coeFn_smul ((a ^ 2 - b ^ 2 : ℝ) : ℂ) (KDop hb (hL2.toLp _)), hL2.coeFn_toLp,
      KDop_ae_eq hb (hL2.toLp _), ae_restrict_mem measurableSet_Ioi] with z h1 h2 h3 h4 h5 hz
    rw [h1, h2, Pi.add_apply, h3, Pi.smul_apply, h4, h5,
      KD_toLp hb hg hL2 (integrableOn_exp_mul hb hL2) (mem_Ioi.mp hz).le, smul_eq_mul]
    simp only [shiftD]
    push_cast
    ring
  have hK : KDop hb (hL2.toLp _) = KDop ha (hL2h.toLp _) := by
    apply Lp.ext
    filter_upwards [KDop_ae_eq hb (hL2.toLp _), KDop_ae_eq ha (hL2h.toLp _),
      ae_restrict_mem measurableSet_Ioi] with z h1 h2 hz
    rw [h1, h2, KD_toLp hb hg hL2 (integrableOn_exp_mul hb hL2) (mem_Ioi.mp hz).le,
      KD_toLp ha (continuous_shiftD (a := a) hb hg) hL2h (integrableOn_exp_mul ha hL2h) (mem_Ioi.mp hz).le,
      solD_level_shift ha hb hg hL2 (mem_Ioi.mp hz).le]
  conv_lhs => rw [hK, hH, map_add, map_smul]

/-- Operator form on continuous data: `K_R(b) g = K_R(a) g + (a² − b²) K_R(a) K_R(b) g`. -/
theorem KRop_level_shift_toLp (ha : 0 < a) (hab : β < a) (hb : 0 < b) (hbβ : β < b)
    {g : ℝ → ℝ} (hg : Continuous g) (hL2 : MemLp (fun w => (g w : ℂ)) 2 μ) :
    KRop hb β (hL2.toLp _) = KRop ha β (hL2.toLp _) +
      ((a ^ 2 - b ^ 2 : ℝ) : ℂ) • KRop ha β (KRop hb β (hL2.toLp _)) := by
  have hL2h := memLp_shiftR (a := a) hb hbβ hg hL2
  have hH : hL2h.toLp _ = hL2.toLp _ + ((a ^ 2 - b ^ 2 : ℝ) : ℂ) • KRop hb β (hL2.toLp _) := by
    apply Lp.ext
    filter_upwards [hL2h.coeFn_toLp, Lp.coeFn_add (hL2.toLp _)
      (((a ^ 2 - b ^ 2 : ℝ) : ℂ) • KRop hb β (hL2.toLp _)),
      Lp.coeFn_smul ((a ^ 2 - b ^ 2 : ℝ) : ℂ) (KRop hb β (hL2.toLp _)), hL2.coeFn_toLp,
      KRop_ae_eq hb hbβ (hL2.toLp _), ae_restrict_mem measurableSet_Ioi] with z h1 h2 h3 h4 h5 hz
    rw [h1, h2, Pi.add_apply, h3, Pi.smul_apply, h4, h5,
      KR_toLp hb hbβ hg hL2 (integrableOn_exp_mul hb hL2) (mem_Ioi.mp hz).le, smul_eq_mul]
    simp only [shiftR]
    push_cast
    ring
  have hK : KRop hb β (hL2.toLp _) = KRop ha β (hL2h.toLp _) := by
    apply Lp.ext
    filter_upwards [KRop_ae_eq hb hbβ (hL2.toLp _), KRop_ae_eq ha hab (hL2h.toLp _),
      ae_restrict_mem measurableSet_Ioi] with z h1 h2 hz
    rw [h1, h2, KR_toLp hb hbβ hg hL2 (integrableOn_exp_mul hb hL2) (mem_Ioi.mp hz).le,
      KR_toLp ha hab (continuous_shiftR (a := a) hb hg) hL2h (integrableOn_exp_mul ha hL2h)
        (mem_Ioi.mp hz).le,
      solR_level_shift ha hab hb hbβ hg hL2 (mem_Ioi.mp hz).le]
  conv_lhs => rw [hK, hH, map_add, map_smul]

/-- A bounded operator on `L²(0,∞)` that vanishes on every continuous real function of
`L²(0,∞)` is zero (density of continuous functions, Mathlib). -/
theorem eq_zero_of_toLp_real {T : L2 →L[ℂ] L2}
    (hT : ∀ g : ℝ → ℝ, Continuous g → ∀ hL2 : MemLp (fun w => (g w : ℂ)) 2 μ,
      T (hL2.toLp _) = 0) : T = 0 := by
  -- `T` vanishes on every continuous complex function of `L²(0,∞)`
  have hC : ∀ g : ℝ → ℂ, Continuous g → ∀ hg : MemLp g 2 μ, T (hg.toLp g) = 0 := by
    intro g hgc hg
    have hre : MemLp (fun w => (((g w).re : ℝ) : ℂ)) 2 μ :=
      hg.of_le (by fun_prop : Continuous fun w => (((g w).re : ℝ) : ℂ)).aestronglyMeasurable
        (Eventually.of_forall fun w => by
          show ‖(((g w).re : ℝ) : ℂ)‖ ≤ ‖g w‖
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact Complex.abs_re_le_norm _)
    have him : MemLp (fun w => (((g w).im : ℝ) : ℂ)) 2 μ :=
      hg.of_le (by fun_prop : Continuous fun w => (((g w).im : ℝ) : ℂ)).aestronglyMeasurable
        (Eventually.of_forall fun w => by
          show ‖(((g w).im : ℝ) : ℂ)‖ ≤ ‖g w‖
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact Complex.abs_im_le_norm _)
    have hsplit : hg.toLp g = hre.toLp _ + Complex.I • him.toLp _ := by
      apply Lp.ext
      filter_upwards [hg.coeFn_toLp, Lp.coeFn_add (hre.toLp _) (Complex.I • him.toLp _),
        Lp.coeFn_smul Complex.I (him.toLp _), hre.coeFn_toLp, him.coeFn_toLp]
        with w h1 h2 h3 h4 h5
      rw [h1, h2, Pi.add_apply, h3, Pi.smul_apply, h4, h5, smul_eq_mul, mul_comm]
      exact (Complex.re_add_im (g w)).symm
    rw [hsplit, map_add, map_smul, hT (fun w => (g w).re) (by fun_prop) hre,
      hT (fun w => (g w).im) (by fun_prop) him, smul_zero, add_zero]
  -- density
  ext1 F
  rw [_root_.zero_apply, ← norm_le_zero_iff]
  have key : ∀ ε : ℝ, 0 < ε → ‖T F‖ ≤ ‖T‖ * ε := by
    intro ε hε
    obtain ⟨g, hgε, hgmem⟩ := (Lp.memLp F).exists_boundedContinuous_eLpNorm_sub_le
      (μ := μ) ENNReal.ofNat_ne_top (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε).ne'
    have hdist : ‖F - hgmem.toLp g‖ ≤ ε := by
      rw [Lp.norm_def]
      apply ENNReal.toReal_le_of_le_ofReal hε.le
      refine le_trans (le_of_eq ?_) hgε
      apply eLpNorm_congr_ae
      filter_upwards [Lp.coeFn_sub F (hgmem.toLp g), hgmem.coeFn_toLp] with w h1 h2
      simp only [h1, Pi.sub_apply, h2]
    have hTg : T (hgmem.toLp g) = 0 := hC g g.continuous hgmem
    calc ‖T F‖ = ‖T (F - hgmem.toLp g)‖ := by rw [map_sub, hTg, sub_zero]
      _ ≤ ‖T‖ * ‖F - hgmem.toLp g‖ := T.le_opNorm _
      _ ≤ ‖T‖ * ε := mul_le_mul_of_nonneg_left hdist (norm_nonneg _)
  by_contra hne'
  have hne : 0 < ‖T F‖ := not_le.mp hne'
  have hT0 : 0 ≤ ‖T‖ := norm_nonneg _
  have hε : 0 < ‖T F‖ / (2 * (‖T‖ + 1)) := div_pos hne (by positivity)
  have h := key _ hε
  have h2 : ‖T‖ * (‖T F‖ / (2 * (‖T‖ + 1))) < ‖T F‖ := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [mul_nonneg hT0 hne.le]
  linarith

/-- **`K_D(b) = K_D(a) + (a² − b²) K_D(a) K_D(b)`** on all of `L²(0,∞)`, for `a, b > 0`. -/
theorem KDop_level_shift (ha : 0 < a) (hb : 0 < b) :
    KDop hb = KDop ha + ((a ^ 2 - b ^ 2 : ℝ) : ℂ) • (KDop ha ∘L KDop hb) := by
  rw [← sub_eq_zero]
  apply eq_zero_of_toLp_real
  intro g hg hL2
  simp only [_root_.sub_apply, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.comp_apply]
  rw [sub_eq_zero]
  exact KDop_level_shift_toLp ha hb hg hL2

/-- **`K_R(b) = K_R(a) + (a² − b²) K_R(a) K_R(b)`** on all of `L²(0,∞)`, for `β < a`, `β < b`. -/
theorem KRop_level_shift (ha : 0 < a) (hab : β < a) (hb : 0 < b) (hbβ : β < b) :
    KRop hb β = KRop ha β + ((a ^ 2 - b ^ 2 : ℝ) : ℂ) • (KRop ha β ∘L KRop hb β) := by
  rw [← sub_eq_zero]
  apply eq_zero_of_toLp_real
  intro g hg hL2
  simp only [_root_.sub_apply, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.comp_apply]
  rw [sub_eq_zero]
  exact KRop_level_shift_toLp ha hab hb hbβ hg hL2

/-- **First resolvent identity, Dirichlet**: `K_D(a) − K_D(b) = (b² − a²) K_D(a) K_D(b)`. -/
theorem KDop_resolvent_identity (ha : 0 < a) (hb : 0 < b) :
    KDop ha - KDop hb = ((b ^ 2 - a ^ 2 : ℝ) : ℂ) • (KDop ha ∘L KDop hb) := by
  have h := KDop_level_shift ha hb
  conv_lhs => rw [h]
  rw [sub_add_cancel_left]
  push_cast
  module

/-- **First resolvent identity, Robin**: `K_R(a) − K_R(b) = (b² − a²) K_R(a) K_R(b)`. -/
theorem KRop_resolvent_identity (ha : 0 < a) (hab : β < a) (hb : 0 < b) (hbβ : β < b) :
    KRop ha β - KRop hb β = ((b ^ 2 - a ^ 2 : ℝ) : ℂ) • (KRop ha β ∘L KRop hb β) := by
  have h := KRop_level_shift ha hab hb hbβ
  conv_lhs => rw [h]
  rw [sub_add_cancel_left]
  push_cast
  module

/-- The Green operators at two levels commute (Dirichlet). -/
theorem KDop_comm (ha : 0 < a) (hb : 0 < b) : KDop ha ∘L KDop hb = KDop hb ∘L KDop ha := by
  rcases eq_or_ne (a ^ 2) (b ^ 2) with hab | hab
  · have hab' : a = b := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
    subst hab'
    rfl
  · have h1 := KDop_resolvent_identity ha hb
    have h2 := KDop_resolvent_identity hb ha
    have hc : ((b ^ 2 - a ^ 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero, sub_ne_zero]
      exact Ne.symm hab
    have h3 : ((b ^ 2 - a ^ 2 : ℝ) : ℂ) • (KDop ha ∘L KDop hb) =
        ((b ^ 2 - a ^ 2 : ℝ) : ℂ) • (KDop hb ∘L KDop ha) := by
      have h2' : ((b ^ 2 - a ^ 2 : ℝ) : ℂ) • (KDop hb ∘L KDop ha) = -(KDop hb - KDop ha) := by
        rw [h2]
        push_cast
        module
      rw [← h1, h2', neg_sub]
    exact smul_right_injective _ hc h3

/-- The Green operators at two levels commute (Robin). -/
theorem KRop_comm (ha : 0 < a) (hab : β < a) (hb : 0 < b) (hbβ : β < b) :
    KRop ha β ∘L KRop hb β = KRop hb β ∘L KRop ha β := by
  rcases eq_or_ne (a ^ 2) (b ^ 2) with hab2 | hab2
  · have hab' : a = b := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
    subst hab'
    rfl
  · have h1 := KRop_resolvent_identity ha hab hb hbβ
    have h2 := KRop_resolvent_identity hb hbβ ha hab
    have hc : ((b ^ 2 - a ^ 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero, sub_ne_zero]
      exact Ne.symm hab2
    have h3 : ((b ^ 2 - a ^ 2 : ℝ) : ℂ) • (KRop ha β ∘L KRop hb β) =
        ((b ^ 2 - a ^ 2 : ℝ) : ℂ) • (KRop hb β ∘L KRop ha β) := by
      have h2' : ((b ^ 2 - a ^ 2 : ℝ) : ℂ) • (KRop hb β ∘L KRop ha β) =
          -(KRop hb β - KRop ha β) := by
        rw [h2]
        push_cast
        module
      rw [← h1, h2', neg_sub]
    exact smul_right_injective _ hc h3

/-! ### Part E: independence of the level -/

/-- **`t + K_D(a)⁻¹ = s + K_D(b)⁻¹`** whenever `a, b > 0` and `t + a² = s + b²`. -/
theorem HD_eq_of_level (ha : 0 < a) (hb : 0 < b) {t s : ℝ} (hts : t + a ^ 2 = s + b ^ 2) :
    HD ha t = HD hb s := by
  have hc : (b ^ 2 - a ^ 2 : ℝ) = t - s := by linarith
  unfold HD
  apply realisation_eq_of_resolvent_identity
  · have h := KDop_level_shift hb ha
    conv_lhs => rw [h]
    rw [add_sub_cancel_left, hc]
  · rw [KDop_resolvent_identity ha hb, hc]

/-- **`t + K_R(a)⁻¹ = s + K_R(b)⁻¹`** whenever `β < a`, `β < b`, `a, b > 0` and `t + a² = s + b²`. -/
theorem HR_eq_of_level (ha : 0 < a) (hab : β < a) (hb : 0 < b) (hbβ : β < b) {t s : ℝ}
    (hts : t + a ^ 2 = s + b ^ 2) : HR ha β t = HR hb β s := by
  have hc : (b ^ 2 - a ^ 2 : ℝ) = t - s := by linarith
  unfold HR
  apply realisation_eq_of_resolvent_identity
  · have h := KRop_level_shift hb hbβ ha hab
    conv_lhs => rw [h]
    rw [add_sub_cancel_left, hc]
  · rw [KRop_resolvent_identity ha hab hb hbβ, hc]

/-! ### Manuscript form -/

theorem level_sum {c t : ℝ} (ht : t < c - β ^ 2) : t + aOf c t ^ 2 = c := by
  rw [aOf_sq ht]
  ring

/-- **Proposition 14.2 (§14.2) on one fixed pair of operators.**  With `c = ‖κ‖²`, `β > 0`, a fixed
level `t₀ < c − β²`, `a₀ = √(c − t₀)` and `H_D = t₀ + K_D(a₀)⁻¹`, `H_R = t₀ + K_R(a₀)⁻¹` (self-adjoint,
#611): for **every** level `t < c − β²`, with `a = √(c − t)`,
`t + K_D(a)⁻¹ = H_D` and `t + K_R(a)⁻¹ = H_R`; `(H_D − t)⁻¹ = K_D(a)` and `(H_R − t)⁻¹ = K_R(a)` on both
sides; `K(a) − K(a₀) = (t − t₀) K(a) K(a₀)` for both kernels; and
`(H_R − t)⁻¹ − (H_D − t)⁻¹ = K_R(a) − K_D(a) = (a − β)⁻¹ |v_a⟩⟨v_a|`. -/
theorem prop14_2_level_independence {κ : EuclideanSpace ℝ (Fin 2)} (hβ : 0 < β) {t₀ : ℝ}
    (ht₀ : t₀ < ‖κ‖ ^ 2 - β ^ 2) :
    IsSelfAdjoint (HD (aOf_pos hβ ht₀) t₀) ∧ IsSelfAdjoint (HR (aOf_pos hβ ht₀) β t₀) ∧
    ∀ (t : ℝ) (ht : t < ‖κ‖ ^ 2 - β ^ 2),
      HD (aOf_pos hβ ht) t = HD (aOf_pos hβ ht₀) t₀ ∧
      HR (aOf_pos hβ ht) β t = HR (aOf_pos hβ ht₀) β t₀ ∧
      (∀ f : L2, ∃ h : KDop (aOf_pos hβ ht) f ∈ (HD (aOf_pos hβ ht₀) t₀).domain,
        HD (aOf_pos hβ ht₀) t₀ ⟨KDop (aOf_pos hβ ht) f, h⟩ - (t : ℂ) • KDop (aOf_pos hβ ht) f = f) ∧
      (∀ u : (HD (aOf_pos hβ ht₀) t₀).domain,
        KDop (aOf_pos hβ ht) (HD (aOf_pos hβ ht₀) t₀ u - (t : ℂ) • (u : L2)) = u) ∧
      (∀ f : L2, ∃ h : KRop (aOf_pos hβ ht) β f ∈ (HR (aOf_pos hβ ht₀) β t₀).domain,
        HR (aOf_pos hβ ht₀) β t₀ ⟨KRop (aOf_pos hβ ht) β f, h⟩ -
          (t : ℂ) • KRop (aOf_pos hβ ht) β f = f) ∧
      (∀ u : (HR (aOf_pos hβ ht₀) β t₀).domain,
        KRop (aOf_pos hβ ht) β (HR (aOf_pos hβ ht₀) β t₀ u - (t : ℂ) • (u : L2)) = u) ∧
      KDop (aOf_pos hβ ht) - KDop (aOf_pos hβ ht₀) =
        ((t - t₀ : ℝ) : ℂ) • (KDop (aOf_pos hβ ht) ∘L KDop (aOf_pos hβ ht₀)) ∧
      KRop (aOf_pos hβ ht) β - KRop (aOf_pos hβ ht₀) β =
        ((t - t₀ : ℝ) : ℂ) • (KRop (aOf_pos hβ ht) β ∘L KRop (aOf_pos hβ ht₀) β) ∧
      KRop (aOf_pos hβ ht) β - KDop (aOf_pos hβ ht) = robinDiff (aOf_pos hβ ht) β := by
  have ha₀ := aOf_pos hβ ht₀
  have hab₀ := lt_aOf hβ ht₀
  refine ⟨HD_isSelfAdjoint ha₀ t₀, HR_isSelfAdjoint ha₀ hab₀ t₀, fun t ht => ?_⟩
  have ha := aOf_pos hβ ht
  have hab := lt_aOf hβ ht
  have hlev : t + aOf (‖κ‖ ^ 2) t ^ 2 = t₀ + aOf (‖κ‖ ^ 2) t₀ ^ 2 := by
    rw [level_sum ht, level_sum ht₀]
  have hc : (aOf (‖κ‖ ^ 2) t₀ ^ 2 - aOf (‖κ‖ ^ 2) t ^ 2 : ℝ) = t - t₀ := by linarith
  have hD := HD_eq_of_level ha ha₀ hlev
  have hR := HR_eq_of_level ha hab ha₀ hab₀ hlev
  have rD := resolvent_of_eq (t := t) (KDop_injective ha) hD
  have rR := resolvent_of_eq (t := t) (KRop_injective ha hab) hR
  refine ⟨hD, hR, rD.1, rD.2, rR.1, rR.2, ?_, ?_, KRop_sub_KDop ha β⟩
  · rw [KDop_resolvent_identity ha ha₀, hc]
  · rw [KRop_resolvent_identity ha hab ha₀ hab₀, hc]

end

end Manuscript16.RobinDirichletLevelIndependence

#print axioms Manuscript16.RobinDirichletLevelIndependence.graphSub_eq_of_resolvent_identity
#print axioms Manuscript16.RobinDirichletLevelIndependence.realisation_eq_of_resolvent_identity
#print axioms Manuscript16.RobinDirichletLevelIndependence.resolvent_of_eq
#print axioms Manuscript16.RobinDirichletLevelIndependence.enorm_greenD_le_freeK
#print axioms Manuscript16.RobinDirichletLevelIndependence.freeK_le
#print axioms Manuscript16.RobinDirichletLevelIndependence.lintegral_greenD_sq_le
#print axioms Manuscript16.RobinDirichletLevelIndependence.kerBound
#print axioms Manuscript16.RobinDirichletLevelIndependence.norm_kD_le
#print axioms Manuscript16.RobinDirichletLevelIndependence.norm_KD_le
#print axioms Manuscript16.RobinDirichletLevelIndependence.norm_KR_le
#print axioms Manuscript16.RobinDirichletLevelIndependence.memLp_real_of_complex
#print axioms Manuscript16.RobinDirichletLevelIndependence.integrableOn_exp_mul
#print axioms Manuscript16.RobinDirichletLevelIndependence.shiftD
#print axioms Manuscript16.RobinDirichletLevelIndependence.shiftR
#print axioms Manuscript16.RobinDirichletLevelIndependence.continuous_solD
#print axioms Manuscript16.RobinDirichletLevelIndependence.continuous_solR
#print axioms Manuscript16.RobinDirichletLevelIndependence.continuous_shiftD
#print axioms Manuscript16.RobinDirichletLevelIndependence.continuous_shiftR
#print axioms Manuscript16.RobinDirichletLevelIndependence.memLp_solD
#print axioms Manuscript16.RobinDirichletLevelIndependence.memLp_solR
#print axioms Manuscript16.RobinDirichletLevelIndependence.memLp_shiftD
#print axioms Manuscript16.RobinDirichletLevelIndependence.memLp_shiftR
#print axioms Manuscript16.RobinDirichletLevelIndependence.solD_bounded
#print axioms Manuscript16.RobinDirichletLevelIndependence.solR_bounded
#print axioms Manuscript16.RobinDirichletLevelIndependence.solD_level_shift
#print axioms Manuscript16.RobinDirichletLevelIndependence.solR_level_shift
#print axioms Manuscript16.RobinDirichletLevelIndependence.KDop_level_shift_toLp
#print axioms Manuscript16.RobinDirichletLevelIndependence.KRop_level_shift_toLp
#print axioms Manuscript16.RobinDirichletLevelIndependence.eq_zero_of_toLp_real
#print axioms Manuscript16.RobinDirichletLevelIndependence.KDop_level_shift
#print axioms Manuscript16.RobinDirichletLevelIndependence.KRop_level_shift
#print axioms Manuscript16.RobinDirichletLevelIndependence.KDop_resolvent_identity
#print axioms Manuscript16.RobinDirichletLevelIndependence.KRop_resolvent_identity
#print axioms Manuscript16.RobinDirichletLevelIndependence.KDop_comm
#print axioms Manuscript16.RobinDirichletLevelIndependence.KRop_comm
#print axioms Manuscript16.RobinDirichletLevelIndependence.HD_eq_of_level
#print axioms Manuscript16.RobinDirichletLevelIndependence.HR_eq_of_level
#print axioms Manuscript16.RobinDirichletLevelIndependence.level_sum
#print axioms Manuscript16.RobinDirichletLevelIndependence.prop14_2_level_independence
