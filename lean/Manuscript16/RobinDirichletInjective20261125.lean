import Mathlib
import Manuscript16.RobinDirichletPositive20261125

/-!
# M16 v16.5 §14.2, Proposition 14.2: the Dirichlet and Robin Green operators are injective

`Manuscript16.RobinDirichletPositive20261125` (PR #606) factors the Dirichlet Green operator of
Proposition 14.2 as `K_D = W† W` on `L² = L²((0,∞); ℂ)`, with
`(W f)(s) = ∫₀^∞ ψ(w,s) f(w) dw`, `ψ(w,s) = 1_{s ≤ w} e^{−a(w−s)}`, and proves that `K_D` and
`K_R = K_D + P_a` are positive and self-adjoint; it lists injectivity and strict positivity as not
claimed.  A resolvent `(H − t)⁻¹` of a self-adjoint operator is injective with dense range, so
these are necessary properties of the printed Green operators.  This file proves them.

* Part A (tail integral): with `g_f(w) = e^{−aw} f(w)` (integrable on `(0,∞)`) and
  `G_f(s) = ∫_{(s,∞)} g_f`, one has `(W f)(s) = e^{as} G_f(s)` for every `s` (`Wfun_eq_tail`),
  and `G_f` is continuous (`continuous_tail`, dominated convergence).
* Part B (injectivity of `W`): if `W f = 0` then `G_f = 0` almost everywhere on `(0,∞)`, hence
  everywhere (continuity); so `∫_S g_f = 0` on the π-system `{(s,∞)}` generating the Borel sets,
  hence on every Borel set (Dynkin), hence `g_f = 0` and `f = 0` almost everywhere
  (`Wop_injective`).
* Part C (consequences): `K_D` is injective and strictly positive, `Re ⟪f, K_D f⟫ = ‖W f‖² > 0`
  for `f ≠ 0`; `K_R = K_D + P_a` is injective and strictly positive for `β < a`; both have dense
  range (`(range T)ᗮ = ker T† = ker T = 0`); manuscript form `prop14_2_injective`.

Not claimed: the self-adjoint realisations `H_D`, `H_R` on `H²(0,∞)` and the identification
`KDop = (H_D − t)⁻¹`, `KRop = (H_R − t)⁻¹`; any coercivity bound `Re ⟪f, K f⟫ ≥ c ‖f‖²`;
surjectivity or non-surjectivity; Schatten-ideal membership; the essential spectrum; any Maxwell
or geometric identification.
-/

namespace Manuscript16.RobinDirichletInjective

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal ComplexInnerProductSpace
open Manuscript16.RobinDirichletRankOne Manuscript16.RobinDirichletL2Bounded
  Manuscript16.RobinDirichletPositive

noncomputable section

variable {a β : ℝ}

/-! ### Part A: the weighted function and its tail integral -/

/-- `g_f(w) = e^{−aw} f(w)`. -/
def weighted (a : ℝ) (f : L2) (w : ℝ) : ℂ := ((Real.exp (-a * w) : ℝ) : ℂ) * f w

/-- `g_f` is integrable on `(0,∞)` (Cauchy–Schwarz). -/
theorem integrable_weighted (ha : 0 < a) (f : L2) : Integrable (weighted a f) μ := by
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) ((memLp_exp ha).toLp _) f).congr ?_
  filter_upwards [(memLp_exp ha).coeFn_toLp] with w hw
  rw [hw, weighted, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]

/-- The tail integral `G_f(s) = ∫_{(s,∞)} e^{−aw} f(w) dw` on `(0,∞)`. -/
def tail (a : ℝ) (f : L2) (s : ℝ) : ℂ := ∫ w in Ioi s, weighted a f w ∂μ

/-- `(W f)(s) = e^{as} G_f(s)` for every real `s`. -/
theorem Wfun_eq_tail (ha : 0 < a) (f : L2) (s : ℝ) :
    Wfun ha f s = ((Real.exp (a * s) : ℝ) : ℂ) * tail a f s := by
  rw [Wfun_eq_integral, tail, setIntegral_congr_set (Ioi_ae_eq_Ici (μ := μ)),
    ← integral_const_mul, ← integral_indicator measurableSet_Ici]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  by_cases h : s ≤ w
  · have hw : w ∈ Ici s := h
    simp only [psi, h, ↓reduceIte, indicator_of_mem hw, weighted]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    have he : -a * (w - s) = a * s + -a * w := by ring
    rw [he]
  · have hw : w ∉ Ici s := h
    simp only [psi, h, ↓reduceIte, indicator_of_notMem hw, Complex.ofReal_zero, zero_mul]

/-- `G_f` is continuous (dominated convergence; `μ` has no atoms). -/
theorem continuous_tail (ha : 0 < a) (f : L2) : Continuous (tail a f) := by
  have hg := integrable_weighted ha f
  have key : tail a f = fun s => ∫ w, (Ioi s).indicator (weighted a f) w ∂μ :=
    funext fun s => (integral_indicator measurableSet_Ioi).symm
  rw [key, continuous_iff_continuousAt]
  intro s₀
  refine continuousAt_of_dominated (bound := fun w => ‖weighted a f w‖) ?_ ?_ hg.norm ?_
  · exact Eventually.of_forall fun s => (hg.indicator measurableSet_Ioi).aestronglyMeasurable
  · exact Eventually.of_forall fun s =>
      Eventually.of_forall fun w => norm_indicator_le_norm_self _ _
  · have hne : ∀ᵐ w ∂μ, w ≠ s₀ := by
      rw [ae_iff]
      simp
    filter_upwards [hne] with w hw
    rcases hw.lt_or_gt with h | h
    · have hev : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝 s₀]
          fun s => (Ioi s).indicator (weighted a f) w := by
        filter_upwards [Ioi_mem_nhds h] with s hs
        exact (indicator_of_notMem
          (fun hws : w ∈ Ioi s => lt_asymm (mem_Ioi.mp hws) (mem_Ioi.mp hs)) _).symm
      exact continuousAt_const.congr hev
    · have hev : (fun _ : ℝ => weighted a f w) =ᶠ[𝓝 s₀]
          fun s => (Ioi s).indicator (weighted a f) w := by
        filter_upwards [Iio_mem_nhds h] with s hs
        exact (indicator_of_mem (show w ∈ Ioi s from hs) _).symm
      exact continuousAt_const.congr hev

/-- For `s ≤ 0`, `G_f(s) = ∫₀^∞ g_f`. -/
theorem tail_of_nonpos (f : L2) {s : ℝ} (hs : s ≤ 0) : tail a f s = ∫ w, weighted a f w ∂μ := by
  rw [tail, Measure.restrict_eq_self_of_ae_mem]
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with w hw
  exact lt_of_le_of_lt hs hw

/-! ### Part B: injectivity of `W` -/

/-- If `W f = 0`, then `G_f(s) = 0` for every real `s`. -/
theorem tail_eq_zero_of_Wop (ha : 0 < a) {f : L2} (hf : Wop ha f = 0) (s : ℝ) :
    tail a f s = 0 := by
  have hW := Wop_ae_eq ha f
  rw [hf] at hW
  have h1 : tail a f =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun _ => (0 : ℂ) := by
    filter_upwards [hW, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with s hs h0
    have hWs : Wfun ha f s = 0 := by rw [← hs, h0]; rfl
    rw [Wfun_eq_tail] at hWs
    exact (mul_eq_zero.mp hWs).resolve_left (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
  have hpos : EqOn (tail a f) (fun _ => (0 : ℂ)) (Ioi 0) :=
    Measure.eqOn_open_of_ae_eq h1 isOpen_Ioi (continuous_tail ha f).continuousOn
      continuousOn_const
  have hclosed : IsClosed {s : ℝ | tail a f s = 0} :=
    isClosed_eq (continuous_tail ha f) continuous_const
  have hIci : Ici (0 : ℝ) ⊆ {s : ℝ | tail a f s = 0} := by
    rw [← closure_Ioi]
    exact hclosed.closure_subset_iff.mpr fun s hs => hpos hs
  rcases le_or_gt s 0 with hs | hs
  · rw [tail_of_nonpos f hs, ← tail_of_nonpos f le_rfl]
    exact hIci (mem_Ici.mpr le_rfl)
  · exact hpos hs

/-- If `W f = 0`, then `∫_S g_f = 0` on every Borel set `S`. -/
theorem setIntegral_weighted_eq_zero (ha : 0 < a) {f : L2} (hf : Wop ha f = 0) :
    ∀ S, MeasurableSet S → ∫ w in S, weighted a f w ∂μ = 0 := by
  have hg := integrable_weighted ha f
  have htot : ∫ w, weighted a f w ∂μ = 0 := by
    rw [← tail_of_nonpos f le_rfl]
    exact tail_eq_zero_of_Wop ha hf 0
  have h_eq : (inferInstance : MeasurableSpace ℝ) = MeasurableSpace.generateFrom (range Ioi) :=
    BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioi ℝ)
  intro S hS
  induction S, hS using MeasurableSpace.induction_on_inter h_eq isPiSystem_Ioi with
  | empty => simp
  | basic t ht =>
    obtain ⟨s, rfl⟩ := ht
    exact tail_eq_zero_of_Wop ha hf s
  | compl t htm iht => rw [setIntegral_compl htm hg, htot, iht, sub_zero]
  | iUnion F hd hm ihF =>
    rw [integral_iUnion hm hd hg.integrableOn]
    simp [ihF]

/-- If `W f = 0`, then `f = 0`. -/
theorem eq_zero_of_Wop (ha : 0 < a) {f : L2} (hf : Wop ha f = 0) : f = 0 := by
  have hg0 : weighted a f =ᵐ[μ] 0 :=
    (integrable_weighted ha f).ae_eq_zero_of_forall_setIntegral_eq_zero
      fun S hS _ => setIntegral_weighted_eq_zero ha hf S hS
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hg0] with w hw
  have hw' : ((Real.exp (-a * w) : ℝ) : ℂ) * f w = 0 := hw
  exact (mul_eq_zero.mp hw').resolve_left (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')

/-- **`W` is injective** on `L²(0,∞)`. -/
theorem Wop_injective (ha : 0 < a) : Function.Injective (Wop ha) :=
  (injective_iff_map_eq_zero (Wop ha)).mpr fun _ hf => eq_zero_of_Wop ha hf

/-! ### Part C: injectivity, strict positivity and dense range of `K_D`, `K_R` -/

/-- `Re ⟪f, K_D f⟫ = ‖W f‖² > 0` for `f ≠ 0`. -/
theorem re_inner_KDop_pos (ha : 0 < a) {f : L2} (hf : f ≠ 0) :
    0 < (⟪f, KDop ha f⟫).re := by
  rw [inner_KDop_self, Complex.ofReal_re]
  have hW : Wop ha f ≠ 0 := fun h => hf (eq_zero_of_Wop ha h)
  exact pow_pos (norm_pos_iff.mpr hW) 2

/-- `Re ⟪f, K_R f⟫ ≥ ‖W f‖² > 0` for `f ≠ 0` and `β < a`. -/
theorem re_inner_KRop_pos (ha : 0 < a) (hab : β < a) {f : L2} (hf : f ≠ 0) :
    0 < (⟪f, KRop ha β f⟫).re := by
  have hP : 0 ≤ RCLike.re ⟪f, robinDiff ha β f⟫ :=
    (robinDiff_isPositive ha hab).re_inner_nonneg_right f
  change 0 < (⟪f, KDop ha f + robinDiff ha β f⟫).re
  rw [inner_add_right, Complex.add_re]
  exact add_pos_of_pos_of_nonneg (re_inner_KDop_pos ha hf) hP

/-- A bounded operator with `Re ⟪f, T f⟫ > 0` for every `f ≠ 0` is injective. -/
theorem injective_of_re_inner_pos {T : L2 →L[ℂ] L2}
    (hT : ∀ f : L2, f ≠ 0 → 0 < (⟪f, T f⟫).re) : Function.Injective T := by
  refine (injective_iff_map_eq_zero T).mpr fun f hf => ?_
  by_contra hne
  have h := hT f hne
  rw [hf, inner_zero_right, Complex.zero_re] at h
  exact lt_irrefl 0 h

/-- `K_D` is injective on `L²(0,∞)`. -/
theorem KDop_injective (ha : 0 < a) : Function.Injective (KDop ha) :=
  injective_of_re_inner_pos fun _ hf => re_inner_KDop_pos ha hf

/-- `K_R` is injective on `L²(0,∞)` for `β < a`. -/
theorem KRop_injective (ha : 0 < a) (hab : β < a) : Function.Injective (KRop ha β) :=
  injective_of_re_inner_pos fun _ hf => re_inner_KRop_pos ha hab hf

/-- A self-adjoint injective bounded operator on `L²(0,∞)` has dense range. -/
theorem denseRange_of_isSelfAdjoint {T : L2 →L[ℂ] L2} (hT : IsSelfAdjoint T)
    (hinj : Function.Injective T) : DenseRange T := by
  have h1 : T.rangeᗮ = ⊥ := by
    rw [ContinuousLinearMap.orthogonal_range, hT.adjoint_eq]
    exact LinearMap.ker_eq_bot.mpr hinj
  have h2 : T.range.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.mpr h1
  have h3 := (Submodule.dense_iff_topologicalClosure_eq_top).mpr h2
  rwa [LinearMap.coe_range] at h3

/-- `K_D` has dense range in `L²(0,∞)`. -/
theorem denseRange_KDop (ha : 0 < a) : DenseRange (KDop ha) :=
  denseRange_of_isSelfAdjoint (KDop_isSelfAdjoint ha) (KDop_injective ha)

/-- `K_R` has dense range in `L²(0,∞)` for `β < a`. -/
theorem denseRange_KRop (ha : 0 < a) (hab : β < a) : DenseRange (KRop ha β) :=
  denseRange_of_isSelfAdjoint (KRop_isSelfAdjoint ha hab) (KRop_injective ha hab)

/-! ### Manuscript form -/

/-- Proposition 14.2 (§14.2), injectivity: with `c = ‖κ‖²`, `β > 0`, `t < c − β²` and
`a = √(c − t)`, the Volterra operator `W`, the Dirichlet Green operator `K_D = W† W` and the Robin
Green operator `K_R = K_D + P_a` are injective on `L²(0,∞)`; `K_D` and `K_R` are strictly positive
(`Re ⟪f, K f⟫ > 0` for `f ≠ 0`) and have dense range. -/
theorem prop14_2_injective {κ : EuclideanSpace ℝ (Fin 2)} {t : ℝ} (hβ : 0 < β)
    (ht : t < ‖κ‖ ^ 2 - β ^ 2) :
    Function.Injective (Wop (aOf_pos hβ ht)) ∧
    Function.Injective (KDop (aOf_pos hβ ht)) ∧
    Function.Injective (KRop (aOf_pos hβ ht) β) ∧
    (∀ f : L2, f ≠ 0 → 0 < (⟪f, KDop (aOf_pos hβ ht) f⟫).re) ∧
    (∀ f : L2, f ≠ 0 → 0 < (⟪f, KRop (aOf_pos hβ ht) β f⟫).re) ∧
    DenseRange (KDop (aOf_pos hβ ht)) ∧
    DenseRange (KRop (aOf_pos hβ ht) β) := by
  have hab := lt_aOf hβ ht
  exact ⟨Wop_injective _, KDop_injective _, KRop_injective _ hab,
    fun _ hf => re_inner_KDop_pos _ hf, fun _ hf => re_inner_KRop_pos _ hab hf,
    denseRange_KDop _, denseRange_KRop _ hab⟩

end

end Manuscript16.RobinDirichletInjective

#print axioms Manuscript16.RobinDirichletInjective.integrable_weighted
#print axioms Manuscript16.RobinDirichletInjective.Wfun_eq_tail
#print axioms Manuscript16.RobinDirichletInjective.continuous_tail
#print axioms Manuscript16.RobinDirichletInjective.tail_of_nonpos
#print axioms Manuscript16.RobinDirichletInjective.tail_eq_zero_of_Wop
#print axioms Manuscript16.RobinDirichletInjective.setIntegral_weighted_eq_zero
#print axioms Manuscript16.RobinDirichletInjective.eq_zero_of_Wop
#print axioms Manuscript16.RobinDirichletInjective.Wop_injective
#print axioms Manuscript16.RobinDirichletInjective.re_inner_KDop_pos
#print axioms Manuscript16.RobinDirichletInjective.re_inner_KRop_pos
#print axioms Manuscript16.RobinDirichletInjective.injective_of_re_inner_pos
#print axioms Manuscript16.RobinDirichletInjective.KDop_injective
#print axioms Manuscript16.RobinDirichletInjective.KRop_injective
#print axioms Manuscript16.RobinDirichletInjective.denseRange_of_isSelfAdjoint
#print axioms Manuscript16.RobinDirichletInjective.denseRange_KDop
#print axioms Manuscript16.RobinDirichletInjective.denseRange_KRop
#print axioms Manuscript16.RobinDirichletInjective.prop14_2_injective
