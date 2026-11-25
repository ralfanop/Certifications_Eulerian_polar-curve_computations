import Mathlib
import Manuscript16.RobinDirichletRankOne20261125

/-!
# M16 v16.5 §14.2, Proposition 14.2: the Green kernels define bounded operators on `L²(0,∞)`

`Manuscript16.RobinDirichletRankOne20261125` (PR #603) defines, for `a > 0`, the Dirichlet and
Robin Green kernels

* `G_D(z,w) = (e^{−a|z−w|} − e^{−a(z+w)})/(2a)`,
* `G_R(z,w) = (e^{−a|z−w|} + ((a+β)/(a−β)) e^{−a(z+w)})/(2a)`,

and, for `f ∈ L² = L²((0,∞); ℂ)`, the functions `(K_D f)(z) = ∫₀^∞ G_D(z,w) f(w) dw` and
`(K_R f)(z) = ∫₀^∞ G_R(z,w) f(w) dw` (`KD`, `KR`), with `K_R f − K_D f = P_a f` a.e. for the
rank-one operator `P_a = (a−β)⁻¹ |v_a⟩⟨v_a|` (`robinDiff`).  It leaves open whether `K_D f`,
`K_R f` belong to `L²` at all.  This file closes that gap.

* Part A (Schur test): for a jointly measurable kernel `k ≥ 0` whose row and column integrals are
  bounded by `M`, `∫ (∫ k(z,w) h(w) dw)² dz ≤ M² ∫ h²` for every measurable `h ≥ 0`
  (`schur_lintegral`), via the weighted Cauchy–Schwarz inequality `lintegral_mul_sq_le`.
* Part B (free kernel): `∫_ℝ e^{−a|x|} dx = 2/a`; the row and column integrals of
  `e^{−a|z−w|}/(2a)` over `(0,∞)` are at most `1/a²`; `0 ≤ G_D(z,w) ≤ e^{−a|z−w|}/(2a)` for
  `z, w ≥ 0`.
* Part C (Dirichlet operator): `K_D f ∈ L²(0,∞)` with `‖K_D f‖₂ ≤ a⁻² ‖f‖₂` for **every**
  `f ∈ L²(0,∞)`; `KDop : L² →L[ℂ] L²` with `KDop f = K_D f` a.e. and `‖KDop‖ ≤ a⁻²`; it is the
  unique bounded operator with this action.
* Part D (Robin operator): `KRop = KDop + P_a` satisfies `KRop f = K_R f` a.e. for every
  `f ∈ L²(0,∞)`, `‖KRop‖ ≤ a⁻² + 1/(2a(a−β))`, it is the unique bounded operator with this action,
  and `KRop − KDop = P_a` as operators on all of `L²(0,∞)`.
* Manuscript form `prop14_2_bounded` (`c = ‖κ‖²`, `t < c − β²`, `a = √(c − t)`, so `a⁻² = 1/(c−t)`).

Not claimed: the self-adjoint Dirichlet and Robin realisations on `H²(0,∞)` and the identification
of `KDop`, `KRop` with their resolvents `(H_D − t)⁻¹`, `(H_R − t)⁻¹` (so the bound `‖KDop‖ ≤ a⁻²`
is not called a resolvent estimate, and its sharpness is not claimed); self-adjointness or
positivity of `KDop`, `KRop`; Schatten-ideal membership; the essential spectrum; any Maxwell or
geometric identification.
-/

namespace Manuscript16.RobinDirichletL2Bounded

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal ComplexInnerProductSpace
open Manuscript16.RobinDirichletRankOne

noncomputable section

variable {a β : ℝ}

/-! ### Part A: the Schur test for nonnegative kernels -/

/-- Weighted Cauchy–Schwarz: `(∫ k h)² ≤ (∫ k)(∫ k h²)` for `k, h ≥ 0`. -/
theorem lintegral_mul_sq_le {ν : Measure ℝ} {k h : ℝ → ℝ≥0∞}
    (hk : AEMeasurable k ν) (hh : AEMeasurable h ν) :
    (∫⁻ w, k w * h w ∂ν) ^ 2 ≤ (∫⁻ w, k w ∂ν) * ∫⁻ w, k w * h w ^ 2 ∂ν := by
  have H : ∫⁻ w, k w ^ (1 / 2 : ℝ) * (k w * h w ^ 2) ^ (1 / 2 : ℝ) ∂ν ≤
      (∫⁻ w, k w ∂ν) ^ (1 / 2 : ℝ) * (∫⁻ w, k w * h w ^ 2 ∂ν) ^ (1 / 2 : ℝ) :=
    ENNReal.lintegral_mul_norm_pow_le (g := fun w => k w * h w ^ 2) hk
      (hk.mul (hh.pow_const 2)) (by norm_num) (by norm_num) (by norm_num)
  have hint : ∀ w, k w ^ (1 / 2 : ℝ) * (k w * h w ^ 2) ^ (1 / 2 : ℝ) = k w * h w := by
    intro w
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← mul_assoc,
      ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num), ← ENNReal.rpow_two,
      ← ENNReal.rpow_mul]
    norm_num
  simp only [hint] at H
  calc (∫⁻ w, k w * h w ∂ν) ^ 2
      ≤ ((∫⁻ w, k w ∂ν) ^ (1 / 2 : ℝ) * (∫⁻ w, k w * h w ^ 2 ∂ν) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ zero_le H 2
    _ = (∫⁻ w, k w ∂ν) * ∫⁻ w, k w * h w ^ 2 ∂ν := by
        rw [mul_pow, ← ENNReal.rpow_two ((∫⁻ w, k w ∂ν) ^ (1 / 2 : ℝ)),
          ← ENNReal.rpow_two ((∫⁻ w, k w * h w ^ 2 ∂ν) ^ (1 / 2 : ℝ)),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

/-- **Schur test.** If the row and column integrals of a measurable kernel `k ≥ 0` are bounded by
`M < ∞`, then `∫ (∫ k(z,w) h(w) dw)² dz ≤ M² ∫ h²`. -/
theorem schur_lintegral {ν : Measure ℝ} [SFinite ν] {k : ℝ → ℝ → ℝ≥0∞} {h : ℝ → ℝ≥0∞}
    (hk : Measurable (Function.uncurry k)) (hh : AEMeasurable h ν) {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hrow : ∀ z, ∫⁻ w, k z w ∂ν ≤ M) (hcol : ∀ w, ∫⁻ z, k z w ∂ν ≤ M) :
    ∫⁻ z, (∫⁻ w, k z w * h w ∂ν) ^ 2 ∂ν ≤ M ^ 2 * ∫⁻ w, h w ^ 2 ∂ν := by
  have hk1 : ∀ z, Measurable (k z) := fun z => hk.of_uncurry_left
  have hk2 : ∀ w, Measurable (fun z => k z w) := fun w => hk.of_uncurry_right
  calc ∫⁻ z, (∫⁻ w, k z w * h w ∂ν) ^ 2 ∂ν
      ≤ ∫⁻ z, M * ∫⁻ w, k z w * h w ^ 2 ∂ν ∂ν := by
        apply lintegral_mono
        intro z
        refine (lintegral_mul_sq_le (hk1 z).aemeasurable hh).trans ?_
        show _ ≤ M * _
        gcongr
        exact hrow z
    _ = M * ∫⁻ w, ∫⁻ z, k z w * h w ^ 2 ∂ν ∂ν := by
        rw [lintegral_const_mul' _ _ hM, lintegral_lintegral_swap]
        exact hk.aemeasurable.mul (hh.pow_const 2).comp_snd
    _ = M * ∫⁻ w, (∫⁻ z, k z w ∂ν) * h w ^ 2 ∂ν := by
        congr 1
        apply lintegral_congr
        intro w
        rw [lintegral_mul_const _ (hk2 w)]
    _ ≤ M * ∫⁻ w, M * h w ^ 2 ∂ν := by
        gcongr with w
        exact hcol w
    _ = M ^ 2 * ∫⁻ w, h w ^ 2 ∂ν := by
        rw [lintegral_const_mul' _ _ hM, ← mul_assoc, sq]

/-! ### Part B: the free kernel `e^{−a|z−w|}/(2a)` -/

/-- `∫_ℝ e^{−a|x|} dx = 2/a`. -/
theorem integral_exp_neg_abs (ha : 0 < a) : ∫ x : ℝ, Real.exp (-a * |x|) = 2 / a := by
  rw [integral_comp_abs (f := fun x => Real.exp (-a * x)),
    integral_exp_mul_Ioi (by linarith : -a < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

theorem integrable_exp_neg_abs (ha : 0 < a) : Integrable (fun x : ℝ => Real.exp (-a * |x|)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_exp_neg_abs ha]
  positivity

/-- The free kernel `e^{−a|z−w|}/(2a)` with values in `ℝ≥0∞`. -/
def freeK (a z w : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-a * |z - w|) / (2 * a))

theorem measurable_freeK (a : ℝ) : Measurable (Function.uncurry (freeK a)) := by
  have hc : Continuous fun p : ℝ × ℝ => Real.exp (-a * |p.1 - p.2|) / (2 * a) := by fun_prop
  exact hc.measurable.ennreal_ofReal

theorem freeK_symm (a z w : ℝ) : freeK a z w = freeK a w z := by
  rw [freeK, freeK, abs_sub_comm]

/-- `∫_ℝ e^{−a|w−z|}/(2a) dw = 1/a²`. -/
theorem lintegral_freeK_real (ha : 0 < a) (z : ℝ) :
    ∫⁻ w, freeK a z w = ENNReal.ofReal ((a ^ 2)⁻¹) := by
  have hshift : (∫⁻ w, freeK a z w) =
      ∫⁻ x, ENNReal.ofReal (Real.exp (-a * |x|) / (2 * a)) := by
    have h := lintegral_sub_right_eq_self
      (μ := (volume : Measure ℝ)) (fun x => ENNReal.ofReal (Real.exp (-a * |x|) / (2 * a))) z
    rw [← h]
    apply lintegral_congr
    intro w
    rw [freeK, abs_sub_comm]
  rw [hshift, ← ofReal_integral_eq_lintegral_ofReal ((integrable_exp_neg_abs ha).div_const _)
    (Eventually.of_forall fun x => by positivity), integral_div, integral_exp_neg_abs ha]
  congr 1
  field_simp

/-- Row bound of the free kernel on the half-line: `∫₀^∞ e^{−a|z−w|}/(2a) dw ≤ 1/a²`. -/
theorem row_freeK (ha : 0 < a) (z : ℝ) : ∫⁻ w, freeK a z w ∂μ ≤ ENNReal.ofReal ((a ^ 2)⁻¹) :=
  (setLIntegral_le_lintegral _ _).trans (lintegral_freeK_real ha z).le

/-- Column bound of the free kernel on the half-line. -/
theorem col_freeK (ha : 0 < a) (w : ℝ) : ∫⁻ z, freeK a z w ∂μ ≤ ENNReal.ofReal ((a ^ 2)⁻¹) := by
  simp_rw [freeK_symm a _ w]
  exact row_freeK ha w

/-- `0 ≤ G_D(z,w)` for `z, w ≥ 0`. -/
theorem greenD_nonneg (ha : 0 < a) {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w) : 0 ≤ greenD a z w := by
  unfold greenD
  apply div_nonneg _ (by positivity)
  rw [sub_nonneg, Real.exp_le_exp]
  have : |z - w| ≤ z + w := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith

/-- `G_D(z,w) ≤ e^{−a|z−w|}/(2a)`. -/
theorem greenD_le (ha : 0 < a) (z w : ℝ) : greenD a z w ≤ Real.exp (-a * |z - w|) / (2 * a) := by
  unfold greenD
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith [Real.exp_pos (-a * (z + w))]

/-- Domination of the Dirichlet kernel by the free kernel on `(0,∞)²`. -/
theorem enorm_greenD_le (ha : 0 < a) {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    ‖(greenD a z w : ℂ)‖ₑ ≤ freeK a z w := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (greenD_nonneg ha hz.le hw.le), freeK]
  exact ENNReal.ofReal_le_ofReal (greenD_le ha z w)

/-! ### Part C: the Dirichlet operator on `L²(0,∞)` -/

theorem aestronglyMeasurable_KD (ha : 0 < a) (f : L2) : AEStronglyMeasurable (KD ha f) μ := by
  have h : KD ha f = fun z => ∫ w, (greenD a z w : ℂ) * f w ∂μ := funext (KD_eq_integral ha f)
  rw [h]
  have hc : Continuous fun p : ℝ × ℝ => (greenD a p.1 p.2 : ℂ) := by
    unfold greenD
    fun_prop
  exact (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f).comp_snd).integral_prod_right'

/-- The Schur bound for `K_D`: `∫₀^∞ |K_D f|² ≤ a⁻⁴ ∫₀^∞ |f|²` in `ℝ≥0∞`. -/
theorem lintegral_KD_sq_le (ha : 0 < a) (f : L2) :
    ∫⁻ z, ‖KD ha f z‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal ((a ^ 2)⁻¹) ^ 2 * ∫⁻ w, ‖f w‖ₑ ^ 2 ∂μ := by
  refine le_trans ?_ (schur_lintegral (measurable_freeK a)
    (Lp.aestronglyMeasurable f).enorm ENNReal.ofReal_ne_top (row_freeK ha) (col_freeK ha))
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  apply pow_le_pow_left₀ zero_le
  rw [KD_eq_integral]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [enorm_mul]
  gcongr
  exact enorm_greenD_le ha hz hw

/-- `‖K_D f‖₂ ≤ a⁻² ‖f‖₂` in `ℝ≥0∞`. -/
theorem eLpNorm_KD_le (ha : 0 < a) (f : L2) :
    eLpNorm (KD ha f) 2 μ ≤ ENNReal.ofReal ((a ^ 2)⁻¹) * eLpNorm f 2 μ := by
  rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top (aestronglyMeasurable_KD ha f),
    eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top (Lp.aestronglyMeasurable f),
    eLpNorm', eLpNorm']
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc (∫⁻ z, ‖KD ha f z‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal ((a ^ 2)⁻¹) ^ 2 * ∫⁻ w, ‖f w‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_KD_sq_le ha f) (by norm_num)
    _ = ENNReal.ofReal ((a ^ 2)⁻¹) * (∫⁻ w, ‖f w‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ← ENNReal.rpow_two (ENNReal.ofReal ((a ^ 2)⁻¹)), ← ENNReal.rpow_mul]
        norm_num

/-- `K_D f ∈ L²(0,∞)` for every `f ∈ L²(0,∞)`. -/
theorem memLp_KD (ha : 0 < a) (f : L2) : MemLp (KD ha f) 2 μ :=
  memLp_iff.mpr ((eLpNorm_KD_le ha f).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top f)))

theorem KD_add (ha : 0 < a) (f g : L2) : KD ha (f + g) = KD ha f + KD ha g := by
  funext z
  simp [KD, inner_add_right]

theorem KD_smul (ha : 0 < a) (c : ℂ) (f : L2) : KD ha (c • f) = c • KD ha f := by
  funext z
  simp [KD, inner_smul_right]

theorem norm_toLp_KD_le (ha : 0 < a) (f : L2) :
    ‖(memLp_KD ha f).toLp (KD ha f)‖ ≤ (a ^ 2)⁻¹ * ‖f‖ := by
  rw [Lp.norm_toLp, Lp.norm_def]
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f)) (eLpNorm_KD_le ha f)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h

/-- The Dirichlet integral operator as a bounded operator on `L²(0,∞)`. -/
def KDop (ha : 0 < a) : L2 →L[ℂ] L2 :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_KD ha f).toLp (KD ha f)
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z => by rw [KD_add])
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z => by rw [KD_smul]) }
    ((a ^ 2)⁻¹) (norm_toLp_KD_le ha)

theorem KDop_apply (ha : 0 < a) (f : L2) : KDop ha f = (memLp_KD ha f).toLp (KD ha f) := rfl

/-- `KDop f = K_D f` almost everywhere on `(0,∞)`, for every `f ∈ L²(0,∞)`. -/
theorem KDop_ae_eq (ha : 0 < a) (f : L2) : (KDop ha f : ℝ → ℂ) =ᵐ[μ] KD ha f :=
  (memLp_KD ha f).coeFn_toLp

/-- `‖K_D‖ ≤ a⁻²` on `L²(0,∞)`. -/
theorem norm_KDop_le (ha : 0 < a) : ‖KDop ha‖ ≤ (a ^ 2)⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- `KDop` is the only bounded operator acting by the Dirichlet Green kernel. -/
theorem KDop_unique (ha : 0 < a) (T : L2 →L[ℂ] L2)
    (hT : ∀ f : L2, (T f : ℝ → ℂ) =ᵐ[μ] KD ha f) : T = KDop ha := by
  ext1 f
  exact Lp.ext ((hT f).trans (KDop_ae_eq ha f).symm)

/-! ### Part D: the Robin operator on `L²(0,∞)` -/

/-- The Robin integral operator as a bounded operator: `K_R = K_D + P_a`. -/
def KRop (ha : 0 < a) (β : ℝ) : L2 →L[ℂ] L2 := KDop ha + robinDiff ha β

/-- `KRop f = K_R f` almost everywhere on `(0,∞)`, for every `f ∈ L²(0,∞)`. -/
theorem KRop_ae_eq (ha : 0 < a) (hab : β < a) (f : L2) :
    (KRop ha β f : ℝ → ℂ) =ᵐ[μ] KR ha β f := by
  have h : KRop ha β f = KDop ha f + robinDiff ha β f := rfl
  rw [h]
  filter_upwards [Lp.coeFn_add (KDop ha f) (robinDiff ha β f), KDop_ae_eq ha f,
    robinDiff_ae_eq ha hab f] with z h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]
  ring

/-- `KRop − KDop = P_a` as operators on all of `L²(0,∞)`. -/
theorem KRop_sub_KDop (ha : 0 < a) (β : ℝ) : KRop ha β - KDop ha = robinDiff ha β := by
  rw [KRop, add_sub_cancel_left]

/-- `‖K_R‖ ≤ a⁻² + 1/(2a(a−β))` on `L²(0,∞)`. -/
theorem norm_KRop_le (ha : 0 < a) (hab : β < a) :
    ‖KRop ha β‖ ≤ (a ^ 2)⁻¹ + (2 * a * (a - β))⁻¹ := by
  rw [KRop, ← norm_robinDiff ha hab]
  refine (norm_add_le _ _).trans ?_
  gcongr
  exact norm_KDop_le ha

/-- `KRop` is the only bounded operator acting by the Robin Green kernel. -/
theorem KRop_unique (ha : 0 < a) (hab : β < a) (T : L2 →L[ℂ] L2)
    (hT : ∀ f : L2, (T f : ℝ → ℂ) =ᵐ[μ] KR ha β f) : T = KRop ha β := by
  ext1 f
  exact Lp.ext ((hT f).trans (KRop_ae_eq ha hab f).symm)

/-- `K_R f ∈ L²(0,∞)` for every `f ∈ L²(0,∞)`. -/
theorem memLp_KR (ha : 0 < a) (hab : β < a) (f : L2) : MemLp (KR ha β f) 2 μ :=
  (Lp.memLp (KRop ha β f)).ae_eq (KRop_ae_eq ha hab f)

/-! ### Manuscript form -/

/-- Proposition 14.2 (§14.2), operator level: with `c = ‖κ‖²`, `β > 0`, `t < c − β²` and
`a = √(c − t)`, the Dirichlet and Robin Green kernels define bounded operators on `L²(0,∞)`,
`‖K_D‖ ≤ 1/(c − t)`, `‖K_R‖ ≤ 1/(c − t) + 1/(2a(a−β))`, and `K_R − K_D = P_a` on all of
`L²(0,∞)`. -/
theorem prop14_2_bounded {κ : EuclideanSpace ℝ (Fin 2)} {t : ℝ} (hβ : 0 < β)
    (ht : t < ‖κ‖ ^ 2 - β ^ 2) :
    (∀ f : L2, (KDop (aOf_pos hβ ht) f : ℝ → ℂ) =ᵐ[μ] KD (aOf_pos hβ ht) f) ∧
    (∀ f : L2, (KRop (aOf_pos hβ ht) β f : ℝ → ℂ) =ᵐ[μ] KR (aOf_pos hβ ht) β f) ∧
    ‖KDop (aOf_pos hβ ht)‖ ≤ (‖κ‖ ^ 2 - t)⁻¹ ∧
    ‖KRop (aOf_pos hβ ht) β‖ ≤
      (‖κ‖ ^ 2 - t)⁻¹ + (2 * aOf (‖κ‖ ^ 2) t * (aOf (‖κ‖ ^ 2) t - β))⁻¹ ∧
    KRop (aOf_pos hβ ht) β - KDop (aOf_pos hβ ht) = robinDiff (aOf_pos hβ ht) β := by
  have hsq := aOf_sq (c := ‖κ‖ ^ 2) ht
  refine ⟨KDop_ae_eq _, KRop_ae_eq _ (lt_aOf hβ ht), ?_, ?_, KRop_sub_KDop _ β⟩
  · rw [← hsq]
    exact norm_KDop_le _
  · rw [← hsq]
    exact norm_KRop_le _ (lt_aOf hβ ht)

end

end Manuscript16.RobinDirichletL2Bounded

#print axioms Manuscript16.RobinDirichletL2Bounded.lintegral_mul_sq_le
#print axioms Manuscript16.RobinDirichletL2Bounded.schur_lintegral
#print axioms Manuscript16.RobinDirichletL2Bounded.integral_exp_neg_abs
#print axioms Manuscript16.RobinDirichletL2Bounded.integrable_exp_neg_abs
#print axioms Manuscript16.RobinDirichletL2Bounded.measurable_freeK
#print axioms Manuscript16.RobinDirichletL2Bounded.freeK_symm
#print axioms Manuscript16.RobinDirichletL2Bounded.lintegral_freeK_real
#print axioms Manuscript16.RobinDirichletL2Bounded.row_freeK
#print axioms Manuscript16.RobinDirichletL2Bounded.col_freeK
#print axioms Manuscript16.RobinDirichletL2Bounded.greenD_nonneg
#print axioms Manuscript16.RobinDirichletL2Bounded.greenD_le
#print axioms Manuscript16.RobinDirichletL2Bounded.enorm_greenD_le
#print axioms Manuscript16.RobinDirichletL2Bounded.aestronglyMeasurable_KD
#print axioms Manuscript16.RobinDirichletL2Bounded.lintegral_KD_sq_le
#print axioms Manuscript16.RobinDirichletL2Bounded.eLpNorm_KD_le
#print axioms Manuscript16.RobinDirichletL2Bounded.memLp_KD
#print axioms Manuscript16.RobinDirichletL2Bounded.KD_add
#print axioms Manuscript16.RobinDirichletL2Bounded.KD_smul
#print axioms Manuscript16.RobinDirichletL2Bounded.norm_toLp_KD_le
#print axioms Manuscript16.RobinDirichletL2Bounded.KDop_apply
#print axioms Manuscript16.RobinDirichletL2Bounded.KDop_ae_eq
#print axioms Manuscript16.RobinDirichletL2Bounded.norm_KDop_le
#print axioms Manuscript16.RobinDirichletL2Bounded.KDop_unique
#print axioms Manuscript16.RobinDirichletL2Bounded.KRop_ae_eq
#print axioms Manuscript16.RobinDirichletL2Bounded.KRop_sub_KDop
#print axioms Manuscript16.RobinDirichletL2Bounded.norm_KRop_le
#print axioms Manuscript16.RobinDirichletL2Bounded.KRop_unique
#print axioms Manuscript16.RobinDirichletL2Bounded.memLp_KR
#print axioms Manuscript16.RobinDirichletL2Bounded.prop14_2_bounded
