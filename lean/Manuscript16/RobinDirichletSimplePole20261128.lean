import Mathlib
import Manuscript16.RobinDirichletBoundState20261127

/-!
# M16 v16.5 §14.2, Proposition 14.2: the Robin resolvent across the bound state and the simple pole at `t₀ = c − β²`

Setting of #603–#659: `c = ‖κ‖²`, `β > 0`, `t₀ = c − β²`, `L2 = L²((0,∞); ℂ)`; for `a > 0`,
`K_D(a) = KDop`, `K_R(a) = KRop = K_D(a) + P_a` with `P_a = (a − β)⁻¹ |v_a⟩⟨v_a|`, `v_a(z) = e^{−az}`
(#603, #605); `H_D = t₁ + K_D(a₁)⁻¹`, `H_R = t₁ + K_R(a₁)⁻¹` for one fixed level `t₁ < t₀`,
`a₁ = √(c − t₁)` (self-adjoint, #611; independent of `t₁ < t₀`, #632); `u_β = √(2β) v_β` and
`Q = |u_β⟩⟨u_β|` (#604); `H_R u_β = t₀ u_β`, `ran Q = ker(H_R − t₀)` and
`(t − t₀)(H_R − t)⁻¹ → −Q` as `t ↑ t₀` (#659).

The audit note of Proposition 14.2 states that "the Robin resolvent has a simple pole at `a = β`,
corresponding to `t = c − β²`".  #604 and #659 proved the residue only from the left (`t ↑ t₀`,
`a ↓ β`) and list as not claimed "the resolvent of `H_R` at levels `t₀ < t < c` and the limit
`t ↓ t₀`; that `t₀` is an isolated point of `σ(H_R)` on its right".  This file proves:

* Part A: `K_D(b) v_a = (b² − a²)⁻¹ (v_a − v_b)` for **all** `a, b > 0`, `a ≠ b` (`KDop_vvec_ne`);
  the case `b < a` follows from the case `a < b` of #659 and the first resolvent identity of #632.
* Part B: the first resolvent identity `K_R(a) − K_R(b) = (b² − a²) K_R(a) K_R(b)` for all
  `a, b > 0` with `a ≠ β`, `b ≠ β` (`KRop_resolvent_identity_ne`), by exact rank-one algebra on top
  of the Dirichlet identity of #632; in particular below the bound state (`a < β`), where `K_R(a)`
  is not positive.
* Part C: `K_R(a)` is injective for `a > 0`, `a ≠ β` (`KRop_injective_ne`);
  `t + K_R(a)⁻¹ = s + K_R(b)⁻¹` whenever `t + a² = s + b²` (`HR_eq_of_level_ne`); hence for every
  level `t < c`, `t ≠ t₀`, the operator `K_R(√(c − t)) = K_D(a) + (a − β)⁻¹ |v_a⟩⟨v_a|` (#605;
  for `a > β` the integral operator of the printed kernel `G_R`, #603; for `a < β` the rank-one
  coefficient `(a − β)⁻¹` is negative) is the bounded two-sided inverse of `H_R − t`
  (`HR_resolvent_ne`).
* Part D: the exact identity `(t − t₀) P_{√(c−t)} = −(a + β) |v_a⟩⟨v_a|` for every `t < c`,
  `t ≠ t₀`; two-sided continuity of `a ↦ v_a` at `β`; **two-sided residue**
  `(t − t₀)(H_R − t)⁻¹ → −Q` as `t → t₀`, `t ≠ t₀` (`tendsto_resolvent_residue_ne`), and the
  regular part `(H_R − t)⁻¹ + (t − t₀)⁻¹ Q` is bounded near `t₀` (`regular_part_bounded`): the
  pole at `t₀` is simple, with residue `−Q`.
* Manuscript form `prop14_2_simple_pole` on the fixed operators `H_D`, `H_R`.

Published results cited, not re-proved: as in #659, the identification of the orthogonal projection
onto `ker(H_R − t₀)` with the spectral projection `E_{H_R}({t₀})` (spectral theorem for unbounded
self-adjoint operators, not in Mathlib at the pinned commit).

Not claimed: the pointwise kernel identity `K_R(a) f = ∫₀^∞ G_R(·,w) f(w) dw` for `a < β` (proved in
#603/#605 for `a > β` only); the essential spectrum `[c, ∞)` of `H_D`, `H_R` (spectrum at and above `c`); the
identification of `H_D`, `H_R` with the `H²(0,∞)` realisations; essential self-adjointness on the
cores of #610; Schatten-ideal membership; any Maxwell identification; the correspondence with the
printed Proposition 14.2 of `16.tex` (source not in the repository).
-/

namespace Manuscript16.RobinDirichletSimplePole

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal ComplexInnerProductSpace
open Manuscript16.RobinDirichletRankOne Manuscript16.RobinDirichletL2Bounded
  Manuscript16.RobinDirichletPositive Manuscript16.RobinDirichletInjective
  Manuscript16.RobinDirichletRealisation Manuscript16.RobinDirichletLevelIndependence
  Manuscript16.RobinDirichletPole Manuscript16.RobinDirichletBoundState

noncomputable section

variable {a b β : ℝ}

/-! ### Part A: the Dirichlet Green operator on the exponential family -/

/-- `K_D(b) v_a = (b² − a²)⁻¹ (v_a − v_b)` for `0 < b < a` (the case `a < b` is `KDop_vvec`, #659). -/
theorem KDop_vvec_of_lt (hb : 0 < b) (hba : b < a) :
    KDop hb (vvec a) = (((b ^ 2 - a ^ 2)⁻¹ : ℝ) : ℂ) • (vvec a - vvec b) := by
  have ha : 0 < a := hb.trans hba
  have hs : a ^ 2 - b ^ 2 ≠ 0 := by nlinarith
  have hid := congrArg (fun T : L2 →L[ℂ] L2 => T (vvec b)) (KDop_resolvent_identity hb ha)
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply] at hid
  rw [KDop_vvec hb ha hba] at hid
  have h1 : ((a ^ 2 - b ^ 2 : ℝ) : ℂ) •
      KDop hb ((((a ^ 2 - b ^ 2)⁻¹ : ℝ) : ℂ) • (vvec b - vvec a)) =
      KDop hb (vvec b) - KDop hb (vvec a) := by
    rw [map_smul, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs, Complex.ofReal_one,
      one_smul, map_sub]
  rw [h1] at hid
  have h2 := (sub_right_inj.mp hid).symm
  rw [h2, show b ^ 2 - a ^ 2 = -(a ^ 2 - b ^ 2) by ring, inv_neg, Complex.ofReal_neg, neg_smul,
    ← smul_neg, neg_sub]

/-- **`K_D(b) v_a = (b² − a²)⁻¹ (v_a − v_b)`** for all `a, b > 0`, `a ≠ b`:
`∫₀^∞ G_D^{(b)}(z,w) e^{−aw} dw = (e^{−az} − e^{−bz})/(b² − a²)`. -/
theorem KDop_vvec_ne (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    KDop hb (vvec a) = (((b ^ 2 - a ^ 2)⁻¹ : ℝ) : ℂ) • (vvec a - vvec b) := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact KDop_vvec ha hb h
  · exact KDop_vvec_of_lt hb h

/-! ### Part B: the first resolvent identity of the Robin Green operators across `a = β` -/

theorem KRop_apply' (ha : 0 < a) (β : ℝ) (g : L2) :
    KRop ha β g = KDop ha g + ((((a - β)⁻¹ : ℝ) : ℂ) * ⟪vvec a, g⟫) • vvec a := by
  rw [show KRop ha β g = KDop ha g + robinDiff ha β g from rfl, robinDiff_apply, vvec_eq ha]

/-- Scalar identity behind the rank-one part: `(a−β)⁻¹ − (b−β)⁻¹ = (b − a)(a−β)⁻¹(b−β)⁻¹`. -/
theorem inv_sub_inv_robin (haβ : a ≠ β) (hbβ : b ≠ β) :
    (a - β)⁻¹ - (b - β)⁻¹ = (b - a) * (a - β)⁻¹ * (b - β)⁻¹ := by
  have h1 : a - β ≠ 0 := sub_ne_zero.mpr haβ
  have h2 : b - β ≠ 0 := sub_ne_zero.mpr hbβ
  field_simp
  ring

/-- **First resolvent identity, Robin, for all `a, b > 0` different from `β`:**
`K_R(a) − K_R(b) = (b² − a²) K_R(a) K_R(b)`. -/
theorem KRop_resolvent_identity_ne (ha : 0 < a) (hb : 0 < b) (haβ : a ≠ β) (hbβ : b ≠ β) :
    KRop ha β - KRop hb β = ((b ^ 2 - a ^ 2 : ℝ) : ℂ) • (KRop ha β ∘L KRop hb β) := by
  rcases eq_or_ne a b with rfl | hab
  · ext f
    simp
  refine ContinuousLinearMap.ext fun f => ?_
  have hDD := congrArg (fun T : L2 →L[ℂ] L2 => T f) (KDop_resolvent_identity ha hb)
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply] at hDD
  have hDav : KDop ha (vvec b) = (((a ^ 2 - b ^ 2)⁻¹ : ℝ) : ℂ) • (vvec b - vvec a) :=
    KDop_vvec_ne hb ha (Ne.symm hab)
  have hDbv : KDop hb (vvec a) = (((b ^ 2 - a ^ 2)⁻¹ : ℝ) : ℂ) • (vvec a - vvec b) :=
    KDop_vvec_ne ha hb hab
  have hsym : ⟪vvec a, KDop hb f⟫ = ⟪KDop hb (vvec a), f⟫ :=
    (inner_K_symm (KDop_isSelfAdjoint hb) _ _).symm
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply]
  rw [KRop_apply' ha β (KRop hb β f), KRop_apply' hb β f, KRop_apply' ha β f, map_add, map_smul,
    hDav, inner_add_right, inner_smul_right, hsym, hDbv, inner_smul_left, inner_sub_left,
    inner_vvec ha hb, Complex.conj_ofReal]
  -- scalars
  set X : ℂ := ⟪vvec a, f⟫
  set Y : ℂ := ⟪vvec b, f⟫
  set pa : ℝ := (a - β)⁻¹ with hpa
  set pb : ℝ := (b - β)⁻¹ with hpb
  have hab2 : b ^ 2 - a ^ 2 ≠ 0 := by
    intro h
    have : (b - a) * (b + a) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact hab (by linarith)
    · linarith
  have hapb : a + b ≠ 0 := by linarith
  have e1 : ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * (((a ^ 2 - b ^ 2)⁻¹ : ℝ) : ℂ) = -1 := by
    rw [← Complex.ofReal_mul, show a ^ 2 - b ^ 2 = -(b ^ 2 - a ^ 2) by ring, inv_neg,
      mul_neg, mul_inv_cancel₀ hab2]
    simp
  have e2 : ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * (((b ^ 2 - a ^ 2)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hab2]
    simp
  have e3 : ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * (((a + b)⁻¹ : ℝ) : ℂ) = ((b - a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [show b ^ 2 - a ^ 2 = (b - a) * (a + b) by ring, mul_assoc, mul_inv_cancel₀ hapb, mul_one]
  have e4 : (pa : ℂ) - (pb : ℂ) = ((b - a : ℝ) : ℂ) * (pa : ℂ) * (pb : ℂ) := by
    have h := inv_sub_inv_robin (β := β) haβ hbβ
    rw [← hpa, ← hpb] at h
    exact_mod_cast h
  linear_combination (norm := module) hDD + e1 • (((pb : ℂ) * Y) • (vvec a - vvec b)) +
    e4 • (Y • vvec a) + e2 • ((-((pa : ℂ) * (X - Y))) • vvec a) +
    e3 • ((-((pa : ℂ) * (pb : ℂ) * Y)) • vvec a)

/-! ### Part C: one self-adjoint `H_R` and its resolvent at every level `t < c`, `t ≠ t₀` -/

/-- **`K_R(a)` is injective for every `a > 0`, `a ≠ β`** (for `a > β` this is #607). -/
theorem KRop_injective_ne (hβ : 0 < β) (ha : 0 < a) (haβ : a ≠ β) :
    Function.Injective (KRop ha β) := by
  have hb : (0 : ℝ) < β + 1 := by linarith
  have hbβ : β < β + 1 := by linarith
  have hid := KRop_resolvent_identity_ne hb ha hbβ.ne' haβ
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h := congrArg (fun T : L2 →L[ℂ] L2 => T f) hid
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply, hf, map_zero, smul_zero,
    sub_zero] at h
  exact KRop_injective hb hbβ (h.trans (map_zero _).symm)

/-- **Level independence across the bound state:** `t + K_R(a)⁻¹ = s + K_R(b)⁻¹` whenever
`a, b > 0`, `a ≠ β`, `b ≠ β` and `t + a² = s + b²` (#632 had `a, b > β`). -/
theorem HR_eq_of_level_ne (ha : 0 < a) (haβ : a ≠ β) (hb : 0 < b) (hbβ : b ≠ β) {t s : ℝ}
    (hts : t + a ^ 2 = s + b ^ 2) : HR ha β t = HR hb β s := by
  have hc : (b ^ 2 - a ^ 2 : ℝ) = t - s := by linarith
  unfold HR
  apply realisation_eq_of_resolvent_identity
  · have h := KRop_resolvent_identity_ne hb ha hbβ haβ
    have e : ((t - s : ℝ) : ℂ) = -((a ^ 2 - b ^ 2 : ℝ) : ℂ) := by
      rw [← hc]
      push_cast
      ring
    rw [e, neg_smul, ← h, neg_sub]
  · rw [KRop_resolvent_identity_ne ha hb haβ hbβ, hc]

/-- **Resolvent of `H_R` at every level `t` with `t + a² = s + b²`, `a, b > 0`, `a, b ≠ β`:**
`K_R(a)` is the bounded two-sided inverse of `H_R − t` for `H_R = s + K_R(b)⁻¹`. -/
theorem HR_resolvent_ne (hβ : 0 < β) (ha : 0 < a) (haβ : a ≠ β) (hb : 0 < b) (hbβ : b ≠ β)
    {t s : ℝ} (hts : t + a ^ 2 = s + b ^ 2) :
    (∀ f : L2, ∃ h : KRop ha β f ∈ (HR hb β s).domain,
      HR hb β s ⟨KRop ha β f, h⟩ - (t : ℂ) • KRop ha β f = f) ∧
    (∀ u : (HR hb β s).domain, KRop ha β (HR hb β s u - (t : ℂ) • (u : L2)) = u) :=
  resolvent_of_eq (KRop_injective_ne hβ ha haβ) (HR_eq_of_level_ne ha haβ hb hbβ hts)

/-! ### Part D: the two-sided simple pole at `t₀ = c − β²` -/

theorem aOf_pos_of_lt {c t : ℝ} (ht : t < c) : 0 < aOf c t := by
  unfold aOf
  exact Real.sqrt_pos.mpr (by linarith)

theorem aOf_sq_of_lt {c t : ℝ} (ht : t < c) : aOf c t ^ 2 = c - t := by
  unfold aOf
  exact Real.sq_sqrt (by linarith)

/-- `√(c − t) ≠ β` for `t < c`, `t ≠ c − β²`. -/
theorem aOf_ne {c t : ℝ} (ht : t < c) (hne : t ≠ c - β ^ 2) : aOf c t ≠ β := by
  intro h
  apply hne
  have h2 := aOf_sq_of_lt ht
  rw [h] at h2
  linarith

/-- Exact residue identity at every level `t < c`, `t ≠ t₀`:
`(t − t₀) P_{√(c−t)} = −(a + β) |v_a⟩⟨v_a|` (#604 had `t < t₀`). -/
theorem smul_robinDiffT_spectral_ne {c t : ℝ} (ht : t < c)
    (hne : t ≠ c - β ^ 2) :
    (((t - (c - β ^ 2) : ℝ)) : ℂ) • robinDiffT (aOf c t) β
      = (((-(aOf c t + β) : ℝ)) : ℂ) • rankOne ℂ (vvec (aOf c t)) (vvec (aOf c t)) := by
  have hsq := aOf_sq_of_lt ht
  have hne' : aOf c t - β ≠ 0 := sub_ne_zero.mpr (aOf_ne ht hne)
  have hscalar : (t - (c - β ^ 2)) * (aOf c t - β)⁻¹ = -(aOf c t + β) := by
    have h : t - (c - β ^ 2) = -(aOf c t + β) * (aOf c t - β) := by linear_combination hsq
    rw [h, mul_inv_cancel_right₀ hne']
  rw [robinDiffT, smul_smul, ← Complex.ofReal_mul, hscalar]

/-- Two-sided continuity of `a ↦ v_a` at `β > 0` (#604 had the right limit). -/
theorem tendsto_vvec_nhds (hβ : 0 < β) : Tendsto vvec (𝓝 β) (𝓝 (vvec β)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hden : (0 : ℝ) < 2 * β * β * (β + β) := by positivity
  have hcont : ContinuousAt (fun x : ℝ => (x - β) ^ 2 / (2 * x * β * (x + β))) β := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    exact ne_of_gt hden
  have hzero : ((β - β) ^ 2 / (2 * β * β * (β + β))) = 0 := by
    simp
  have hsq : Tendsto (fun x : ℝ => Real.sqrt ((x - β) ^ 2 / (2 * x * β * (x + β))))
      (𝓝 β) (𝓝 0) := by
    have h := (Real.continuous_sqrt.continuousAt.comp hcont).tendsto
    rw [Function.comp_apply, hzero, Real.sqrt_zero] at h
    exact h
  refine squeeze_zero' (Eventually.of_forall fun x => dist_nonneg) ?_ hsq
  filter_upwards [lt_mem_nhds hβ] with x hx
  rw [dist_eq_norm, norm_vvec_sub hx hβ]

/-- `t ↦ √(c − t)` is continuous at `t₀ = c − β²` with value `β`. -/
theorem tendsto_aOf_nhds (hβ : 0 < β) (c : ℝ) :
    Tendsto (aOf c) (𝓝 (c - β ^ 2)) (𝓝 β) := by
  have hc : Continuous (aOf c) := by
    unfold aOf; fun_prop
  have hv : aOf c (c - β ^ 2) = β := by
    unfold aOf
    rw [show c - (c - β ^ 2) = β ^ 2 by ring, Real.sqrt_sq hβ.le]
  have h := hc.tendsto (c - β ^ 2)
  rwa [hv] at h

theorem eventually_lt_c (hβ : 0 < β) (c : ℝ) :
    ∀ᶠ t in 𝓝 (c - β ^ 2), t < c - β ^ 2 / 4 :=
  Iio_mem_nhds (by nlinarith [sq_pos_of_pos hβ])

/-- `(t − t₀) P_{√(c−t)} → −Q` as `t → t₀`, `t ≠ t₀` (both sides). -/
theorem tendsto_residue_spectral_ne (hβ : 0 < β) (c : ℝ) :
    Tendsto (fun t : ℝ => (((t - (c - β ^ 2) : ℝ)) : ℂ) • robinDiffT (aOf c t) β)
      (𝓝[≠] (c - β ^ 2)) (𝓝 (-eigProj β)) := by
  have hscal : Tendsto (fun a : ℝ => (((-(a + β) : ℝ)) : ℂ)) (𝓝 β)
      (𝓝 (((-(2 * β) : ℝ)) : ℂ)) := by
    have hc : Continuous (fun a : ℝ => (((-(a + β) : ℝ)) : ℂ)) := by fun_prop
    have h2 : Tendsto (fun a : ℝ => (((-(a + β) : ℝ)) : ℂ)) (𝓝 β) (𝓝 (((-(β + β) : ℝ)) : ℂ)) :=
      hc.tendsto β
    rwa [show (-(β + β) : ℝ) = (-(2 * β) : ℝ) by ring] at h2
  have h1 : Tendsto (fun a : ℝ => (((-(a + β) : ℝ)) : ℂ) • rankOne ℂ (vvec a) (vvec a))
      (𝓝 β) (𝓝 ((((-(2 * β)) : ℝ) : ℂ) • rankOne ℂ (vvec β) (vvec β))) :=
    hscal.smul (tendsto_rankOne_self (g := vvec) (x := vvec β) (tendsto_vvec_nhds hβ))
  have h2 : ((((-(2 * β)) : ℝ) : ℂ)) • rankOne ℂ (vvec β) (vvec β) = -eigProj β := by
    rw [rankOne_vvec_eq hβ, smul_smul, ← Complex.ofReal_mul]
    rw [show (-(2 * β) * (2 * β)⁻¹ : ℝ) = -1 by
      field_simp]
    simp
  rw [h2] at h1
  refine ((h1.comp (tendsto_aOf_nhds hβ c)).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [nhdsWithin_le_nhds (eventually_lt_c hβ c), self_mem_nhdsWithin] with t ht hne
  have htc : t < c := by nlinarith [sq_nonneg β]
  exact (smul_robinDiffT_spectral_ne htc hne).symm

/-- `‖K_D(√(c − t))‖ ≤ 4/β²` for `t < c − β²/4`. -/
theorem norm_KDopT_le (hβ : 0 < β) {c t : ℝ} (ht : t < c - β ^ 2 / 4) :
    ‖KDopT (aOf c t)‖ ≤ 4 * (β ^ 2)⁻¹ := by
  have htc : t < c := by nlinarith [sq_nonneg β]
  have ha := aOf_pos_of_lt htc
  rw [KDopT_eq ha]
  calc ‖KDop ha‖ ≤ (aOf c t ^ 2)⁻¹ := norm_KDop_le ha
    _ ≤ 4 * (β ^ 2)⁻¹ := by
      rw [aOf_sq_of_lt htc, show 4 * (β ^ 2)⁻¹ = (β ^ 2 / 4)⁻¹ by rw [inv_div, div_eq_mul_inv]]
      exact inv_anti₀ (by positivity) (by linarith)

/-- `(t − t₀) K_D(√(c − t)) → 0` in operator norm as `t → t₀`. -/
theorem tendsto_smul_KDopT_nhds (hβ : 0 < β) (c : ℝ) :
    Tendsto (fun t : ℝ => (((t - (c - β ^ 2) : ℝ)) : ℂ) • KDopT (aOf c t))
      (𝓝 (c - β ^ 2)) (𝓝 0) := by
  have hcont : Continuous (fun t : ℝ => |t - (c - β ^ 2)| * (4 * (β ^ 2)⁻¹)) := by fun_prop
  have hlim : Tendsto (fun t : ℝ => |t - (c - β ^ 2)| * (4 * (β ^ 2)⁻¹)) (𝓝 (c - β ^ 2))
      (𝓝 0) := by
    have h := hcont.tendsto (c - β ^ 2)
    simpa using h
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_lt_c hβ c] with t ht
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  exact norm_KDopT_le hβ ht

/-- **Two-sided residue of the Robin resolvent.** `(t − t₀) K_R(√(c − t)) → −Q` in operator norm
as `t → t₀ = c − β²`, `t ≠ t₀`. -/
theorem tendsto_resolvent_residue_ne (hβ : 0 < β) (c : ℝ) :
    Tendsto (fun t : ℝ => (((t - (c - β ^ 2) : ℝ)) : ℂ) • KRopT (aOf c t) β)
      (𝓝[≠] (c - β ^ 2)) (𝓝 (-eigProj β)) := by
  have h := ((tendsto_smul_KDopT_nhds hβ c).mono_left nhdsWithin_le_nhds).add
    (tendsto_residue_spectral_ne hβ c)
  rw [zero_add] at h
  refine h.congr' (Eventually.of_forall fun t => ?_)
  simp only [KRopT, smul_add]

/-! #### The pole is simple: the regular part is bounded near `t₀` -/

/-- Comparison function `G(a) = a⁻² + (2aβ(a+β))^{−1/2} (‖v_a‖ + ‖v_β‖) + (a+β)⁻¹ ‖v_β‖²`. -/
def regBound (β a : ℝ) : ℝ :=
  (a ^ 2)⁻¹ + (Real.sqrt (2 * a * β * (a + β)))⁻¹ * (‖vvec a‖ + ‖vvec β‖) +
    (a + β)⁻¹ * ‖vvec β‖ ^ 2

theorem tendsto_regBound (hβ : 0 < β) : Tendsto (regBound β) (𝓝 β) (𝓝 (regBound β β)) := by
  have hv := (tendsto_vvec_nhds hβ).norm
  have T1 : Tendsto (fun a : ℝ => (a ^ 2)⁻¹) (𝓝 β) (𝓝 ((β ^ 2)⁻¹)) :=
    ((continuous_pow 2).tendsto β).inv₀ (pow_ne_zero 2 hβ.ne')
  have hD : (0 : ℝ) < 2 * β * β * (β + β) := by positivity
  have T2 : Tendsto (fun a : ℝ => (Real.sqrt (2 * a * β * (a + β)))⁻¹) (𝓝 β)
      (𝓝 ((Real.sqrt (2 * β * β * (β + β)))⁻¹)) :=
    (((by fun_prop : Continuous fun a : ℝ => 2 * a * β * (a + β)).tendsto β).sqrt).inv₀
      (Real.sqrt_pos.mpr hD).ne'
  have T3 : Tendsto (fun a : ℝ => (a + β)⁻¹) (𝓝 β) (𝓝 ((β + β)⁻¹)) :=
    (tendsto_id.add (tendsto_const_nhds (x := β))).inv₀ (by linarith)
  exact (T1.add (T2.mul (hv.add tendsto_const_nhds))).add (T3.mul tendsto_const_nhds)

/-- `Q = 2β |v_β⟩⟨v_β|`. -/
theorem eigProj_eq_smul_rankOne (hβ : 0 < β) :
    eigProj β = (((2 * β : ℝ)) : ℂ) • rankOne ℂ (vvec β) (vvec β) := by
  rw [rankOne_vvec_eq hβ, smul_smul, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (by positivity : (2 * β : ℝ) ≠ 0), Complex.ofReal_one, one_smul]

/-- Exact decomposition of the singular part: for `t < c`, `t ≠ t₀`, `a = √(c − t)`,
`P_a + (t − t₀)⁻¹ Q = −(β − a)⁻¹ (|v_a⟩⟨v_a| − |v_β⟩⟨v_β|) + (a + β)⁻¹ |v_β⟩⟨v_β|`. -/
theorem robinDiffT_add_smul_eigProj (hβ : 0 < β) {c t : ℝ} (ht : t < c)
    (hne : t ≠ c - β ^ 2) :
    robinDiffT (aOf c t) β + (((t - (c - β ^ 2))⁻¹ : ℝ) : ℂ) • eigProj β =
      (-(((β - aOf c t)⁻¹ : ℝ) : ℂ)) • (rankOne ℂ (vvec (aOf c t)) (vvec (aOf c t)) -
          rankOne ℂ (vvec β) (vvec β)) +
        (((aOf c t + β)⁻¹ : ℝ) : ℂ) • rankOne ℂ (vvec β) (vvec β) := by
  set a := aOf c t with ha_def
  have ha : 0 < a := aOf_pos_of_lt ht
  have haβ : a ≠ β := aOf_ne ht hne
  have hsq : a ^ 2 = c - t := aOf_sq_of_lt ht
  have hτ : t - (c - β ^ 2) = (β - a) * (β + a) := by linear_combination hsq
  have h1 : β - a ≠ 0 := sub_ne_zero.mpr (Ne.symm haβ)
  have h2 : β + a ≠ 0 := by linarith
  have h3 : a + β ≠ 0 := by linarith
  have e5r : (a - β)⁻¹ = -(β - a)⁻¹ := by
    rw [← inv_neg, neg_sub]
  have e6r : (t - (c - β ^ 2))⁻¹ * (2 * β) = (β - a)⁻¹ + (a + β)⁻¹ := by
    rw [hτ]
    field_simp
    ring
  have e5 : (((a - β)⁻¹ : ℝ) : ℂ) = -(((β - a)⁻¹ : ℝ) : ℂ) := by
    rw [e5r, Complex.ofReal_neg]
  have e6 : (((t - (c - β ^ 2))⁻¹ : ℝ) : ℂ) * (((2 * β : ℝ)) : ℂ) =
      (((β - a)⁻¹ : ℝ) : ℂ) + (((a + β)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_add, e6r]
  rw [eigProj_eq_smul_rankOne hβ, robinDiffT]
  linear_combination (norm := module) e5 • rankOne ℂ (vvec a) (vvec a) +
    e6 • rankOne ℂ (vvec β) (vvec β)

/-- **Pointwise bound of the regular part:** for `t < c`, `t ≠ t₀`, `a = √(c − t)`,
`‖(H_R − t)⁻¹ + (t − t₀)⁻¹ Q‖ ≤ G(a)`. -/
theorem norm_regular_part_le (hβ : 0 < β) {c t : ℝ} (ht : t < c) (hne : t ≠ c - β ^ 2) :
    ‖KRopT (aOf c t) β + (((t - (c - β ^ 2))⁻¹ : ℝ) : ℂ) • eigProj β‖ ≤
      regBound β (aOf c t) := by
  have ha : 0 < aOf c t := aOf_pos_of_lt ht
  have haβ : aOf c t ≠ β := aOf_ne ht hne
  have hD : 0 < 2 * aOf c t * β * (aOf c t + β) := by positivity
  have habs : |aOf c t - β| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr haβ)
  have hsplit : KRopT (aOf c t) β + (((t - (c - β ^ 2))⁻¹ : ℝ) : ℂ) • eigProj β =
      KDop ha + (robinDiffT (aOf c t) β + (((t - (c - β ^ 2))⁻¹ : ℝ) : ℂ) • eigProj β) := by
    rw [KRopT, KDopT_eq ha, add_assoc]
  have hdiff : |β - aOf c t|⁻¹ * ‖vvec (aOf c t) - vvec β‖ =
      (Real.sqrt (2 * aOf c t * β * (aOf c t + β)))⁻¹ := by
    rw [norm_vvec_sub ha hβ, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_sub_comm,
      div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ habs, one_mul]
  rw [hsplit, robinDiffT_add_smul_eigProj hβ ht hne]
  unfold regBound
  calc _ ≤ ‖KDop ha‖ + (‖(-(((β - aOf c t)⁻¹ : ℝ) : ℂ)) •
          (rankOne ℂ (vvec (aOf c t)) (vvec (aOf c t)) - rankOne ℂ (vvec β) (vvec β))‖ +
        ‖(((aOf c t + β)⁻¹ : ℝ) : ℂ) • rankOne ℂ (vvec β) (vvec β)‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ (aOf c t ^ 2)⁻¹ + ((Real.sqrt (2 * aOf c t * β * (aOf c t + β)))⁻¹ *
          (‖vvec (aOf c t)‖ + ‖vvec β‖) + (aOf c t + β)⁻¹ * ‖vvec β‖ ^ 2) := by
        gcongr
        · exact norm_KDop_le ha
        · rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_inv, ← hdiff,
            mul_assoc]
          gcongr
          exact norm_rankOne_self_sub _ _
        · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
            abs_of_pos (by linarith : (0 : ℝ) < aOf c t + β), norm_rankOne, sq]
    _ = _ := by ring

/-- **The pole at `t₀` is simple:** the regular part `(H_R − t)⁻¹ + (t − t₀)⁻¹ Q` stays bounded in
operator norm on a punctured neighbourhood of `t₀`. -/
theorem regular_part_bounded (hβ : 0 < β) (c : ℝ) :
    ∃ C : ℝ, ∀ᶠ t in 𝓝[≠] (c - β ^ 2),
      ‖KRopT (aOf c t) β + (((t - (c - β ^ 2))⁻¹ : ℝ) : ℂ) • eigProj β‖ ≤ C := by
  refine ⟨regBound β β + 1, ?_⟩
  have hlim := (tendsto_regBound hβ).comp (tendsto_aOf_nhds hβ c)
  have hev : ∀ᶠ t in 𝓝 (c - β ^ 2), (regBound β ∘ aOf c) t < regBound β β + 1 :=
    hlim.eventually (gt_mem_nhds (lt_add_one _))
  filter_upwards [nhdsWithin_le_nhds hev, nhdsWithin_le_nhds (eventually_lt_c hβ c),
    self_mem_nhdsWithin] with t h1 h2 hne
  have htc : t < c := by nlinarith [sq_nonneg β]
  exact (norm_regular_part_le hβ htc hne).trans h1.le

/-! ### Manuscript form -/

/-- **Proposition 14.2: the Robin resolvent across the bound state and the simple pole.**
With `c = ‖κ‖²`, `κ ∈ ℝ²`, `β > 0`, `t₀ = c − β²`, a fixed level `t₁ < t₀`, `a₁ = √(c − t₁)` and the
self-adjoint operators `H_R = t₁ + K_R(a₁)⁻¹`, `H_D = t₁ + K_D(a₁)⁻¹` of #611 (#632):

1. for every `t < c`, `t ≠ t₀`, with `a = √(c − t)`: `t + K_R(a)⁻¹ = H_R`;
   `K_R(a) = K_D(a) + (a − β)⁻¹ |v_a⟩⟨v_a|` (rank-one coefficient negative for `t₀ < t < c`) is the
   bounded two-sided inverse of `H_R − t`, so `(H_R − t)⁻¹ − K_D(a) = (a − β)⁻¹ |v_a⟩⟨v_a|`; and
   `(H_R − t)⁻¹ u_β = (t₀ − t)⁻¹ u_β`;
2. for real `λ < c`, `λ` is an eigenvalue of `H_R` if and only if `λ = t₀`;
3. for every `t < c`: `t + K_D(√(c − t))⁻¹ = H_D` and `K_D(√(c − t))` is the bounded two-sided
   inverse of `H_D − t`;
4. `(t − t₀)(H_R − t)⁻¹ → −Q` in operator norm as `t → t₀`, `t ≠ t₀` (both sides);
5. `(H_R − t)⁻¹ + (t − t₀)⁻¹ Q` is bounded on a punctured neighbourhood of `t₀`: the pole is simple. -/
theorem prop14_2_simple_pole {κ : EuclideanSpace ℝ (Fin 2)} (hβ : 0 < β) {t₁ : ℝ}
    (ht₁ : t₁ < ‖κ‖ ^ 2 - β ^ 2) :
    IsSelfAdjoint (HR (aOf_pos hβ ht₁) β t₁) ∧ IsSelfAdjoint (HD (aOf_pos hβ ht₁) t₁) ∧
    (∀ (t : ℝ) (ht : t < ‖κ‖ ^ 2), t ≠ ‖κ‖ ^ 2 - β ^ 2 →
      HR (aOf_pos_of_lt ht) β t = HR (aOf_pos hβ ht₁) β t₁ ∧
      KRopT (aOf (‖κ‖ ^ 2) t) β = KRop (aOf_pos_of_lt ht) β ∧
      KRopT (aOf (‖κ‖ ^ 2) t) β - KDopT (aOf (‖κ‖ ^ 2) t) = robinDiffT (aOf (‖κ‖ ^ 2) t) β ∧
      (∀ f : L2, ∃ h : KRopT (aOf (‖κ‖ ^ 2) t) β f ∈ (HR (aOf_pos hβ ht₁) β t₁).domain,
        HR (aOf_pos hβ ht₁) β t₁ ⟨KRopT (aOf (‖κ‖ ^ 2) t) β f, h⟩ -
          (t : ℂ) • KRopT (aOf (‖κ‖ ^ 2) t) β f = f) ∧
      (∀ u : (HR (aOf_pos hβ ht₁) β t₁).domain,
        KRopT (aOf (‖κ‖ ^ 2) t) β (HR (aOf_pos hβ ht₁) β t₁ u - (t : ℂ) • (u : L2)) = u) ∧
      KRopT (aOf (‖κ‖ ^ 2) t) β (eigVec β) =
        ((((‖κ‖ ^ 2 - β ^ 2) - t)⁻¹ : ℝ) : ℂ) • eigVec β) ∧
    (∀ lam : ℝ, lam < ‖κ‖ ^ 2 →
      ((∃ u : (HR (aOf_pos hβ ht₁) β t₁).domain, (u : L2) ≠ 0 ∧
          HR (aOf_pos hβ ht₁) β t₁ u = (lam : ℂ) • (u : L2)) ↔ lam = ‖κ‖ ^ 2 - β ^ 2)) ∧
    (∀ (t : ℝ) (ht : t < ‖κ‖ ^ 2),
      HD (aOf_pos_of_lt ht) t = HD (aOf_pos hβ ht₁) t₁ ∧
      (∀ f : L2, ∃ h : KDopT (aOf (‖κ‖ ^ 2) t) f ∈ (HD (aOf_pos hβ ht₁) t₁).domain,
        HD (aOf_pos hβ ht₁) t₁ ⟨KDopT (aOf (‖κ‖ ^ 2) t) f, h⟩ -
          (t : ℂ) • KDopT (aOf (‖κ‖ ^ 2) t) f = f) ∧
      (∀ u : (HD (aOf_pos hβ ht₁) t₁).domain,
        KDopT (aOf (‖κ‖ ^ 2) t) (HD (aOf_pos hβ ht₁) t₁ u - (t : ℂ) • (u : L2)) = u)) ∧
    Tendsto (fun t : ℝ => (((t - (‖κ‖ ^ 2 - β ^ 2) : ℝ)) : ℂ) • KRopT (aOf (‖κ‖ ^ 2) t) β)
      (𝓝[≠] (‖κ‖ ^ 2 - β ^ 2)) (𝓝 (-eigProj β)) ∧
    (∃ C : ℝ, ∀ᶠ t in 𝓝[≠] (‖κ‖ ^ 2 - β ^ 2),
      ‖KRopT (aOf (‖κ‖ ^ 2) t) β + (((t - (‖κ‖ ^ 2 - β ^ 2))⁻¹ : ℝ) : ℂ) • eigProj β‖ ≤ C) := by
  have ha₁ := aOf_pos hβ ht₁
  have hab₁ := lt_aOf hβ ht₁
  have hsq₁ := aOf_sq ht₁
  -- the resolvent at every level `t < c`, `t ≠ t₀`
  have hres : ∀ (t : ℝ) (ht : t < ‖κ‖ ^ 2), t ≠ ‖κ‖ ^ 2 - β ^ 2 →
      HR (aOf_pos_of_lt ht) β t = HR ha₁ β t₁ ∧
      (∀ f : L2, ∃ h : KRop (aOf_pos_of_lt ht) β f ∈ (HR ha₁ β t₁).domain,
        HR ha₁ β t₁ ⟨KRop (aOf_pos_of_lt ht) β f, h⟩ - (t : ℂ) • KRop (aOf_pos_of_lt ht) β f = f) ∧
      (∀ u : (HR ha₁ β t₁).domain,
        KRop (aOf_pos_of_lt ht) β (HR ha₁ β t₁ u - (t : ℂ) • (u : L2)) = u) := by
    intro t ht hne
    have ha := aOf_pos_of_lt ht
    have haβ := aOf_ne ht hne
    have hlev : t + aOf (‖κ‖ ^ 2) t ^ 2 = t₁ + aOf (‖κ‖ ^ 2) t₁ ^ 2 := by
      rw [aOf_sq_of_lt ht, hsq₁]
      ring
    exact ⟨HR_eq_of_level_ne ha haβ ha₁ hab₁.ne' hlev,
      HR_resolvent_ne hβ ha haβ ha₁ hab₁.ne' hlev⟩
  -- the eigenvector `u_β` of `H_R` at `t₀`
  obtain ⟨hdom, hev⟩ := HR_eigVec hβ ha₁ hab₁ t₁
  have hlev₀ : ((t₁ + (aOf (‖κ‖ ^ 2) t₁ ^ 2 - β ^ 2) : ℝ) : ℂ) = ((‖κ‖ ^ 2 - β ^ 2 : ℝ) : ℂ) := by
    rw [hsq₁]
    push_cast
    ring
  rw [hlev₀] at hev
  refine ⟨HR_isSelfAdjoint ha₁ hab₁ t₁, HD_isSelfAdjoint ha₁ t₁, ?_, ?_, ?_,
    tendsto_resolvent_residue_ne hβ _, regular_part_bounded hβ _⟩
  · intro t ht hne
    obtain ⟨hR, hR1, hR2⟩ := hres t ht hne
    have hK : KRopT (aOf (‖κ‖ ^ 2) t) β = KRop (aOf_pos_of_lt ht) β := KRopT_eq _ β
    refine ⟨hR, hK, by rw [KRopT, add_sub_cancel_left], ?_, ?_, ?_⟩
    · rw [hK]
      exact hR1
    · rw [hK]
      exact hR2
    · have h0 := hR2 ⟨eigVec β, hdom⟩
      simp only at h0
      rw [hev, ← sub_smul, map_smul] at h0
      have hs : ((‖κ‖ ^ 2 - β ^ 2 : ℝ) : ℂ) - (t : ℂ) = (((‖κ‖ ^ 2 - β ^ 2) - t : ℝ) : ℂ) := by
        push_cast
        ring
      have hs0 : (((‖κ‖ ^ 2 - β ^ 2) - t : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero, sub_ne_zero]
        exact Ne.symm hne
      rw [hs] at h0
      rw [hK]
      conv_rhs => rw [← h0]
      rw [smul_smul, Complex.ofReal_inv, inv_mul_cancel₀ hs0, one_smul]
  · intro lam hlam
    constructor
    · rintro ⟨u, hu0, hu⟩
      by_contra hne
      obtain ⟨-, -, hR2⟩ := hres lam hlam hne
      exact hu0 (eq_zero_of_resolvent hR2 u hu)
    · rintro rfl
      exact ⟨⟨eigVec β, hdom⟩, eigVec_ne_zero hβ, hev⟩
  · intro t ht
    have ha := aOf_pos_of_lt ht
    have hlev : t + aOf (‖κ‖ ^ 2) t ^ 2 = t₁ + aOf (‖κ‖ ^ 2) t₁ ^ 2 := by
      rw [aOf_sq_of_lt ht, hsq₁]
      ring
    have hD := HD_eq_of_level ha ha₁ hlev
    obtain ⟨hD1, hD2⟩ := resolvent_of_eq (t := t) (KDop_injective ha) hD
    have hK : KDopT (aOf (‖κ‖ ^ 2) t) = KDop ha := KDopT_eq ha
    refine ⟨hD, ?_, ?_⟩
    · rw [hK]
      exact hD1
    · rw [hK]
      exact hD2

end

end Manuscript16.RobinDirichletSimplePole

#print axioms Manuscript16.RobinDirichletSimplePole.KDop_vvec_of_lt
#print axioms Manuscript16.RobinDirichletSimplePole.KDop_vvec_ne
#print axioms Manuscript16.RobinDirichletSimplePole.KRop_apply'
#print axioms Manuscript16.RobinDirichletSimplePole.inv_sub_inv_robin
#print axioms Manuscript16.RobinDirichletSimplePole.KRop_resolvent_identity_ne
#print axioms Manuscript16.RobinDirichletSimplePole.KRop_injective_ne
#print axioms Manuscript16.RobinDirichletSimplePole.HR_eq_of_level_ne
#print axioms Manuscript16.RobinDirichletSimplePole.HR_resolvent_ne
#print axioms Manuscript16.RobinDirichletSimplePole.aOf_pos_of_lt
#print axioms Manuscript16.RobinDirichletSimplePole.aOf_sq_of_lt
#print axioms Manuscript16.RobinDirichletSimplePole.aOf_ne
#print axioms Manuscript16.RobinDirichletSimplePole.smul_robinDiffT_spectral_ne
#print axioms Manuscript16.RobinDirichletSimplePole.tendsto_vvec_nhds
#print axioms Manuscript16.RobinDirichletSimplePole.tendsto_aOf_nhds
#print axioms Manuscript16.RobinDirichletSimplePole.eventually_lt_c
#print axioms Manuscript16.RobinDirichletSimplePole.tendsto_residue_spectral_ne
#print axioms Manuscript16.RobinDirichletSimplePole.norm_KDopT_le
#print axioms Manuscript16.RobinDirichletSimplePole.tendsto_smul_KDopT_nhds
#print axioms Manuscript16.RobinDirichletSimplePole.tendsto_resolvent_residue_ne
#print axioms Manuscript16.RobinDirichletSimplePole.regBound
#print axioms Manuscript16.RobinDirichletSimplePole.tendsto_regBound
#print axioms Manuscript16.RobinDirichletSimplePole.eigProj_eq_smul_rankOne
#print axioms Manuscript16.RobinDirichletSimplePole.robinDiffT_add_smul_eigProj
#print axioms Manuscript16.RobinDirichletSimplePole.norm_regular_part_le
#print axioms Manuscript16.RobinDirichletSimplePole.regular_part_bounded
#print axioms Manuscript16.RobinDirichletSimplePole.prop14_2_simple_pole
