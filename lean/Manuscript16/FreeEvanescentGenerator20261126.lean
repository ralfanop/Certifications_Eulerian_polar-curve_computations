import Mathlib
import Manuscript16.FreeEvanescentResolvent20261125
import Manuscript16.RobinDirichletRealisation20261125

/-!
# M16 v16.5 §14.1, Theorem 14.1: the self-adjoint operator `−d²/dz² + α²` on `L²(ℝ)` with domain `H²(ℝ)` whose inverse is `R_κ(k²)`

`FreeEvanescentResolvent20261125` (#602, merged) defines on `L²(ℝ; ℂ)` the bounded operator
`resolvent b = 𝓕⁻¹ (4π²ξ² + b)⁻¹ 𝓕` (`b > 0`) and proves that it inverts `−d²/dz² + b` on the
Schwartz core.  Its docstring and the register list as not claimed "the self-adjoint realisation of
`H_κ` on the Sobolev space `H²(ℝ)` and the identity `R = (H_κ − k²)⁻¹` on that whole domain".  This
file proves it, with Mathlib's own Sobolev space (`TemperedDistribution.MemSobolev`, Bessel potential
definition) and Mathlib's distributional derivative on `𝓢'(ℝ)`.

* `generator hb`: the unbounded operator `B = resolvent⁻¹` on `L²(ℝ)` (a Mathlib `LinearPMap`),
  built with the merged abstract construction `RobinDirichletRealisation.realisation` (#611, here
  with `t = 0`), not re-proved.
* `generator_isSelfAdjoint`: `B` is self-adjoint.
* `generator_resolvent`, `resolvent_generator`: `B (R f) = f` for every `f ∈ L²(ℝ)` and
  `R (B u) = u` for every `u ∈ dom B`: **`R = B⁻¹`**.
* `toDist_generator`: for every `u ∈ dom B`, **`B u = −u'' + b u` in `𝓢'(ℝ)`**, with
  `u'' = ∂₁ ∂₁ u` the distributional second derivative (`distOp`).
* `mem_domain_iff_distOp`, `mem_domain_iff_secondDeriv`: `dom B` is the maximal domain
  `{u ∈ L² : −u'' + b u ∈ L²} = {u ∈ L² : u'' ∈ L²}` (derivatives in `𝓢'(ℝ)`).
* `generator_domain_eq`: **`dom B = H²(ℝ)`**, with `H2Line = {u ∈ L² : MemSobolev 2 2 u}` the
  Sobolev space of Mathlib (`𝓕⁻¹ (1 + |ξ|²) 𝓕 u ∈ L²`).
* `generator_schwartz`: on the Schwartz core `B u = −u'' + b u` pointwise (`evanescentOp` of #602).
* `re_inner_generator_ge`: `Re ⟪u, B u⟫ ≥ b ‖u‖²` on `dom B`.
* `generator_sub_generator`: for `b₁, b₂ > 0` the domains coincide and `B_{b₁} u = B_{b₂} u +
  (b₁ − b₂) u`: the operator `B_b − b` does not depend on the auxiliary level `b`.
* `thm14_1_selfadjoint_realisation`: manuscript form with `H_κ − k² = B_{α²}`,
  `α² = |κ|² − k²`: self-adjoint, domain `H²(ℝ)`, `(H_κ − k²)⁻¹ = R_κ(k²)` on both sides, acting as
  `−u'' + α² u`, and `H_κ = B_{α²} + k²` independent of `k`.

Inputs used, not re-proved: Mathlib (Plancherel, `𝓕` on `𝓢'`, `MemSobolev`,
`Lp.ker_toTemperedDistributionCLM_eq_bot`, `fourier_lineDerivOp_eq`); #602 (`resolvent`, its
self-adjointness, injectivity and its action on Schwartz functions); #611 (self-adjointness of
`t + K⁻¹` for a bounded self-adjoint injective `K`).

Not claimed: the Green kernel `e^{−α|z−z'|}/(2α)`; equivalence of Mathlib's Bessel-potential
definition of `H²(ℝ)` with the definition by weak derivatives of all orders up to two (only
`{u ∈ L² : u'' ∈ L²} = H²(ℝ)` is proved here); spectrum of `B` beyond the lower bound; any Maxwell
boundary realisation; correspondence with the printed statement of Theorem 14.1 of `16.tex` (source
not in the repository).
-/

namespace Manuscript16.FreeEvanescentGenerator20261126

open MeasureTheory FourierTransform Filter Topology TemperedDistribution LineDeriv
open scoped ENNReal ComplexInnerProductSpace SchwartzMap
open Manuscript16.FreeEvanescentResolvent
open Manuscript16.RobinDirichletRealisation (realisation realisation_isSelfAdjoint
  mem_realisation_domain K_mem_domain realisation_sub_K K_realisation_sub)

noncomputable section

/-! ### `L²(ℝ)` inside `𝓢'(ℝ)` -/

/-- The embedding `L²(ℝ) → 𝓢'(ℝ)`, `u ↦ (φ ↦ ∫ φ u)` (Mathlib). -/
def toDist : L2 →L[ℂ] 𝓢'(ℝ, ℂ) := Lp.toTemperedDistributionCLM ℂ volume 2

theorem toDist_apply (u : L2) (φ : 𝓢(ℝ, ℂ)) : toDist u φ = ∫ x, φ x • u x :=
  Lp.toTemperedDistribution_apply u φ

/-- `L²(ℝ) → 𝓢'(ℝ)` is injective. -/
theorem toDist_injective : Function.Injective toDist :=
  LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)
    (μ := (volume : Measure ℝ)) (p := 2))

theorem fourier_toDist (u : L2) : 𝓕 (toDist u) = toDist (fourierL2 u) :=
  Lp.fourier_toTemperedDistribution_eq u

theorem fourierInv_toDist (u : L2) : 𝓕⁻ (toDist u) = toDist (fourierL2.symm u) :=
  Lp.fourierInv_toTemperedDistribution_eq u

/-- If `G = p F` almost everywhere, then `p · F = G` in `𝓢'(ℝ)`. -/
theorem smulLeftCLM_toDist {p : ℝ → ℂ} (hp : p.HasTemperateGrowth) {F G : L2}
    (h : (G : ℝ → ℂ) =ᵐ[volume] fun ξ => p ξ * F ξ) :
    smulLeftCLM ℂ p (toDist F) = toDist G := by
  ext φ
  rw [smulLeftCLM_apply_apply, toDist_apply, toDist_apply]
  apply integral_congr_ae
  filter_upwards [h] with ξ hξ
  rw [SchwartzMap.smulLeftCLM_apply_apply hp, hξ, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

/-! ### The distributional operator `−d²/dz² + b` -/

/-- `T ↦ −T'' + b T` on `𝓢'(ℝ)`, with `T'' = ∂₁ ∂₁ T` (Mathlib's distributional derivative). -/
def distOp (b : ℝ) : 𝓢'(ℝ, ℂ) →L[ℂ] 𝓢'(ℝ, ℂ) :=
  -(lineDerivOpCLM ℂ 𝓢'(ℝ, ℂ) (1 : ℝ) ∘L lineDerivOpCLM ℂ 𝓢'(ℝ, ℂ) (1 : ℝ)) +
    (b : ℂ) • ContinuousLinearMap.id ℂ 𝓢'(ℝ, ℂ)

theorem distOp_apply (b : ℝ) (T : 𝓢'(ℝ, ℂ)) :
    distOp b T = -(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} T)) + (b : ℂ) • T := rfl

/-- The symbol `4π²ξ² + b` as a complex function. -/
def symbolC (b ξ : ℝ) : ℂ := ((symbol b ξ : ℝ) : ℂ)

theorem symbolC_hasTemperateGrowth (b : ℝ) : (symbolC b).HasTemperateGrowth := by
  have h : symbolC b = fun ξ : ℝ => (4 * (Real.pi : ℂ) ^ 2) * ((ξ : ℂ) ^ 2) + (b : ℂ) := by
    funext ξ
    simp only [symbolC, symbol]
    push_cast
    ring
  rw [h]
  fun_prop

/-- **`𝓕 (−T'' + b T) = (4π²ξ² + b) 𝓕 T`** in `𝓢'(ℝ)`. -/
theorem fourier_distOp (b : ℝ) (T : 𝓢'(ℝ, ℂ)) :
    𝓕 (distOp b T) = smulLeftCLM ℂ (symbolC b) (𝓕 T) := by
  have hi : (fun x : ℝ => ((inner ℝ x (1 : ℝ) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  rw [distOp_apply, FourierTransform.fourier_add, FourierTransform.fourier_neg,
    FourierTransform.fourier_smul, fourier_lineDerivOp_eq, fourier_lineDerivOp_eq]
  ext φ
  have key : -((2 * (Real.pi : ℂ) * Complex.I) • (2 * (Real.pi : ℂ) * Complex.I) •
        SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => ((inner ℝ x (1 : ℝ) : ℝ) : ℂ))
          (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => ((inner ℝ x (1 : ℝ) : ℝ) : ℂ)) φ)) +
        (b : ℂ) • φ = SchwartzMap.smulLeftCLM ℂ (symbolC b) φ := by
    ext x
    simp only [add_apply, neg_apply, smul_apply, SchwartzMap.smulLeftCLM_apply_apply hi,
      SchwartzMap.smulLeftCLM_apply_apply (symbolC_hasTemperateGrowth b)]
    simp only [symbolC, symbol, smul_eq_mul, RCLike.inner_apply, conj_trivial, one_mul]
    push_cast
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (-(4 : ℂ) * (Real.pi : ℂ) ^ 2 * (x : ℂ) ^ 2 * φ x) * hI
  simp only [add_apply, neg_apply, smul_apply, smulLeftCLM_apply_apply, map_smul]
  rw [← key, map_add, map_smul]
  simp only [map_neg, map_smul]

/-- `−w'' + b w = 0` in `𝓢'(ℝ)` with `w ∈ L²(ℝ)` and `b > 0` forces `w = 0`. -/
theorem eq_zero_of_distOp_eq_zero {b : ℝ} (hb : 0 < b) {w : L2}
    (hw : distOp b (toDist w) = 0) : w = 0 := by
  set W := fourierL2 w with hW
  have hS : smulLeftCLM ℂ (symbolC b) (toDist W) = 0 := by
    rw [hW, ← fourier_toDist, ← fourier_distOp, hw, FourierTransform.fourier_zero]
  -- weight `(1 + ξ²)⁻¹`
  set h : ℝ → ℂ := fun ξ => (((1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ) : ℝ) : ℂ) with hh
  have hht : h.HasTemperateGrowth := by rw [hh]; fun_prop
  have hval : ∀ ξ : ℝ, h ξ = (((1 + ξ ^ 2)⁻¹ : ℝ) : ℂ) := by
    intro ξ
    simp only [hh]
    rw [Real.rpow_neg_one, Real.norm_eq_abs, sq_abs]
  set q : ℝ → ℂ := symbolC b * h with hq
  have hqt : q.HasTemperateGrowth := (symbolC_hasTemperateGrowth b).mul hht
  have hqval : ∀ ξ : ℝ, q ξ = ((symbol b ξ / (1 + ξ ^ 2) : ℝ) : ℂ) := by
    intro ξ
    rw [hq, Pi.mul_apply, hval, symbolC, ← Complex.ofReal_mul, div_eq_mul_inv]
  have hpos : ∀ ξ : ℝ, 0 < 1 + ξ ^ 2 := fun ξ => by positivity
  have hqne : ∀ ξ : ℝ, q ξ ≠ 0 := by
    intro ξ
    rw [hqval]
    exact Complex.ofReal_ne_zero.mpr (div_pos (symbol_pos hb ξ) (hpos ξ)).ne'
  have hqle : ∀ ξ : ℝ, ‖q ξ‖ ≤ 4 * Real.pi ^ 2 + b := by
    intro ξ
    rw [hqval, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos (symbol_pos hb ξ) (hpos ξ)), div_le_iff₀ (hpos ξ)]
    unfold symbol
    have : 0 ≤ b * ξ ^ 2 := mul_nonneg hb.le (sq_nonneg ξ)
    nlinarith
  have hqc : Continuous q := hqt.1.continuous
  have hmem : MemLp (fun ξ => q ξ * W ξ) 2 (volume : Measure ℝ) := by
    refine (Lp.memLp W).of_le_mul (c := 4 * Real.pi ^ 2 + b)
      (hqc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable W)) (ae_of_all _ fun ξ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hqle ξ) (norm_nonneg _)
  set G : L2 := hmem.toLp _ with hG
  have hGq : smulLeftCLM ℂ q (toDist W) = toDist G :=
    smulLeftCLM_toDist hqt (MemLp.coeFn_toLp hmem)
  have hG0 : toDist G = 0 := by
    rw [← hGq, hq, ← smulLeftCLM_smulLeftCLM_apply (symbolC_hasTemperateGrowth b) hht, hS,
      map_zero]
  have hG0' : G = 0 := toDist_injective (by rw [hG0, map_zero])
  have hW0 : W = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    have h0 : (G : ℝ → ℂ) =ᵐ[volume] 0 := by
      rw [hG0']
      exact Lp.coeFn_zero _ _ _
    filter_upwards [MemLp.coeFn_toLp hmem, h0] with ξ h1 h2
    rw [← hG, h2] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (hqne ξ)
  exact fourierL2.injective (by rw [← hW, hW0, map_zero])

/-! ### The resolvent solves `−u'' + b u = f` in `𝓢'(ℝ)` -/

theorem fourierL2_resolvent_ae {b : ℝ} (hb : 0 < b) (f : L2) :
    (fourierL2 f : ℝ → ℂ) =ᵐ[volume] fun ξ => symbolC b ξ * fourierL2 (resolvent hb f) ξ := by
  rw [fourierL2_resolvent]
  filter_upwards [mulOp_coeFn hb (fourierL2 f)] with ξ h
  rw [h, ← mul_assoc, symbolC, mul_comm ((symbol b ξ : ℝ) : ℂ), multiplier_mul_symbol hb, one_mul]

/-- **`−(R f)'' + b R f = f`** in `𝓢'(ℝ)` for every `f ∈ L²(ℝ)`. -/
theorem distOp_resolvent {b : ℝ} (hb : 0 < b) (f : L2) :
    distOp b (toDist (resolvent hb f)) = toDist f := by
  calc distOp b (toDist (resolvent hb f))
      = 𝓕⁻ (𝓕 (distOp b (toDist (resolvent hb f)))) := (fourierInv_fourier_eq _).symm
    _ = 𝓕⁻ (smulLeftCLM ℂ (symbolC b) (toDist (fourierL2 (resolvent hb f)))) := by
        rw [fourier_distOp, fourier_toDist]
    _ = 𝓕⁻ (toDist (fourierL2 f)) := by
        rw [smulLeftCLM_toDist (symbolC_hasTemperateGrowth b) (fourierL2_resolvent_ae hb f)]
    _ = toDist f := by rw [← fourier_toDist, fourierInv_fourier_eq]

/-- `u = R f` iff `−u'' + b u = f` in `𝓢'(ℝ)`. -/
theorem resolvent_eq_iff_distOp {b : ℝ} (hb : 0 < b) (f u : L2) :
    resolvent hb f = u ↔ distOp b (toDist u) = toDist f := by
  constructor
  · rintro rfl
    exact distOp_resolvent hb f
  · intro h
    have h0 : distOp b (toDist (u - resolvent hb f)) = 0 := by
      rw [map_sub, map_sub, h, distOp_resolvent, sub_self]
    exact (sub_eq_zero.mp (eq_zero_of_distOp_eq_zero hb h0)).symm

/-! ### The operator `B = R⁻¹` -/

/-- **The operator `B = −d²/dz² + b` on `L²(ℝ)`**: `resolvent⁻¹`, with graph `{(R f, f)}`. -/
def generator {b : ℝ} (hb : 0 < b) : L2 →ₗ.[ℂ] L2 := realisation (resolvent hb) 0

/-- `B` is self-adjoint. -/
theorem generator_isSelfAdjoint {b : ℝ} (hb : 0 < b) : IsSelfAdjoint (generator hb) :=
  realisation_isSelfAdjoint (resolvent_isSelfAdjoint hb) (resolvent_injective hb)

theorem mem_generator_domain {b : ℝ} (hb : 0 < b) {u : L2} :
    u ∈ (generator hb).domain ↔ ∃ f, resolvent hb f = u :=
  mem_realisation_domain (resolvent_injective hb)

theorem resolvent_mem_domain {b : ℝ} (hb : 0 < b) (f : L2) :
    resolvent hb f ∈ (generator hb).domain :=
  K_mem_domain (resolvent_injective hb) f

/-- `B (R f) = f` for every `f ∈ L²(ℝ)`. -/
theorem generator_resolvent {b : ℝ} (hb : 0 < b) (f : L2) :
    generator hb ⟨resolvent hb f, resolvent_mem_domain hb f⟩ = f := by
  have h := realisation_sub_K (t := 0) (resolvent_injective hb) f
  rw [Complex.ofReal_zero, zero_smul, sub_zero] at h
  exact h

/-- `R (B u) = u` for every `u ∈ dom B`. -/
theorem resolvent_generator {b : ℝ} (hb : 0 < b) (u : (generator hb).domain) :
    resolvent hb (generator hb u) = u := by
  have h := K_realisation_sub (t := 0) (resolvent_injective hb) u
  rw [Complex.ofReal_zero, zero_smul, sub_zero] at h
  exact h

/-- **`B u = −u'' + b u` in `𝓢'(ℝ)`** for every `u ∈ dom B`. -/
theorem toDist_generator {b : ℝ} (hb : 0 < b) (u : (generator hb).domain) :
    toDist (generator hb u) = distOp b (toDist (u : L2)) :=
  ((resolvent_eq_iff_distOp hb _ _).mp (resolvent_generator hb u)).symm

/-- `B` is the maximal operator: `u ∈ dom B ⇔ −u'' + b u ∈ L²(ℝ)`. -/
theorem mem_domain_iff_distOp {b : ℝ} (hb : 0 < b) (u : L2) :
    u ∈ (generator hb).domain ↔ ∃ f : L2, distOp b (toDist u) = toDist f := by
  rw [mem_generator_domain]
  exact exists_congr fun f => resolvent_eq_iff_distOp hb f u

/-- `u ∈ dom B ⇔ u'' ∈ L²(ℝ)` (second derivative in `𝓢'(ℝ)`). -/
theorem mem_domain_iff_secondDeriv {b : ℝ} (hb : 0 < b) (u : L2) :
    u ∈ (generator hb).domain ↔ ∃ g : L2, ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (toDist u)) = toDist g := by
  rw [mem_domain_iff_distOp hb]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨(b : ℂ) • u - f, ?_⟩
    rw [map_sub, map_smul, ← hf, distOp_apply]
    abel
  · rintro ⟨g, hg⟩
    refine ⟨(b : ℂ) • u - g, ?_⟩
    rw [map_sub, map_smul, ← hg, distOp_apply]
    abel

/-! ### `dom B = H²(ℝ)` -/

/-- **Mathlib's Sobolev space `H²(ℝ)`** inside `L²(ℝ)` (Bessel potential definition,
`𝓕⁻¹ (1 + |ξ|²) 𝓕 u ∈ L²`). -/
def H2Line : Set L2 := {u | MemSobolev 2 2 (toDist u)}

/-- The Bessel weight of order two is `1 + ξ²`. -/
theorem besselWeight_two (x : ℝ) :
    (((1 + ‖x‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ) = ((1 + x ^ 2 : ℝ) : ℂ) := by
  rw [div_self two_ne_zero, Real.rpow_one, Real.norm_eq_abs, sq_abs]

/-- `(4π²ξ² + b) S = 4π² (1 + ξ²) S + (b − 4π²) S` in `𝓢'(ℝ)`. -/
theorem smulLeftCLM_symbolC (b : ℝ) (S : 𝓢'(ℝ, ℂ)) :
    smulLeftCLM ℂ (symbolC b) S =
      (4 * (Real.pi : ℂ) ^ 2) •
          smulLeftCLM ℂ (fun x : ℝ => (((1 + ‖x‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ)) S +
        ((b : ℂ) - 4 * (Real.pi : ℂ) ^ 2) • S := by
  have hw : (fun x : ℝ => (((1 + ‖x‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  ext φ
  have key : SchwartzMap.smulLeftCLM ℂ (symbolC b) φ =
      SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (((1 + ‖x‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ))
          ((4 * (Real.pi : ℂ) ^ 2) • φ) + ((b : ℂ) - 4 * (Real.pi : ℂ) ^ 2) • φ := by
    ext x
    simp only [add_apply, smul_apply, SchwartzMap.smulLeftCLM_apply_apply hw,
      SchwartzMap.smulLeftCLM_apply_apply (symbolC_hasTemperateGrowth b)]
    simp only [besselWeight_two, symbolC, symbol, smul_eq_mul]
    push_cast
    ring
  simp only [add_apply, smul_apply, smulLeftCLM_apply_apply]
  rw [key, map_add, map_smul, map_smul]
  simp only [map_smul]

/-- `−u'' + b u ∈ L²(ℝ) ⇔ u ∈ H²(ℝ)` for `u ∈ L²(ℝ)`. -/
theorem exists_distOp_iff_mem_H2Line {b : ℝ} (u : L2) :
    (∃ f : L2, distOp b (toDist u) = toDist f) ↔ u ∈ H2Line := by
  have hpi : (4 * (Real.pi : ℂ) ^ 2) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 this)
  change _ ↔ MemSobolev 2 2 (toDist u)
  rw [memSobolev_iff_exists_smulLeftCLM_fourier]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨(4 * (Real.pi : ℂ) ^ 2)⁻¹ •
      (fourierL2 f - ((b : ℂ) - 4 * (Real.pi : ℂ) ^ 2) • fourierL2 u), ?_⟩
    have h1 := congrArg 𝓕 hf
    rw [fourier_distOp, smulLeftCLM_symbolC, fourier_toDist, fourier_toDist] at h1
    change _ = toDist _
    rw [fourier_toDist, map_smul, map_sub, map_smul, ← h1]
    rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hpi, one_smul]
  · rintro ⟨f', hf'⟩
    change _ = toDist f' at hf'
    refine ⟨fourierL2.symm ((4 * (Real.pi : ℂ) ^ 2) • f' +
      ((b : ℂ) - 4 * (Real.pi : ℂ) ^ 2) • fourierL2 u), ?_⟩
    rw [← fourierInv_toDist, map_add, map_smul, map_smul]
    rw [← hf', ← fourier_toDist, ← smulLeftCLM_symbolC, ← fourier_distOp,
      fourierInv_fourier_eq]

/-- **`dom B = H²(ℝ)`** (Mathlib's Sobolev space). -/
theorem generator_domain_eq {b : ℝ} (hb : 0 < b) :
    ((generator hb).domain : Set L2) = H2Line := by
  ext u
  change u ∈ (generator hb).domain ↔ u ∈ H2Line
  rw [mem_domain_iff_distOp hb, exists_distOp_iff_mem_H2Line]

/-! ### The Schwartz core -/

/-- Every Schwartz function lies in `dom B` and `B u = −u'' + b u` pointwise. -/
theorem generator_schwartz {b : ℝ} (hb : 0 < b) (u : 𝓢(ℝ, ℂ)) :
    ∃ h : (u.toLp 2 : L2) ∈ (generator hb).domain,
      generator hb ⟨u.toLp 2, h⟩ = (evanescentOp b u).toLp 2 := by
  have hR := resolvent_evanescentOp hb u
  refine ⟨hR ▸ resolvent_mem_domain hb _, ?_⟩
  have he : (⟨(u.toLp 2 : L2), hR ▸ resolvent_mem_domain hb _⟩ : (generator hb).domain) =
      ⟨resolvent hb ((evanescentOp b u).toLp 2), resolvent_mem_domain hb _⟩ :=
    Subtype.ext hR.symm
  rw [he, generator_resolvent]

/-! ### Lower bound -/

/-- `Re ⟪R f, f − b R f⟫ ≥ 0`. -/
theorem re_inner_resolvent_sub_nonneg {b : ℝ} (hb : 0 < b) (f : L2) :
    0 ≤ RCLike.re ⟪resolvent hb f, f - (b : ℂ) • resolvent hb f⟫ := by
  rw [← fourierL2.inner_map_map, map_sub, map_smul, fourierL2_resolvent, L2.inner_def]
  have hint : (fun ξ => ⟪(mulOp hb (fourierL2 f) : ℝ → ℂ) ξ,
      ((fourierL2 f - (b : ℂ) • mulOp hb (fourierL2 f) : L2) : ℝ → ℂ) ξ⟫) =ᵐ[volume]
      fun ξ => ((((symbol b ξ)⁻¹ * (1 - b * (symbol b ξ)⁻¹) * ‖fourierL2 f ξ‖ ^ 2 : ℝ)) : ℂ) := by
    filter_upwards [mulOp_coeFn hb (fourierL2 f),
      Lp.coeFn_sub (fourierL2 f) ((b : ℂ) • mulOp hb (fourierL2 f)),
      Lp.coeFn_smul (b : ℂ) (mulOp hb (fourierL2 f))] with ξ h1 h2 h3
    rw [h2, Pi.sub_apply, h3, Pi.smul_apply, h1, smul_eq_mul]
    simp only [RCLike.inner_apply, multiplier, map_mul, Complex.conj_ofReal]
    rw [show (fourierL2 f ξ) = (fourierL2 f ξ) from rfl]
    have hc : (starRingEnd ℂ) (fourierL2 f ξ) * fourierL2 f ξ = (‖fourierL2 f ξ‖ : ℂ) ^ 2 := by
      rw [mul_comm, Complex.mul_conj']
    push_cast
    linear_combination ((symbol b ξ : ℂ)⁻¹ * (1 - (b : ℂ) * (symbol b ξ : ℂ)⁻¹)) * hc
  rw [integral_congr_ae hint, integral_complex_ofReal, RCLike.re_to_complex, Complex.ofReal_re]
  refine integral_nonneg fun ξ => ?_
  have hs := symbol_pos hb ξ
  have h1 : 0 ≤ 1 - b * (symbol b ξ)⁻¹ := by
    rw [sub_nonneg, ← div_eq_mul_inv, div_le_one hs]
    exact symbol_ge b ξ
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hs.le) h1) (by positivity)

/-- **`Re ⟪u, B u⟫ ≥ b ‖u‖²`** for every `u ∈ dom B`. -/
theorem re_inner_generator_ge {b : ℝ} (hb : 0 < b) (u : (generator hb).domain) :
    b * ‖(u : L2)‖ ^ 2 ≤ RCLike.re ⟪(u : L2), generator hb u⟫ := by
  obtain ⟨f, hf⟩ := (mem_generator_domain hb).mp u.2
  have hu : u = ⟨resolvent hb f, resolvent_mem_domain hb f⟩ := Subtype.ext hf.symm
  rw [hu, generator_resolvent]
  have h := re_inner_resolvent_sub_nonneg hb f
  rw [inner_sub_right, inner_smul_right, map_sub, inner_self_eq_norm_sq_to_K] at h
  simp only [RCLike.re_to_complex] at h ⊢
  have : ((b : ℂ) * ((‖resolvent hb f‖ : ℂ) ^ 2)).re = b * ‖resolvent hb f‖ ^ 2 := by
    norm_cast
  change 0 ≤ (⟪resolvent hb f, f⟫).re - ((b : ℂ) * ((‖resolvent hb f‖ : ℂ) ^ 2)).re at h
  rw [this] at h
  linarith

/-! ### Independence of the auxiliary level -/

/-- For `b₁, b₂ > 0`, `dom B_{b₁} = dom B_{b₂}` and `B_{b₁} u = B_{b₂} u + (b₁ − b₂) u`. -/
theorem generator_sub_generator {b₁ b₂ : ℝ} (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    (generator hb₁).domain = (generator hb₂).domain ∧
      ∀ (u : L2) (h₁ : u ∈ (generator hb₁).domain) (h₂ : u ∈ (generator hb₂).domain),
        generator hb₁ ⟨u, h₁⟩ = generator hb₂ ⟨u, h₂⟩ + ((b₁ - b₂ : ℝ) : ℂ) • u := by
  refine ⟨SetLike.coe_injective ((generator_domain_eq hb₁).trans (generator_domain_eq hb₂).symm),
    fun u h₁ h₂ => toDist_injective ?_⟩
  rw [toDist_generator hb₁ ⟨u, h₁⟩, map_add, map_smul, toDist_generator hb₂ ⟨u, h₂⟩,
    distOp_apply, distOp_apply]
  push_cast
  module

/-! ### Theorem 14.1 in the parameters of the manuscript -/

/-- **M16 Theorem 14.1, the operator `H_κ − k² = −d²/dz² + α²` on `L²(ℝ)`**, `α² = |κ|² − k² > 0`:
`B = generator (α² > 0)` is self-adjoint; `dom B = H²(ℝ)` (Mathlib's Sobolev space); `R_κ(k²) = B⁻¹`
on both sides; `B u = −u'' + α² u` in `𝓢'(ℝ)` on all of `dom B`; `Re ⟪u, B u⟫ ≥ α² ‖u‖²`; and for
`0 < k₁, k₂ < |κ|` the operators `B_{α₁²} + k₁²` and `B_{α₂²} + k₂²` coincide (same domain, same
values): `H_κ = B + k²` does not depend on `k`. -/
theorem thm14_1_selfadjoint_realisation (κ : EuclideanSpace ℝ (Fin 2)) (k : ℝ) (hk : 0 < k)
    (hκ : k < ‖κ‖) :
    IsSelfAdjoint (generator (alphaSq_pos hk hκ)) ∧
    ((generator (alphaSq_pos hk hκ)).domain : Set L2) = H2Line ∧
    (∀ f : L2, ∃ h : freeEvanescentResolvent κ k hk hκ f ∈ (generator (alphaSq_pos hk hκ)).domain,
        generator (alphaSq_pos hk hκ) ⟨freeEvanescentResolvent κ k hk hκ f, h⟩ = f) ∧
    (∀ u : (generator (alphaSq_pos hk hκ)).domain,
        freeEvanescentResolvent κ k hk hκ (generator (alphaSq_pos hk hκ) u) = u) ∧
    (∀ u : (generator (alphaSq_pos hk hκ)).domain,
        toDist (generator (alphaSq_pos hk hκ) u) =
          -(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (toDist (u : L2)))) +
            ((‖κ‖ ^ 2 - k ^ 2 : ℝ) : ℂ) • toDist (u : L2)) ∧
    (∀ u : (generator (alphaSq_pos hk hκ)).domain,
        (‖κ‖ ^ 2 - k ^ 2) * ‖(u : L2)‖ ^ 2 ≤
          RCLike.re ⟪(u : L2), generator (alphaSq_pos hk hκ) u⟫) ∧
    (∀ (k' : ℝ) (hk' : 0 < k') (hκ' : k' < ‖κ‖) (u : L2)
        (h : u ∈ (generator (alphaSq_pos hk hκ)).domain)
        (h' : u ∈ (generator (alphaSq_pos hk' hκ')).domain),
        generator (alphaSq_pos hk hκ) ⟨u, h⟩ + ((k ^ 2 : ℝ) : ℂ) • u =
          generator (alphaSq_pos hk' hκ') ⟨u, h'⟩ + ((k' ^ 2 : ℝ) : ℂ) • u) := by
  refine ⟨generator_isSelfAdjoint _, generator_domain_eq _,
    fun f => ⟨resolvent_mem_domain _ f, generator_resolvent _ f⟩, resolvent_generator _,
    fun u => toDist_generator _ u, fun u => re_inner_generator_ge _ u, ?_⟩
  intro k' hk' hκ' u h h'
  rw [(generator_sub_generator (alphaSq_pos hk hκ) (alphaSq_pos hk' hκ')).2 u h h', add_assoc,
    ← add_smul]
  congr 2
  unfold alphaSq
  push_cast
  ring

end

end Manuscript16.FreeEvanescentGenerator20261126

#print axioms Manuscript16.FreeEvanescentGenerator20261126.toDist
#print axioms Manuscript16.FreeEvanescentGenerator20261126.toDist_apply
#print axioms Manuscript16.FreeEvanescentGenerator20261126.toDist_injective
#print axioms Manuscript16.FreeEvanescentGenerator20261126.fourier_toDist
#print axioms Manuscript16.FreeEvanescentGenerator20261126.fourierInv_toDist
#print axioms Manuscript16.FreeEvanescentGenerator20261126.smulLeftCLM_toDist
#print axioms Manuscript16.FreeEvanescentGenerator20261126.distOp
#print axioms Manuscript16.FreeEvanescentGenerator20261126.distOp_apply
#print axioms Manuscript16.FreeEvanescentGenerator20261126.symbolC
#print axioms Manuscript16.FreeEvanescentGenerator20261126.symbolC_hasTemperateGrowth
#print axioms Manuscript16.FreeEvanescentGenerator20261126.fourier_distOp
#print axioms Manuscript16.FreeEvanescentGenerator20261126.eq_zero_of_distOp_eq_zero
#print axioms Manuscript16.FreeEvanescentGenerator20261126.fourierL2_resolvent_ae
#print axioms Manuscript16.FreeEvanescentGenerator20261126.distOp_resolvent
#print axioms Manuscript16.FreeEvanescentGenerator20261126.resolvent_eq_iff_distOp
#print axioms Manuscript16.FreeEvanescentGenerator20261126.generator
#print axioms Manuscript16.FreeEvanescentGenerator20261126.generator_isSelfAdjoint
#print axioms Manuscript16.FreeEvanescentGenerator20261126.mem_generator_domain
#print axioms Manuscript16.FreeEvanescentGenerator20261126.resolvent_mem_domain
#print axioms Manuscript16.FreeEvanescentGenerator20261126.generator_resolvent
#print axioms Manuscript16.FreeEvanescentGenerator20261126.resolvent_generator
#print axioms Manuscript16.FreeEvanescentGenerator20261126.toDist_generator
#print axioms Manuscript16.FreeEvanescentGenerator20261126.mem_domain_iff_distOp
#print axioms Manuscript16.FreeEvanescentGenerator20261126.mem_domain_iff_secondDeriv
#print axioms Manuscript16.FreeEvanescentGenerator20261126.H2Line
#print axioms Manuscript16.FreeEvanescentGenerator20261126.besselWeight_two
#print axioms Manuscript16.FreeEvanescentGenerator20261126.smulLeftCLM_symbolC
#print axioms Manuscript16.FreeEvanescentGenerator20261126.exists_distOp_iff_mem_H2Line
#print axioms Manuscript16.FreeEvanescentGenerator20261126.generator_domain_eq
#print axioms Manuscript16.FreeEvanescentGenerator20261126.generator_schwartz
#print axioms Manuscript16.FreeEvanescentGenerator20261126.re_inner_resolvent_sub_nonneg
#print axioms Manuscript16.FreeEvanescentGenerator20261126.re_inner_generator_ge
#print axioms Manuscript16.FreeEvanescentGenerator20261126.generator_sub_generator
#print axioms Manuscript16.FreeEvanescentGenerator20261126.thm14_1_selfadjoint_realisation
