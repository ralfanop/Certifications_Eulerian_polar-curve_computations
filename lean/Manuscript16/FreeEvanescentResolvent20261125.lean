import Mathlib

/-!
# M16 v16.5 §14.1, Theorem 14.1: the free evanescent resolvent as an operator on `L²(ℝ)`

Fix `κ ∈ ℝ²`, `k > 0` with `|κ| > k`, and put `α² = |κ|² − k² > 0`.  In Mathlib's convention
`𝓕 f (ξ) = ∫ e^{−2πixξ} f(x) dx`, the operator `H_κ − k² = −d²/dz² + α²` has Fourier symbol
`4π²ξ² + α²`.  This file defines

* `mulOp b`: multiplication by `(4π²ξ² + b)⁻¹` on `L²(ℝ; ℂ)`, a bounded operator;
* `resolvent b = 𝓕⁻¹ ∘ mulOp b ∘ 𝓕`, with `𝓕` Mathlib's unitary Fourier transform on `L²(ℝ)`
  (`MeasureTheory.Lp.fourierTransformₗᵢ`, Plancherel);
* `evanescentOp b u = −u'' + b u` on Schwartz space `𝓢(ℝ; ℂ)`;

and proves, for every `b > 0`:

* `norm_resolvent`: `‖resolvent b‖ = b⁻¹` (operator norm on `L²(ℝ)`, both inequalities;
  the lower one with frequency indicators of `[−δ, δ]`, `δ → 0⁺`);
* `resolvent_isPositive`, `resolvent_isSelfAdjoint`, `im_inner_self_resolvent`:
  `R` is self-adjoint and positive, and `Im ⟪f, R f⟫ = 0` for every `f ∈ L²`;
* `resolvent_injective`;
* `resolvent_sub_resolvent`: `R(b₁) − R(b₂) = (b₂ − b₁) R(b₁) R(b₂)`;
* `resolvent_evanescentOp`: `R(b)((−d²/dz² + b) u) = u` for every Schwartz `u`, with
  `evanescentOp_apply`: `(evanescentOp b u)(z) = −u''(z) + b u(z)`;

and the manuscript form `thm14_1_*` with `b = |κ|² − k²`.

Not claimed: the self-adjoint realisation of `H_κ` on the Sobolev space `H²(ℝ)` and the identity
`R = (H_κ − k²)⁻¹` on that whole domain.  The inverse identity is proved on the Schwartz core only;
Mathlib at the pinned commit does contain Sobolev (Bessel potential) spaces
(`TemperedDistribution.MemSobolev`, `BesselPotentialSpace`), and the `H²` statement through them
is not done here.  Also not claimed: the Green kernel `e^{−α|z−z'|}/(2α)`; any Maxwell boundary
realisation or trace-class statement.
-/

namespace Manuscript16.FreeEvanescentResolvent

open MeasureTheory FourierTransform Filter Topology
open scoped ENNReal ComplexInnerProductSpace

noncomputable section

/-- `L²(ℝ; ℂ)` with Lebesgue measure. -/
abbrev L2 := Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)

/-- Mathlib's unitary Fourier transform on `L²(ℝ)` (Plancherel). -/
abbrev fourierL2 : L2 ≃ₗᵢ[ℂ] L2 := Lp.fourierTransformₗᵢ ℝ ℂ

/-! ### The symbol and the multiplier -/

/-- Fourier symbol of `−d²/dz² + b`. -/
def symbol (b ξ : ℝ) : ℝ := 4 * Real.pi ^ 2 * ξ ^ 2 + b

theorem symbol_ge (b ξ : ℝ) : b ≤ symbol b ξ := by
  unfold symbol
  have : 0 ≤ 4 * Real.pi ^ 2 * ξ ^ 2 := by positivity
  linarith

theorem symbol_pos {b : ℝ} (hb : 0 < b) (ξ : ℝ) : 0 < symbol b ξ :=
  lt_of_lt_of_le hb (symbol_ge b ξ)

theorem symbol_le_of_abs_le (b : ℝ) {ξ δ : ℝ} (h : |ξ| ≤ δ) : symbol b ξ ≤ symbol b δ := by
  unfold symbol
  have h2 : ξ ^ 2 ≤ δ ^ 2 := by
    rw [← sq_abs ξ]
    exact pow_le_pow_left₀ (abs_nonneg ξ) h 2
  have : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  nlinarith

theorem continuous_symbol (b : ℝ) : Continuous (symbol b) := by
  unfold symbol
  fun_prop

/-- The multiplier `(4π²ξ² + b)⁻¹`. -/
def multiplier (b ξ : ℝ) : ℂ := (((symbol b ξ)⁻¹ : ℝ) : ℂ)

theorem continuous_multiplier {b : ℝ} (hb : 0 < b) : Continuous (multiplier b) :=
  Complex.continuous_ofReal.comp
    ((continuous_symbol b).inv₀ fun ξ => (symbol_pos hb ξ).ne')

theorem norm_multiplier {b : ℝ} (hb : 0 < b) (ξ : ℝ) :
    ‖multiplier b ξ‖ = (symbol b ξ)⁻¹ := by
  unfold multiplier
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (symbol_pos hb ξ))]

theorem norm_multiplier_le {b : ℝ} (hb : 0 < b) (ξ : ℝ) : ‖multiplier b ξ‖ ≤ b⁻¹ := by
  rw [norm_multiplier hb]
  exact inv_anti₀ hb (symbol_ge b ξ)

theorem multiplier_mul_symbol {b : ℝ} (hb : 0 < b) (ξ : ℝ) :
    multiplier b ξ * (symbol b ξ : ℂ) = 1 := by
  unfold multiplier
  rw [← Complex.ofReal_mul, inv_mul_cancel₀ (symbol_pos hb ξ).ne', Complex.ofReal_one]

theorem memLp_multiplier {b : ℝ} (hb : 0 < b) :
    MemLp (multiplier b) ∞ (volume : Measure ℝ) :=
  memLp_top_of_bound (continuous_multiplier hb).aestronglyMeasurable b⁻¹
    (ae_of_all _ (norm_multiplier_le hb))

/-- The multiplier as an element of `L^∞(ℝ)`. -/
def multiplierLinfty {b : ℝ} (hb : 0 < b) : Lp (α := ℝ) ℂ ∞ volume :=
  (memLp_multiplier hb).toLp _

/-! ### The multiplication operator on `L²(ℝ)` -/

/-- Multiplication by `(4π²ξ² + b)⁻¹` on `L²(ℝ)`. -/
def mulOp {b : ℝ} (hb : 0 < b) : L2 →L[ℂ] L2 :=
  ContinuousLinearMap.holderL volume ∞ 2 2 (ContinuousLinearMap.mul ℂ ℂ) (multiplierLinfty hb)

theorem mulOp_coeFn {b : ℝ} (hb : 0 < b) (f : L2) :
    (mulOp hb f : ℝ → ℂ) =ᵐ[volume] fun ξ => multiplier b ξ * f ξ := by
  rw [mulOp, ContinuousLinearMap.holderL_apply_apply]
  have h2 : (multiplierLinfty hb : ℝ → ℂ) =ᵐ[volume] multiplier b := MemLp.coeFn_toLp _
  filter_upwards [ContinuousLinearMap.coeFn_holder (r := 2) (ContinuousLinearMap.mul ℂ ℂ)
    (multiplierLinfty hb) f, h2] with ξ h1 h2
  rw [h1, ContinuousLinearMap.mul_apply', h2]

theorem norm_mulOp_apply_le {b : ℝ} (hb : 0 < b) (f : L2) : ‖mulOp hb f‖ ≤ b⁻¹ * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mulOp_coeFn hb f] with ξ h
  rw [h, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_multiplier_le hb ξ) (norm_nonneg _)

/-- Frequency test function: indicator of `[−δ, δ]`. -/
def bump (δ : ℝ) : L2 :=
  indicatorConstLp 2 measurableSet_Icc (by simp [Real.volume_Icc]) (1 : ℂ)
    (s := Set.Icc (-δ) δ)

theorem norm_bump_pos {δ : ℝ} (hδ : 0 < δ) : 0 < ‖bump δ‖ := by
  rw [bump, norm_indicatorConstLp (by norm_num) (by norm_num)]
  have hvol : (volume : Measure ℝ).real (Set.Icc (-δ) δ) = 2 * δ := by
    rw [Real.volume_real_Icc]
    rw [max_eq_left (by linarith)]
    ring
  rw [hvol, norm_one, one_mul]
  exact Real.rpow_pos_of_pos (by linarith) _

theorem norm_bump_le {b : ℝ} (hb : 0 < b) {δ : ℝ} :
    ‖bump δ‖ ≤ symbol b δ * ‖mulOp hb (bump δ)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mulOp_coeFn hb (bump δ), indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
    (hs := measurableSet_Icc) (hμs := (by simp [Real.volume_Icc] : (volume : Measure ℝ)
      (Set.Icc (-δ) δ) ≠ ∞)) (c := (1 : ℂ))] with ξ h1 h2
  rw [h1]
  change ‖(bump δ : ℝ → ℂ) ξ‖ ≤ _ at *
  rw [show (bump δ : ℝ → ℂ) ξ = (Set.Icc (-δ) δ).indicator (fun _ => (1 : ℂ)) ξ from h2]
  by_cases hξ : ξ ∈ Set.Icc (-δ) δ
  · rw [Set.indicator_of_mem hξ, norm_mul, norm_multiplier hb, norm_one, mul_one]
    have hab : |ξ| ≤ δ := abs_le.mpr hξ
    have hs := symbol_le_of_abs_le b hab
    have hp := symbol_pos hb ξ
    rw [le_mul_inv_iff₀ hp, one_mul]
    exact hs
  · rw [Set.indicator_of_notMem hξ, norm_zero]
    exact mul_nonneg (symbol_pos hb δ).le (norm_nonneg _)

theorem norm_mulOp {b : ℝ} (hb : 0 < b) : ‖mulOp hb‖ = b⁻¹ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hb.le) (norm_mulOp_apply_le hb)
  · have hlow : ∀ δ : ℝ, 0 < δ → (symbol b δ)⁻¹ ≤ ‖mulOp hb‖ := by
      intro δ hδ
      have hpos := norm_bump_pos hδ
      have h1 := norm_bump_le hb (δ := δ)
      have h2 := (mulOp hb).le_opNorm (bump δ)
      have hs := symbol_pos hb δ
      have h3 : ‖bump δ‖ ≤ symbol b δ * (‖mulOp hb‖ * ‖bump δ‖) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hs.le)
      have h4 : 1 ≤ symbol b δ * ‖mulOp hb‖ := by
        by_contra hcon
        replace hcon := not_le.mp hcon
        have : symbol b δ * (‖mulOp hb‖ * ‖bump δ‖) < ‖bump δ‖ := by
          rw [← mul_assoc]
          exact mul_lt_of_lt_one_left hpos hcon
        linarith
      rw [inv_le_iff_one_le_mul₀' hs]
      exact h4
    have ht : Tendsto (fun δ => (symbol b δ)⁻¹) (𝓝[>] 0) (𝓝 (symbol b 0)⁻¹) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact ((continuous_symbol b).inv₀ fun ξ => (symbol_pos hb ξ).ne').tendsto 0
    have h0 : symbol b 0 = b := by simp [symbol]
    rw [h0] at ht
    exact le_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ hδ => hlow δ hδ)

theorem inner_mulOp_left {b : ℝ} (hb : 0 < b) (f g : L2) :
    ⟪mulOp hb f, g⟫ = ⟪f, mulOp hb g⟫ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [mulOp_coeFn hb f, mulOp_coeFn hb g] with ξ h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, map_mul, multiplier, Complex.conj_ofReal]
  ring

theorem inner_self_mulOp {b : ℝ} (hb : 0 < b) (f : L2) :
    ⟪f, mulOp hb f⟫ = ((∫ ξ, (symbol b ξ)⁻¹ * ‖f ξ‖ ^ 2) : ℝ) := by
  rw [L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [mulOp_coeFn hb f] with ξ h
  rw [h]
  simp only [RCLike.inner_apply, multiplier]
  rw [mul_assoc, Complex.mul_conj']
  push_cast
  ring

theorem re_inner_self_mulOp_nonneg {b : ℝ} (hb : 0 < b) (f : L2) :
    0 ≤ RCLike.re ⟪f, mulOp hb f⟫ := by
  rw [inner_self_mulOp hb, RCLike.re_to_complex, Complex.ofReal_re]
  exact integral_nonneg fun ξ => mul_nonneg (inv_nonneg.mpr (symbol_pos hb ξ).le) (by positivity)

theorem multiplier_ne_zero {b : ℝ} (hb : 0 < b) (ξ : ℝ) : multiplier b ξ ≠ 0 := by
  unfold multiplier
  exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (symbol_pos hb ξ).ne')

theorem mulOp_injective {b : ℝ} (hb : 0 < b) : Function.Injective (mulOp hb) := by
  refine (injective_iff_map_eq_zero (mulOp hb)).mpr fun f hf => ?_
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have h0 : (mulOp hb f : ℝ → ℂ) =ᵐ[volume] 0 := by
    rw [hf]
    exact Lp.coeFn_zero _ _ _
  filter_upwards [mulOp_coeFn hb f, h0] with ξ h1 h2
  rw [h1] at h2
  exact (mul_eq_zero.mp h2).resolve_left (multiplier_ne_zero hb ξ)

theorem mulOp_sub_mulOp {b₁ b₂ : ℝ} (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    mulOp hb₁ - mulOp hb₂ = ((b₂ - b₁ : ℝ) : ℂ) • (mulOp hb₁ ∘L mulOp hb₂) := by
  ext1 f
  rw [sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (mulOp hb₁ f) (mulOp hb₂ f),
    Lp.coeFn_smul ((b₂ - b₁ : ℝ) : ℂ) (mulOp hb₁ (mulOp hb₂ f)),
    mulOp_coeFn hb₁ f, mulOp_coeFn hb₂ f, mulOp_coeFn hb₁ (mulOp hb₂ f)]
    with ξ hs hm h1 h2 h12
  rw [hs, hm, Pi.sub_apply, Pi.smul_apply, h1, h2, h12, h2, smul_eq_mul]
  have p1 := symbol_pos hb₁ ξ
  have p2 := symbol_pos hb₂ ξ
  have key : (symbol b₁ ξ)⁻¹ - (symbol b₂ ξ)⁻¹
      = (b₂ - b₁) * ((symbol b₁ ξ)⁻¹ * (symbol b₂ ξ)⁻¹) := by
    unfold symbol at p1 p2 ⊢
    field_simp
    ring
  simp only [multiplier]
  rw [← sub_mul, ← Complex.ofReal_sub, key]
  push_cast
  ring

/-! ### The resolvent `𝓕⁻¹ ∘ mulOp ∘ 𝓕` on `L²(ℝ)` -/

/-- The free evanescent resolvent: Fourier multiplier `(4π²ξ² + b)⁻¹` on `L²(ℝ)`. -/
def resolvent {b : ℝ} (hb : 0 < b) : L2 →L[ℂ] L2 :=
  (fourierL2.symm.toContinuousLinearEquiv : L2 →L[ℂ] L2) ∘L mulOp hb ∘L
    (fourierL2.toContinuousLinearEquiv : L2 →L[ℂ] L2)

theorem resolvent_apply {b : ℝ} (hb : 0 < b) (f : L2) :
    resolvent hb f = fourierL2.symm (mulOp hb (fourierL2 f)) := rfl

theorem fourierL2_resolvent {b : ℝ} (hb : 0 < b) (f : L2) :
    fourierL2 (resolvent hb f) = mulOp hb (fourierL2 f) := by
  rw [resolvent_apply, LinearIsometryEquiv.apply_symm_apply]

theorem norm_resolvent {b : ℝ} (hb : 0 < b) : ‖resolvent hb‖ = b⁻¹ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hb.le) fun f => ?_
    rw [resolvent_apply, LinearIsometryEquiv.norm_map]
    calc ‖mulOp hb (fourierL2 f)‖ ≤ b⁻¹ * ‖fourierL2 f‖ := norm_mulOp_apply_le hb _
      _ = b⁻¹ * ‖f‖ := by rw [LinearIsometryEquiv.norm_map]
  · rw [← norm_mulOp hb]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun g => ?_
    have h := (resolvent hb).le_opNorm (fourierL2.symm g)
    rwa [resolvent_apply, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.norm_map,
      LinearIsometryEquiv.norm_map] at h

theorem inner_resolvent_left {b : ℝ} (hb : 0 < b) (f g : L2) :
    ⟪resolvent hb f, g⟫ = ⟪f, resolvent hb g⟫ := by
  rw [← fourierL2.inner_map_map (resolvent hb f) g, fourierL2_resolvent, inner_mulOp_left,
    ← fourierL2_resolvent, fourierL2.inner_map_map]

theorem inner_self_resolvent {b : ℝ} (hb : 0 < b) (f : L2) :
    ⟪f, resolvent hb f⟫ =
      ((∫ ξ, (symbol b ξ)⁻¹ * ‖(fourierL2 f : ℝ → ℂ) ξ‖ ^ 2) : ℝ) := by
  rw [← fourierL2.inner_map_map f (resolvent hb f), fourierL2_resolvent, inner_self_mulOp]

theorem resolvent_isSymmetric {b : ℝ} (hb : 0 < b) :
    (resolvent hb : L2 →ₗ[ℂ] L2).IsSymmetric :=
  fun f g => inner_resolvent_left hb f g

theorem resolvent_isSelfAdjoint {b : ℝ} (hb : 0 < b) : IsSelfAdjoint (resolvent hb) :=
  (resolvent_isSymmetric hb).isSelfAdjoint

theorem re_inner_self_resolvent_nonneg {b : ℝ} (hb : 0 < b) (f : L2) :
    0 ≤ RCLike.re ⟪f, resolvent hb f⟫ := by
  rw [inner_self_resolvent hb, RCLike.re_to_complex, Complex.ofReal_re]
  exact integral_nonneg fun ξ => mul_nonneg (inv_nonneg.mpr (symbol_pos hb ξ).le) (by positivity)

theorem im_inner_self_resolvent {b : ℝ} (hb : 0 < b) (f : L2) :
    RCLike.im ⟪f, resolvent hb f⟫ = 0 := by
  rw [inner_self_resolvent hb, RCLike.im_to_complex, Complex.ofReal_im]

theorem resolvent_isPositive {b : ℝ} (hb : 0 < b) : (resolvent hb).IsPositive := by
  refine ⟨resolvent_isSymmetric hb, fun f => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf, inner_resolvent_left]
  exact re_inner_self_resolvent_nonneg hb f

theorem resolvent_injective {b : ℝ} (hb : 0 < b) : Function.Injective (resolvent hb) :=
  fourierL2.symm.injective.comp ((mulOp_injective hb).comp fourierL2.injective)

/-- First resolvent identity in the parameter `b`. -/
theorem resolvent_sub_resolvent {b₁ b₂ : ℝ} (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    resolvent hb₁ - resolvent hb₂ = ((b₂ - b₁ : ℝ) : ℂ) • (resolvent hb₁ ∘L resolvent hb₂) := by
  ext1 f
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply, resolvent_apply,
    LinearIsometryEquiv.apply_symm_apply]
  rw [← map_sub, ← map_smul]
  congr 1
  have h := congrArg (fun T : L2 →L[ℂ] L2 => T (fourierL2 f)) (mulOp_sub_mulOp hb₁ hb₂)
  simpa only [sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply] using h

/-! ### The differential operator `−d²/dz² + b` on the Schwartz core -/

/-- `−u'' + b u` on `𝓢(ℝ; ℂ)`, with `u'' = ∂₁ ∂₁ u`. -/
def evanescentOp (b : ℝ) (u : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  -(LineDeriv.lineDerivOp (1 : ℝ) (LineDeriv.lineDerivOp (1 : ℝ) u)) + (b : ℂ) • u

theorem lineDerivOp_one_eq_deriv (v : SchwartzMap ℝ ℂ) :
    ⇑(LineDeriv.lineDerivOp (1 : ℝ) v) = deriv v := by
  funext x
  rw [SchwartzMap.lineDerivOp_apply, v.differentiableAt.lineDeriv_eq_fderiv, fderiv_apply_one_eq_deriv]

theorem evanescentOp_apply (b : ℝ) (u : SchwartzMap ℝ ℂ) (z : ℝ) :
    evanescentOp b u z = -deriv (deriv u) z + (b : ℂ) * u z := by
  simp only [evanescentOp, add_apply, neg_apply, smul_apply,
    smul_eq_mul]
  rw [lineDerivOp_one_eq_deriv, lineDerivOp_one_eq_deriv]

theorem fourier_lineDerivOp_one (v : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (LineDeriv.lineDerivOp (1 : ℝ) v) ξ = (2 * Real.pi * Complex.I * ξ) * 𝓕 v ξ := by
  have ht : Function.HasTemperateGrowth (fun x : ℝ => inner ℝ x (1 : ℝ)) :=
    ((innerSL ℝ).flip (1 : ℝ)).hasTemperateGrowth
  rw [SchwartzMap.fourier_lineDerivOp_eq, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply ht]
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul, Complex.real_smul, one_mul]
  ring

theorem fourier_evanescentOp (b : ℝ) (u : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (evanescentOp b u) ξ = (symbol b ξ : ℂ) * 𝓕 u ξ := by
  rw [evanescentOp, FourierTransform.fourier_add, FourierTransform.fourier_neg,
    FourierTransform.fourier_smul, add_apply,
    neg_apply, smul_apply, fourier_lineDerivOp_one,
    fourier_lineDerivOp_one, smul_eq_mul]
  simp only [symbol]
  push_cast
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-(4 : ℂ) * (Real.pi : ℂ) ^ 2 * (ξ : ℂ) ^ 2 * 𝓕 u ξ) * hI

/-- `R(b)` inverts `−d²/dz² + b` on the Schwartz core. -/
theorem resolvent_evanescentOp {b : ℝ} (hb : 0 < b) (u : SchwartzMap ℝ ℂ) :
    resolvent hb ((evanescentOp b u).toLp 2) = u.toLp 2 := by
  rw [resolvent_apply]
  have hF : ∀ v : SchwartzMap ℝ ℂ, fourierL2 (v.toLp 2) = (𝓕 v).toLp 2 := fun v =>
    SchwartzMap.toLp_fourier_eq v
  rw [hF, LinearIsometryEquiv.symm_apply_eq, hF]
  apply Lp.ext
  filter_upwards [mulOp_coeFn hb ((𝓕 (evanescentOp b u)).toLp 2),
    SchwartzMap.coeFn_toLp (𝓕 (evanescentOp b u)) 2,
    SchwartzMap.coeFn_toLp (𝓕 u) 2] with ξ h1 h2 h3
  rw [h1, h2, h3, fourier_evanescentOp, ← mul_assoc, multiplier_mul_symbol hb, one_mul]

/-! ### Theorem 14.1 in the parameters of the manuscript -/

/-- `α² = |κ|² − k²` for `κ ∈ ℝ²` and `k ∈ ℝ`. -/
def alphaSq (κ : EuclideanSpace ℝ (Fin 2)) (k : ℝ) : ℝ := ‖κ‖ ^ 2 - k ^ 2

theorem alphaSq_pos {κ : EuclideanSpace ℝ (Fin 2)} {k : ℝ} (hk : 0 < k) (hκ : k < ‖κ‖) :
    0 < alphaSq κ k := by
  unfold alphaSq
  nlinarith

/-- `R_κ(k²) = (H_κ − k²)⁻¹`, `H_κ = −d²/dz² + |κ|²`, as a bounded operator on `L²(ℝ)`. -/
def freeEvanescentResolvent (κ : EuclideanSpace ℝ (Fin 2)) (k : ℝ) (hk : 0 < k)
    (hκ : k < ‖κ‖) : L2 →L[ℂ] L2 :=
  resolvent (alphaSq_pos hk hκ)

/-- Theorem 14.1: `‖R_κ(k²)‖_{L² → L²} = 1/α²`, `α² = |κ|² − k²`. -/
theorem thm14_1_norm (κ : EuclideanSpace ℝ (Fin 2)) (k : ℝ) (hk : 0 < k) (hκ : k < ‖κ‖) :
    ‖freeEvanescentResolvent κ k hk hκ‖ = 1 / (‖κ‖ ^ 2 - k ^ 2) := by
  rw [freeEvanescentResolvent, norm_resolvent, one_div, alphaSq]

/-- Theorem 14.1: `R_κ(k²)` is self-adjoint and positive. -/
theorem thm14_1_isPositive (κ : EuclideanSpace ℝ (Fin 2)) (k : ℝ) (hk : 0 < k)
    (hκ : k < ‖κ‖) :
    IsSelfAdjoint (freeEvanescentResolvent κ k hk hκ) ∧
      (freeEvanescentResolvent κ k hk hκ).IsPositive :=
  ⟨resolvent_isSelfAdjoint _, resolvent_isPositive _⟩

/-- Theorem 14.1: `Im ⟪f, R_κ(k²) f⟫ = 0` for every `f ∈ L²(ℝ)`. -/
theorem thm14_1_im_inner (κ : EuclideanSpace ℝ (Fin 2)) (k : ℝ) (hk : 0 < k) (hκ : k < ‖κ‖)
    (f : L2) : RCLike.im ⟪f, freeEvanescentResolvent κ k hk hκ f⟫ = 0 :=
  im_inner_self_resolvent _ f

/-- Theorem 14.1: `R_κ(k₁²) − R_κ(k₂²) = (k₁² − k₂²) R_κ(k₁²) R_κ(k₂²)`. -/
theorem thm14_1_resolvent_identity (κ : EuclideanSpace ℝ (Fin 2)) (k₁ k₂ : ℝ)
    (hk₁ : 0 < k₁) (hκ₁ : k₁ < ‖κ‖) (hk₂ : 0 < k₂) (hκ₂ : k₂ < ‖κ‖) :
    freeEvanescentResolvent κ k₁ hk₁ hκ₁ - freeEvanescentResolvent κ k₂ hk₂ hκ₂ =
      ((k₁ ^ 2 - k₂ ^ 2 : ℝ) : ℂ) •
        (freeEvanescentResolvent κ k₁ hk₁ hκ₁ ∘L freeEvanescentResolvent κ k₂ hk₂ hκ₂) := by
  rw [freeEvanescentResolvent, freeEvanescentResolvent, resolvent_sub_resolvent]
  have h : alphaSq κ k₂ - alphaSq κ k₁ = k₁ ^ 2 - k₂ ^ 2 := by
    unfold alphaSq
    ring
  rw [h]

/-- Theorem 14.1: `R_κ(k²)((H_κ − k²) u) = u` for every Schwartz function `u`, where
`(H_κ − k²) u = −u'' + (|κ|² − k²) u`. -/
theorem thm14_1_inverse_on_schwartz (κ : EuclideanSpace ℝ (Fin 2)) (k : ℝ) (hk : 0 < k)
    (hκ : k < ‖κ‖) (u : SchwartzMap ℝ ℂ) :
    freeEvanescentResolvent κ k hk hκ ((evanescentOp (‖κ‖ ^ 2 - k ^ 2) u).toLp 2) = u.toLp 2 :=
  resolvent_evanescentOp _ u

/-- Theorem 14.1: `R_κ(k²)` is injective. -/
theorem thm14_1_injective (κ : EuclideanSpace ℝ (Fin 2)) (k : ℝ) (hk : 0 < k)
    (hκ : k < ‖κ‖) : Function.Injective (freeEvanescentResolvent κ k hk hκ) :=
  resolvent_injective _

end

end Manuscript16.FreeEvanescentResolvent

#print axioms Manuscript16.FreeEvanescentResolvent.symbol_ge
#print axioms Manuscript16.FreeEvanescentResolvent.symbol_pos
#print axioms Manuscript16.FreeEvanescentResolvent.symbol_le_of_abs_le
#print axioms Manuscript16.FreeEvanescentResolvent.continuous_symbol
#print axioms Manuscript16.FreeEvanescentResolvent.continuous_multiplier
#print axioms Manuscript16.FreeEvanescentResolvent.norm_multiplier
#print axioms Manuscript16.FreeEvanescentResolvent.norm_multiplier_le
#print axioms Manuscript16.FreeEvanescentResolvent.multiplier_mul_symbol
#print axioms Manuscript16.FreeEvanescentResolvent.memLp_multiplier
#print axioms Manuscript16.FreeEvanescentResolvent.mulOp_coeFn
#print axioms Manuscript16.FreeEvanescentResolvent.norm_mulOp_apply_le
#print axioms Manuscript16.FreeEvanescentResolvent.norm_bump_pos
#print axioms Manuscript16.FreeEvanescentResolvent.norm_bump_le
#print axioms Manuscript16.FreeEvanescentResolvent.norm_mulOp
#print axioms Manuscript16.FreeEvanescentResolvent.inner_mulOp_left
#print axioms Manuscript16.FreeEvanescentResolvent.inner_self_mulOp
#print axioms Manuscript16.FreeEvanescentResolvent.re_inner_self_mulOp_nonneg
#print axioms Manuscript16.FreeEvanescentResolvent.multiplier_ne_zero
#print axioms Manuscript16.FreeEvanescentResolvent.mulOp_injective
#print axioms Manuscript16.FreeEvanescentResolvent.mulOp_sub_mulOp
#print axioms Manuscript16.FreeEvanescentResolvent.resolvent_apply
#print axioms Manuscript16.FreeEvanescentResolvent.fourierL2_resolvent
#print axioms Manuscript16.FreeEvanescentResolvent.norm_resolvent
#print axioms Manuscript16.FreeEvanescentResolvent.inner_resolvent_left
#print axioms Manuscript16.FreeEvanescentResolvent.inner_self_resolvent
#print axioms Manuscript16.FreeEvanescentResolvent.resolvent_isSymmetric
#print axioms Manuscript16.FreeEvanescentResolvent.resolvent_isSelfAdjoint
#print axioms Manuscript16.FreeEvanescentResolvent.re_inner_self_resolvent_nonneg
#print axioms Manuscript16.FreeEvanescentResolvent.im_inner_self_resolvent
#print axioms Manuscript16.FreeEvanescentResolvent.resolvent_isPositive
#print axioms Manuscript16.FreeEvanescentResolvent.resolvent_injective
#print axioms Manuscript16.FreeEvanescentResolvent.resolvent_sub_resolvent
#print axioms Manuscript16.FreeEvanescentResolvent.lineDerivOp_one_eq_deriv
#print axioms Manuscript16.FreeEvanescentResolvent.evanescentOp_apply
#print axioms Manuscript16.FreeEvanescentResolvent.fourier_lineDerivOp_one
#print axioms Manuscript16.FreeEvanescentResolvent.fourier_evanescentOp
#print axioms Manuscript16.FreeEvanescentResolvent.resolvent_evanescentOp
#print axioms Manuscript16.FreeEvanescentResolvent.alphaSq_pos
#print axioms Manuscript16.FreeEvanescentResolvent.thm14_1_norm
#print axioms Manuscript16.FreeEvanescentResolvent.thm14_1_isPositive
#print axioms Manuscript16.FreeEvanescentResolvent.thm14_1_im_inner
#print axioms Manuscript16.FreeEvanescentResolvent.thm14_1_resolvent_identity
#print axioms Manuscript16.FreeEvanescentResolvent.thm14_1_inverse_on_schwartz
#print axioms Manuscript16.FreeEvanescentResolvent.thm14_1_injective
