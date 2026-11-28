import Mathlib
import Manuscript16.HolonomyFunctionalCalculus20261127

/-!
# M16 `eq:hol-integral`: strong continuity of `t ↦ e^{-2t√B}` and its generator `-2√B`

`HolonomyCircleResolvent20261125` (#599) defines on `L²(S¹)`, `S¹ = ℝ/2πℤ` with normalised Haar
measure, the operators `evanescent a φ t` (`t ≥ 0`) as the Fourier multipliers with symbol
`e^{-2t√b_n}`, `b_n = (n - φ)² + a²`, `a > 0`, `φ` real, and proves `e^0 = I` and the semigroup law;
`HolonomyCircleGenerator20261125` (#622) realises `B = (D - φ)² + a²` (`D = -i d/dθ`) as a
self-adjoint operator with `dom B = H²(S¹)` (Fourier form) and `resolvent = B⁻¹`;
`HolonomyFunctionalCalculus20261127` (#643) proves `evanescent a φ t = cfc (evGen t) (B⁻¹)` for
`t > 0` and lists as not claimed "strong continuity of `t ↦ e^{-2t√B}` and the identification of
its generator with `-2√B`". This file proves both.

* `invSqrt a φ := cfc √· (B⁻¹)`, the square root of `B⁻¹` given by Mathlib's continuous functional
  calculus; `invSqrt_eq_multiplier`: it is the Fourier multiplier with symbol `b_n^{-1/2}`; it is
  bounded, self-adjoint and injective.
* `sqrtGen a φ := (cfc √· (B⁻¹))⁻¹`, the operator `√B` (merged construction
  `RobinDirichletRealisation.realisation` of #611 with `t = 0`, not re-proved):
  `sqrtGen_isSelfAdjoint`; `repr_sqrtGen`: `(√B u)^_n = √b_n û_n`; `sqrtGen_domain_eq`:
  **`dom √B = H¹(S¹)`** in Fourier form `∑_{n∈ℤ} (1 + n²) |⟪e_n, u⟫|² < ∞`; `inner_sqrtGen_re`:
  `Re ⟪u, √B u⟫ ≥ a ‖u‖²`; `sqrtGen_sq`, `mem_generator_domain_iff_sqrt`: **`(√B)² = B`** with
  domains, i.e. `u ∈ dom B ⇔ u ∈ dom √B ∧ √B u ∈ dom √B`, and then `√B (√B u) = B u`.
* `evanescent_continuous`: **strong continuity**, `t ↦ e^{-2t√B} u` is continuous on `[0, ∞)` for
  every `u ∈ L²(S¹)` (dominated convergence on the Fourier coefficients, Mathlib
  `tendsto_tsum_of_dominated_convergence`); `evanescent_tendsto_zero`: `e^{-2t√B} u → u` as `t → 0`;
  `evanescent_norm_le`: `‖e^{-2t√B}‖ ≤ 1`; `norm_evanescent_sub_id`: `‖e^{-2t√B} - I‖ = 1` for every
  `t > 0`, so the semigroup is not continuous in operator norm at `0`
  (`evanescent_not_tendsto_norm`).
* `tendsto_diffQuot`, `mem_sqrtGen_domain_of_tendsto`, `generator_iff`: **the generator of
  `t ↦ e^{-2t√B}` is `-2√B`**: for `u, v ∈ L²(S¹)`, `t⁻¹ (e^{-2t√B} u - u) → v` as `t ↓ 0` if and only
  if `u ∈ dom √B` and `v = -2√B u` (the generator in the sense of `C₀`-semigroups, with domain the
  set of `u` for which the limit exists); `semigroupGen := -2 • √B`, `semigroupGen_iff`.
* `hol_semigroup_generator`: manuscript form, all of the above together with `e^{-2t√B} =
  cfc (evGen t) (B⁻¹)` (#643).

Inputs used, not re-proved: the Fourier Hilbert basis of `L²(S¹)` (Mathlib); the Fourier
multipliers, `resolvent`, `evanescent` (#599); `B`, `H²(S¹)`, the comparison `b_n ≍ 1 + n²` (#622);
the identification of `cfc g (B⁻¹)` with the multiplier `g(1/b_n)` (#643); the abstract
self-adjointness of `K⁻¹` (#611).

Not claimed. A functional calculus of the unbounded operator `B` itself (Mathlib has none at the
pinned commit), the identity `h(B) = (h ∘ ι)(B⁻¹)` of the spectral theorem and the uniqueness of the
positive self-adjoint square root of `B` (published results cited): `√B` is *defined* as
`(cfc √· (B⁻¹))⁻¹`, and is proved here to be self-adjoint, bounded below by `a`, and to satisfy
`(√B)² = B` with domains. `H1Circle` is the Fourier-coefficient definition of `H¹(S¹)`; its
equivalence with the definition by weak derivatives is not formalised. No Hille–Yosida or
Lumer–Phillips theorem is used or proved; trace-class membership and basis independence of the
diagonal sums (Lidskii; Simon 2005) are not formalised. No Maxwell or geometric statement is
derived, and the correspondence with the printed display of `16.tex` is not checked (source not in
the repository).
-/

noncomputable section

open scoped ENNReal NNReal InnerProductSpace Topology
open MeasureTheory Set Filter

namespace Manuscript16.HolonomySemigroupGenerator20261128

open Manuscript16.V166L2SpectralInverse Manuscript16.HolonomyMomentSeries20261124
open Manuscript16.HolonomyCircleResolvent20261125 Manuscript16.HolonomyCircleGenerator20261125
open Manuscript16.HolonomyFunctionalCalculus20261127
open Manuscript16.RobinDirichletRealisation (realisation realisation_isSelfAdjoint
  mem_realisation_domain K_mem_domain realisation_sub_K K_realisation_sub)

-- The real algebra structure of `B(L²(S¹))` selected in #643 for Mathlib's continuous functional
-- calculus (restriction of scalars from `ℂ`), so that `cfc` below is the `cfc` of #643.
attribute [local instance high] Manuscript16.HolonomyFunctionalCalculus20261127.instAlgRealL2Circle

/-! ### Fourier coefficients and Parseval -/

/-- The Fourier coefficients of a multiplier: `(multiplier d u)^_n = d n û_n`. -/
theorem repr_multiplier (d : ℤ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hd : ∀ n, ‖d n‖ ≤ M)
    (u : L2Circle) (n : ℤ) :
    fourierONB.repr (multiplier d M hM hd u) n = d n * fourierONB.repr u n :=
  congrArg (fun v : L2 ℤ => (v : ℤ → ℂ) n) (multiplier_repr d M hM hd u)

/-- The Fourier coefficients of an element of `L²(S¹)` are square summable. -/
theorem summable_sq_repr (v : L2Circle) :
    Summable fun n : ℤ => ‖fourierONB.repr v n‖ ^ 2 := by
  have := fourierONB.orthonormal.inner_products_summable (x := v)
  simpa only [fourierONB.repr_apply_apply] using this

/-- Parseval: `‖v‖² = ∑_{n∈ℤ} |v̂_n|²`. -/
theorem norm_sq_eq_tsum (v : L2Circle) :
    ‖v‖ ^ 2 = ∑' n : ℤ, ‖fourierONB.repr v n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (fourierONB.repr v)
  rw [LinearIsometryEquiv.norm_map] at h
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

/-- Dominated convergence for weighted Fourier coefficient sums. -/
theorem tendsto_tsum_mul_sq {α : Type*} {l : Filter α} (c : α → ℤ → ℂ) (x : ℤ → ℂ) (w : ℤ → ℝ)
    (hw : Summable fun n => w n * ‖x n‖ ^ 2) (hb : ∀ᶠ t in l, ∀ n, ‖c t n‖ ^ 2 ≤ w n)
    (hc : ∀ n, Tendsto (fun t => c t n) l (𝓝 0)) :
    Tendsto (fun t => ∑' n, ‖c t n * x n‖ ^ 2) l (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := l) (f := fun t n => ‖c t n * x n‖ ^ 2)
    (g := fun _ => (0 : ℝ)) (bound := fun n => w n * ‖x n‖ ^ 2) hw ?_ ?_
  · simpa using h
  · intro n
    have : Tendsto (fun t => ‖c t n * x n‖ ^ 2) l (𝓝 (‖(0 : ℂ) * x n‖ ^ 2)) :=
      (((hc n).mul_const (x n)).norm).pow 2
    simpa using this
  · filter_upwards [hb] with t ht n
    rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (ht n) (sq_nonneg _)

/-- Convergence in `L²(S¹)` from convergence of the squared norms of the differences. -/
theorem tendsto_of_norm_sq {α : Type*} {l : Filter α} (F : α → L2Circle) (v : L2Circle)
    (h : Tendsto (fun t => ‖F t - v‖ ^ 2) l (𝓝 0)) : Tendsto F l (𝓝 v) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have := h.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

/-! ### Strong continuity of the semigroup -/

section Semigroup

variable (a φ : ℝ)

theorem repr_evanescent (t : ℝ≥0) (u : L2Circle) (n : ℤ) :
    fourierONB.repr (evanescent a φ t u) n = evanescentSymbol a φ t n * fourierONB.repr u n :=
  repr_multiplier _ _ _ _ u n

theorem evanescentSymbol_continuous (n : ℤ) :
    Continuous fun t : ℝ≥0 => evanescentSymbol a φ t n := by
  unfold evanescentSymbol
  exact Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp ((continuous_const.mul NNReal.continuous_coe).neg))

theorem evanescentSymbol_zero (n : ℤ) : evanescentSymbol a φ 0 n = 1 := by
  simp [evanescentSymbol]

theorem exp_mem_Icc (n : ℤ) (t : ℝ≥0) :
    0 < Real.exp (-(2 * Real.sqrt (circleEig a φ n) * t)) ∧
      Real.exp (-(2 * Real.sqrt (circleEig a φ n) * t)) ≤ 1 := by
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr ?_⟩
  have h1 := Real.sqrt_nonneg (circleEig a φ n)
  have h2 := t.2
  nlinarith

theorem evanescentSymbol_sub_norm_le (s t : ℝ≥0) (n : ℤ) :
    ‖evanescentSymbol a φ s n - evanescentSymbol a φ t n‖ ≤ 1 := by
  rw [evanescentSymbol, evanescentSymbol, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_le]
  obtain ⟨hs1, hs2⟩ := exp_mem_Icc a φ n s
  obtain ⟨ht1, ht2⟩ := exp_mem_Icc a φ n t
  constructor <;> linarith

/-- `e^{-2t√B}` is a contraction. -/
theorem evanescent_norm_le (t : ℝ≥0) : ‖evanescent a φ t‖ ≤ 1 :=
  multiplier_norm_le _ _ _ _

theorem norm_sq_evanescent_sub (s t : ℝ≥0) (u : L2Circle) :
    ‖evanescent a φ s u - evanescent a φ t u‖ ^ 2 =
      ∑' n, ‖(evanescentSymbol a φ s n - evanescentSymbol a φ t n) *
        fourierONB.repr u n‖ ^ 2 := by
  rw [norm_sq_eq_tsum]
  congr 1
  funext n
  rw [map_sub, lp.coeFn_sub, Pi.sub_apply, repr_evanescent, repr_evanescent, sub_mul]

/-- **Strong continuity.** For every `u ∈ L²(S¹)`, `t ↦ e^{-2t√B} u` is continuous on `[0, ∞)`. -/
theorem evanescent_continuous (u : L2Circle) : Continuous fun t : ℝ≥0 => evanescent a φ t u := by
  rw [continuous_iff_continuousAt]
  intro t₀
  apply tendsto_of_norm_sq
  simp_rw [norm_sq_evanescent_sub]
  refine tendsto_tsum_mul_sq _ _ (fun _ => 1) (by simpa using summable_sq_repr u) ?_ ?_
  · exact Eventually.of_forall (fun t n =>
      pow_le_one₀ (norm_nonneg _) (evanescentSymbol_sub_norm_le a φ t t₀ n))
  · intro n
    have := ((evanescentSymbol_continuous a φ n).tendsto t₀).sub_const (evanescentSymbol a φ t₀ n)
    simpa using this

/-- `e^{-2t√B} u → u` as `t → 0`. -/
theorem evanescent_tendsto_zero (u : L2Circle) :
    Tendsto (fun t : ℝ≥0 => evanescent a φ t u) (𝓝 0) (𝓝 u) := by
  have := (evanescent_continuous a φ u).tendsto 0
  simpa [evanescent_zero] using this

/-- `e^{-2t√B} - I` is the multiplier with symbol `e^{-2t√b_n} - 1`. -/
theorem evanescent_sub_id_mode (t : ℝ≥0) (n : ℤ) :
    (evanescent a φ t - ContinuousLinearMap.id ℂ L2Circle) (circleMode n) =
      (evanescentSymbol a φ t n - 1) • circleMode n := by
  rw [_root_.sub_apply, evanescent_mode, ContinuousLinearMap.id_apply, sub_smul,
    one_smul]

theorem norm_evanescent_sub_id_le (t : ℝ≥0) :
    ‖evanescent a φ t - ContinuousLinearMap.id ℂ L2Circle‖ ≤ 1 := by
  have hd : ∀ n, ‖evanescentSymbol a φ t n - 1‖ ≤ 1 := fun n => by
    simpa [evanescentSymbol_zero] using evanescentSymbol_sub_norm_le a φ t 0 n
  rw [multiplier_unique _ 1 zero_le_one hd _ (evanescent_sub_id_mode a φ t)]
  exact multiplier_norm_le _ _ _ _

theorem tendsto_sqrt_circleEig_atTop :
    Tendsto (fun k : ℕ => Real.sqrt (circleEig a φ k)) atTop atTop := by
  refine tendsto_atTop_mono (fun k => ?_) (tendsto_natCast_atTop_atTop.atTop_add
    (tendsto_const_nhds (x := -φ)))
  refine Real.le_sqrt_of_sq_le ?_
  unfold circleEig
  push_cast
  nlinarith [sq_nonneg a]

/-- `‖e^{-2t√B} - I‖ = 1` for every `t > 0`. -/
theorem norm_evanescent_sub_id (t : ℝ≥0) (ht : 0 < t) :
    ‖evanescent a φ t - ContinuousLinearMap.id ℂ L2Circle‖ = 1 := by
  refine le_antisymm (norm_evanescent_sub_id_le a φ t) ?_
  have hlow : ∀ k : ℕ, 1 - Real.exp (-(2 * Real.sqrt (circleEig a φ k) * t)) ≤
      ‖evanescent a φ t - ContinuousLinearMap.id ℂ L2Circle‖ := by
    intro k
    have h := (evanescent a φ t - ContinuousLinearMap.id ℂ L2Circle).le_opNorm (circleMode k)
    rw [evanescent_sub_id_mode, norm_smul, norm_circleMode, mul_one, mul_one, evanescentSymbol,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    obtain ⟨_, h2⟩ := exp_mem_Icc a φ k t
    rw [abs_of_nonpos (by linarith)] at h
    linarith
  have hlim : Tendsto (fun k : ℕ => 1 - Real.exp (-(2 * Real.sqrt (circleEig a φ k) * t)))
      atTop (𝓝 (1 - 0)) := by
    refine tendsto_const_nhds.sub ?_
    have ht' : (0 : ℝ) < 2 * t := by positivity
    have h1 : Tendsto (fun k : ℕ => 2 * Real.sqrt (circleEig a φ k) * t) atTop atTop := by
      have := (tendsto_sqrt_circleEig_atTop a φ).const_mul_atTop ht'
      refine this.congr (fun k => ?_)
      ring
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  rw [sub_zero] at hlim
  exact le_of_tendsto' hlim hlow

/-- The semigroup is not continuous in operator norm at `0`. -/
theorem evanescent_not_tendsto_norm :
    ¬ Tendsto (fun t : ℝ≥0 => evanescent a φ t) (𝓝 0)
      (𝓝 (ContinuousLinearMap.id ℂ L2Circle)) := by
  intro h
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  have h1 := h.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have h2 : Tendsto (fun t : ℝ≥0 => ‖evanescent a φ t - ContinuousLinearMap.id ℂ L2Circle‖)
      (𝓝[>] 0) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (norm_evanescent_sub_id a φ t ht).symm
  exact zero_ne_one (tendsto_nhds_unique h1 h2)

end Semigroup

/-! ### `√B := (cfc √· (B⁻¹))⁻¹` -/

theorem sqrt_circleEig_pos (a φ : ℝ) (ha : 0 < a) (n : ℤ) : 0 < Real.sqrt (circleEig a φ n) :=
  Real.sqrt_pos.mpr (circleEig_pos a φ ha n)

theorem le_sqrt_circleEig (a φ : ℝ) (n : ℤ) : a ≤ Real.sqrt (circleEig a φ n) :=
  Real.le_sqrt_of_sq_le (circleEig_ge a φ n)

/-- The symbol `n ↦ b_n^{-1/2}`. -/
def invSqrtSymbol (a φ : ℝ) (n : ℤ) : ℂ := (((Real.sqrt (circleEig a φ n))⁻¹ : ℝ) : ℂ)

theorem invSqrtSymbol_norm_le (a φ : ℝ) (ha : 0 < a) (n : ℤ) : ‖invSqrtSymbol a φ n‖ ≤ a⁻¹ := by
  rw [invSqrtSymbol, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact inv_anti₀ ha (le_sqrt_circleEig a φ n)

section SquareRoot

variable (a φ : ℝ) (ha : 0 < a)

/-- `(√B)⁻¹ = (B⁻¹)^{1/2}`, the square root of `B⁻¹` given by the continuous functional calculus. -/
def invSqrt : L2Circle →L[ℂ] L2Circle := cfc Real.sqrt (resolvent a φ ha)

/-- `cfc √· (B⁻¹)` is the Fourier multiplier with symbol `b_n^{-1/2}`. -/
theorem invSqrt_eq_multiplier :
    invSqrt a φ ha = multiplier (invSqrtSymbol a φ) a⁻¹ (inv_nonneg.mpr ha.le)
      (invSqrtSymbol_norm_le a φ ha) :=
  multiplier_unique _ _ _ _ _ (cfc_sqrt_resolvent_mode a φ ha)

theorem repr_invSqrt (u : L2Circle) (n : ℤ) :
    fourierONB.repr (invSqrt a φ ha u) n = invSqrtSymbol a φ n * fourierONB.repr u n := by
  rw [invSqrt_eq_multiplier]
  exact repr_multiplier _ _ _ _ u n

theorem invSqrt_isSelfAdjoint : IsSelfAdjoint (invSqrt a φ ha) := by
  rw [invSqrt_eq_multiplier]
  exact multiplier_isSelfAdjoint _ _ _ _ (fun _ => Complex.conj_ofReal _)

theorem invSqrt_injective : Function.Injective (invSqrt a φ ha) := by
  rw [invSqrt_eq_multiplier]
  exact multiplier_injective _ _ _ _ (fun n => by
    rw [invSqrtSymbol, Complex.ofReal_ne_zero]
    exact inv_ne_zero (sqrt_circleEig_pos a φ ha n).ne')

/-- **The operator `√B`**: the unbounded operator `(cfc √· (B⁻¹))⁻¹` on `L²(S¹)`, with graph
`{(invSqrt f, f)}` and domain `ran invSqrt`. -/
def sqrtGen : L2Circle →ₗ.[ℂ] L2Circle := realisation (invSqrt a φ ha) 0

/-- `√B` is self-adjoint. -/
theorem sqrtGen_isSelfAdjoint : IsSelfAdjoint (sqrtGen a φ ha) :=
  realisation_isSelfAdjoint (invSqrt_isSelfAdjoint a φ ha) (invSqrt_injective a φ ha)

theorem mem_sqrtGen_domain {u : L2Circle} :
    u ∈ (sqrtGen a φ ha).domain ↔ ∃ f, invSqrt a φ ha f = u :=
  mem_realisation_domain (invSqrt_injective a φ ha)

theorem invSqrt_mem_domain (f : L2Circle) : invSqrt a φ ha f ∈ (sqrtGen a φ ha).domain :=
  K_mem_domain (invSqrt_injective a φ ha) f

/-- `√B ((√B)⁻¹ f) = f`. -/
theorem sqrtGen_invSqrt (f : L2Circle) :
    sqrtGen a φ ha ⟨invSqrt a φ ha f, invSqrt_mem_domain a φ ha f⟩ = f := by
  have h := realisation_sub_K (t := 0) (invSqrt_injective a φ ha) f
  rw [Complex.ofReal_zero, zero_smul, sub_zero] at h
  exact h

/-- `(√B)⁻¹ (√B u) = u`. -/
theorem invSqrt_sqrtGen (u : (sqrtGen a φ ha).domain) :
    invSqrt a φ ha (sqrtGen a φ ha u) = u := by
  have h := K_realisation_sub (t := 0) (invSqrt_injective a φ ha) u
  rw [Complex.ofReal_zero, zero_smul, sub_zero] at h
  exact h

/-- The Fourier coefficients of `√B u` are `√b_n û_n`. -/
theorem repr_sqrtGen (u : (sqrtGen a φ ha).domain) (n : ℤ) :
    fourierONB.repr (sqrtGen a φ ha u) n =
      ((Real.sqrt (circleEig a φ n) : ℝ) : ℂ) * fourierONB.repr (u : L2Circle) n := by
  have h := congrArg (fun v => fourierONB.repr v n) (invSqrt_sqrtGen a φ ha u)
  simp only [repr_invSqrt] at h
  rw [← h, invSqrtSymbol, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (sqrt_circleEig_pos a φ ha n).ne', Complex.ofReal_one, one_mul]

/-- `u ∈ dom √B ⇔ ∑ b_n |û_n|² < ∞`. -/
theorem mem_sqrtGen_domain_iff (u : L2Circle) :
    u ∈ (sqrtGen a φ ha).domain ↔
      Summable fun n : ℤ => circleEig a φ n * ‖fourierONB.repr u n‖ ^ 2 := by
  rw [mem_sqrtGen_domain]
  constructor
  · rintro ⟨f, rfl⟩
    refine (summable_sq_repr f).congr (fun n => ?_)
    have hb := circleEig_pos a φ ha n
    rw [repr_invSqrt, norm_mul, invSqrtSymbol, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), mul_pow, ← mul_assoc, inv_pow,
      Real.sq_sqrt hb.le, mul_inv_cancel₀ hb.ne', one_mul]
  · intro hs
    have hw : Memℓp (fun n : ℤ => ((Real.sqrt (circleEig a φ n) : ℝ) : ℂ) *
        fourierONB.repr u n) 2 := by
      refine memℓp_gen ?_
      refine hs.congr (fun n => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        ENNReal.toReal_ofNat, Real.rpow_two, mul_pow,
        Real.sq_sqrt (circleEig_pos a φ ha n).le]
    refine ⟨fourierONB.repr.symm ⟨_, hw⟩, ext_repr (fun n => ?_)⟩
    rw [repr_invSqrt, LinearIsometryEquiv.apply_symm_apply]
    change invSqrtSymbol a φ n * (((Real.sqrt (circleEig a φ n) : ℝ) : ℂ) *
      fourierONB.repr u n) = _
    rw [invSqrtSymbol, ← mul_assoc, ← Complex.ofReal_mul,
      inv_mul_cancel₀ (sqrt_circleEig_pos a φ ha n).ne', Complex.ofReal_one, one_mul]

/-- The Sobolev space `H¹(S¹)` in Fourier form: `∑_{n∈ℤ} (1 + n²) |⟪e_n, u⟫|² < ∞`. -/
def H1Circle : Set L2Circle :=
  {u | Summable fun n : ℤ => (1 + (n : ℝ) ^ 2) * ‖⟪circleMode n, u⟫_ℂ‖ ^ 2}

/-- **`dom √B = H¹(S¹)`** (Fourier form of `H¹(S¹)`). -/
theorem sqrtGen_domain_eq : ((sqrtGen a φ ha).domain : Set L2Circle) = H1Circle := by
  ext u
  change u ∈ (sqrtGen a φ ha).domain ↔ u ∈ H1Circle
  rw [mem_sqrtGen_domain_iff]
  change _ ↔ Summable fun n : ℤ => (1 + (n : ℝ) ^ 2) * ‖⟪circleMode n, u⟫_ℂ‖ ^ 2
  simp only [repr_eq_inner]
  constructor
  · intro h
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (sq_nonneg _))
      (fun n => ?_) (h.mul_left ((2 * a ^ 2 + 1 + 2 * φ ^ 2) / a ^ 2))
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (one_add_sq_le a φ ha n) (sq_nonneg _)
  · intro h
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (circleEig_pos a φ ha n).le (sq_nonneg _))
      (fun n => ?_) (h.mul_left (2 + 2 * φ ^ 2 + a ^ 2))
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (circleEig_le a φ n) (sq_nonneg _)

/-- `√B` is bounded below by `a`: `Re ⟪u, √B u⟫ ≥ a ‖u‖²`. -/
theorem inner_sqrtGen_re (u : (sqrtGen a φ ha).domain) :
    a * ‖(u : L2Circle)‖ ^ 2 ≤ (⟪(u : L2Circle), sqrtGen a φ ha u⟫_ℂ).re := by
  have hterm : ∀ n, ⟪fourierONB.repr (u : L2Circle) n, fourierONB.repr (sqrtGen a φ ha u) n⟫_ℂ =
      ((Real.sqrt (circleEig a φ n) * ‖fourierONB.repr (u : L2Circle) n‖ ^ 2 : ℝ) : ℂ) := by
    intro n
    rw [repr_sqrtGen]
    have hsm : ((Real.sqrt (circleEig a φ n) : ℝ) : ℂ) * fourierONB.repr (u : L2Circle) n =
        ((Real.sqrt (circleEig a φ n) : ℝ) : ℂ) • fourierONB.repr (u : L2Circle) n := rfl
    rw [hsm, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp
  have hinner : ⟪(u : L2Circle), sqrtGen a φ ha u⟫_ℂ =
      ((∑' n, Real.sqrt (circleEig a φ n) * ‖fourierONB.repr (u : L2Circle) n‖ ^ 2 : ℝ) : ℂ) := by
    rw [← fourierONB.repr.inner_map_map, lp.inner_eq_tsum, Complex.ofReal_tsum]
    exact tsum_congr hterm
  have hs := (mem_sqrtGen_domain_iff a φ ha u).mp u.2
  have hs' : Summable fun n => Real.sqrt (circleEig a φ n) *
      ‖fourierONB.repr (u : L2Circle) n‖ ^ 2 := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (fun n => ?_) (hs.mul_left a⁻¹)
    have hb := circleEig_pos a φ ha n
    have hsq := Real.mul_self_sqrt hb.le
    have hle := le_sqrt_circleEig a φ n
    have h1 : Real.sqrt (circleEig a φ n) ≤ a⁻¹ * circleEig a φ n := by
      rw [inv_mul_eq_div, le_div_iff₀ ha]
      nlinarith [Real.sqrt_nonneg (circleEig a φ n)]
    calc Real.sqrt (circleEig a φ n) * ‖fourierONB.repr (u : L2Circle) n‖ ^ 2
        ≤ (a⁻¹ * circleEig a φ n) * ‖fourierONB.repr (u : L2Circle) n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = _ := by ring
  rw [hinner, Complex.ofReal_re, norm_sq_eq_tsum, ← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right (le_sqrt_circleEig a φ n) (sq_nonneg _))
    ((summable_sq_repr _).mul_left a) hs'

/-- `u ∈ dom B ⇔ ∑ b_n² |û_n|² < ∞` (#622). -/
theorem mem_generator_domain_iff_summable (u : L2Circle) :
    u ∈ (generator a φ ha).domain ↔
      Summable fun n : ℤ => (circleEig a φ n) ^ 2 * ‖fourierONB.repr u n‖ ^ 2 := by
  rw [mem_generator_domain, mem_range_resolvent_iff]

/-- `dom B ⊆ dom √B`. -/
theorem generator_domain_le : (generator a φ ha).domain ≤ (sqrtGen a φ ha).domain := by
  intro u hu
  rw [mem_generator_domain_iff_summable] at hu
  rw [mem_sqrtGen_domain_iff]
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (circleEig_pos a φ ha n).le (sq_nonneg _)) (fun n => ?_)
    (hu.mul_left (a ^ 2)⁻¹)
  have hb := circleEig_pos a φ ha n
  have hab := circleEig_ge a φ n
  have h1 : circleEig a φ n ≤ (a ^ 2)⁻¹ * circleEig a φ n ^ 2 := by
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith
  calc circleEig a φ n * ‖fourierONB.repr u n‖ ^ 2
      ≤ ((a ^ 2)⁻¹ * circleEig a φ n ^ 2) * ‖fourierONB.repr u n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = _ := by ring

/-- **`(√B)² = B`**: for `u ∈ dom B`, `√B u ∈ dom √B` and `√B (√B u) = B u`. -/
theorem sqrtGen_sq (u : (generator a φ ha).domain) :
    ∃ h : sqrtGen a φ ha ⟨u, generator_domain_le a φ ha u.2⟩ ∈ (sqrtGen a φ ha).domain,
      sqrtGen a φ ha ⟨_, h⟩ = generator a φ ha u := by
  have hmem : sqrtGen a φ ha ⟨u, generator_domain_le a φ ha u.2⟩ ∈ (sqrtGen a φ ha).domain := by
    rw [mem_sqrtGen_domain_iff]
    have hs := (mem_generator_domain_iff_summable a φ ha u).mp u.2
    refine hs.congr (fun n => ?_)
    rw [repr_sqrtGen, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt (circleEig_pos a φ ha n).le]
    ring
  refine ⟨hmem, ext_repr (fun n => ?_)⟩
  rw [repr_sqrtGen, repr_sqrtGen, repr_generator, ← mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (circleEig_pos a φ ha n).le]

/-- `dom B = {u ∈ dom √B : √B u ∈ dom √B}`. -/
theorem mem_generator_domain_iff_sqrt (u : L2Circle) :
    u ∈ (generator a φ ha).domain ↔
      ∃ h : u ∈ (sqrtGen a φ ha).domain, sqrtGen a φ ha ⟨u, h⟩ ∈ (sqrtGen a φ ha).domain := by
  constructor
  · intro hu
    exact ⟨generator_domain_le a φ ha hu, (sqrtGen_sq a φ ha ⟨u, hu⟩).1⟩
  · rintro ⟨h, h2⟩
    rw [mem_generator_domain_iff_summable]
    have hs := (mem_sqrtGen_domain_iff a φ ha _).mp h2
    refine hs.congr (fun n => ?_)
    rw [repr_sqrtGen, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt (circleEig_pos a φ ha n).le]
    ring

end SquareRoot

/-! ### The generator of `t ↦ e^{-2t√B}` is `-2√B` -/

section Generator

variable (a φ : ℝ)

/-- The difference quotient `t⁻¹ (e^{-2t√B} u - u)`. -/
def diffQuot (t : ℝ) (u : L2Circle) : L2Circle :=
  ((t⁻¹ : ℝ) : ℂ) • (evanescent a φ t.toNNReal u - u)

theorem repr_diffQuot {t : ℝ} (ht : 0 < t) (u : L2Circle) (n : ℤ) :
    fourierONB.repr (diffQuot a φ t u) n =
      ((t⁻¹ * (Real.exp (-(2 * Real.sqrt (circleEig a φ n) * t)) - 1) : ℝ) : ℂ) *
        fourierONB.repr u n := by
  rw [diffQuot, LinearIsometryEquiv.map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, map_sub,
    lp.coeFn_sub, Pi.sub_apply, repr_evanescent, evanescentSymbol, Real.coe_toNNReal t ht.le]
  push_cast
  ring

/-- For `s ≥ 0`, `t > 0`: `0 ≤ t⁻¹(e^{-2st} - 1) + 2s ≤ 2s`. -/
theorem slope_bound {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    0 ≤ t⁻¹ * (Real.exp (-(2 * s * t)) - 1) + 2 * s ∧
      t⁻¹ * (Real.exp (-(2 * s * t)) - 1) + 2 * s ≤ 2 * s := by
  have h1 := Real.add_one_le_exp (-(2 * s * t))
  have h2 : Real.exp (-(2 * s * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have htinv : 0 < t⁻¹ := inv_pos.mpr ht
  have hid : t⁻¹ * (Real.exp (-(2 * s * t)) - 1) + 2 * s =
      t⁻¹ * (Real.exp (-(2 * s * t)) - 1 + 2 * s * t) := by
    field_simp
  constructor
  · rw [hid]
    exact mul_nonneg htinv.le (by linarith)
  · have h3 : t⁻¹ * (Real.exp (-(2 * s * t)) - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos htinv.le (by linarith)
    linarith

/-- `t⁻¹ (e^{-2st} - 1) → -2s` as `t ↓ 0`. -/
theorem tendsto_slope (s : ℝ) :
    Tendsto (fun t : ℝ => t⁻¹ * (Real.exp (-(2 * s * t)) - 1)) (𝓝[>] 0) (𝓝 (-(2 * s))) := by
  have h : HasDerivAt (fun t : ℝ => Real.exp (-(2 * s * t))) (Real.exp (-(2 * s * 0)) *
      (-(2 * s * 1))) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_mul (2 * s)).neg.exp
  have := h.tendsto_slope_zero_right
  simpa using this

/-- For `u ∈ dom √B`: `t⁻¹ (e^{-2t√B} u - u) → -2√B u` as `t ↓ 0`. -/
theorem tendsto_diffQuot (ha : 0 < a) (u : (sqrtGen a φ ha).domain) :
    Tendsto (fun t : ℝ => diffQuot a φ t u) (𝓝[>] 0)
      (𝓝 (-(2 : ℂ) • sqrtGen a φ ha u)) := by
  apply tendsto_of_norm_sq
  set c : ℝ → ℤ → ℂ := fun t n =>
    ((t⁻¹ * (Real.exp (-(2 * Real.sqrt (circleEig a φ n) * t)) - 1) +
      2 * Real.sqrt (circleEig a φ n) : ℝ) : ℂ) with hc
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ‖diffQuot a φ t u - -(2 : ℂ) • sqrtGen a φ ha u‖ ^ 2 =
        ∑' n, ‖c t n * fourierONB.repr (u : L2Circle) n‖ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [norm_sq_eq_tsum]
    congr 1
    funext n
    rw [map_sub, lp.coeFn_sub, Pi.sub_apply, repr_diffQuot a φ ht, LinearIsometryEquiv.map_smul,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, repr_sqrtGen, hc]
    push_cast
    ring_nf
  refine (tendsto_congr' hev).mpr ?_
  refine tendsto_tsum_mul_sq c _ (fun n => 4 * circleEig a φ n) ?_ ?_ ?_
  · have := ((mem_sqrtGen_domain_iff a φ ha u).mp u.2).mul_left 4
    refine this.congr (fun n => ?_)
    ring
  · filter_upwards [self_mem_nhdsWithin] with t ht n
    obtain ⟨h1, h2⟩ := slope_bound (Real.sqrt_nonneg (circleEig a φ n)) ht
    rw [hc, Complex.norm_real, Real.norm_of_nonneg h1]
    calc _ ≤ (2 * Real.sqrt (circleEig a φ n)) ^ 2 := pow_le_pow_left₀ h1 h2 2
      _ = 4 * circleEig a φ n := by
        rw [mul_pow, Real.sq_sqrt (circleEig_pos a φ ha n).le]
        norm_num
  · intro n
    have h := ((tendsto_slope (Real.sqrt (circleEig a φ n))).add_const
      (2 * Real.sqrt (circleEig a φ n)))
    rw [neg_add_cancel] at h
    have h' := (Complex.continuous_ofReal.tendsto _).comp h
    simpa [hc, Function.comp_def] using h'

/-- Conversely, if `t⁻¹ (e^{-2t√B} u - u)` converges as `t ↓ 0`, then `u ∈ dom √B` and the limit is
`-2√B u`. -/
theorem mem_sqrtGen_domain_of_tendsto (ha : 0 < a) (u v : L2Circle)
    (h : Tendsto (fun t : ℝ => diffQuot a φ t u) (𝓝[>] 0) (𝓝 v)) :
    ∃ hu : u ∈ (sqrtGen a φ ha).domain, v = -(2 : ℂ) • sqrtGen a φ ha ⟨u, hu⟩ := by
  have hcoef : ∀ n, fourierONB.repr v n =
      ((-(2 * Real.sqrt (circleEig a φ n)) : ℝ) : ℂ) * fourierONB.repr u n := by
    intro n
    have hcont : Continuous fun w : L2Circle => fourierONB.repr w n := by
      simp_rw [repr_eq_inner]
      exact continuous_const.inner continuous_id
    have h1 : Tendsto (fun t : ℝ => fourierONB.repr (diffQuot a φ t u) n) (𝓝[>] 0)
        (𝓝 (fourierONB.repr v n)) := (hcont.tendsto v).comp h
    have h2 : Tendsto (fun t : ℝ => fourierONB.repr (diffQuot a φ t u) n) (𝓝[>] 0)
        (𝓝 (((-(2 * Real.sqrt (circleEig a φ n)) : ℝ) : ℂ) * fourierONB.repr u n)) := by
      have := ((Complex.continuous_ofReal.tendsto _).comp
        (tendsto_slope (Real.sqrt (circleEig a φ n)))).mul_const (fourierONB.repr u n)
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [repr_diffQuot a φ ht]
      rfl
    exact tendsto_nhds_unique h1 h2
  have hs : Summable fun n : ℤ => circleEig a φ n * ‖fourierONB.repr u n‖ ^ 2 := by
    have := (summable_sq_repr v).mul_left (1 / 4)
    refine this.congr (fun n => ?_)
    rw [hcoef, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq, mul_pow,
      Real.sq_sqrt (circleEig_pos a φ ha n).le]
    ring
  have hu := (mem_sqrtGen_domain_iff a φ ha u).mpr hs
  refine ⟨hu, ext_repr (fun n => ?_)⟩
  rw [hcoef, LinearIsometryEquiv.map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    repr_sqrtGen]
  push_cast
  ring

/-- **The generator of `t ↦ e^{-2t√B}` is `-2√B`.** For `u, v ∈ L²(S¹)`:
`t⁻¹ (e^{-2t√B} u - u) → v` as `t ↓ 0` iff `u ∈ dom √B = H¹(S¹)` and `v = -2√B u`. -/
theorem generator_iff (ha : 0 < a) (u v : L2Circle) :
    Tendsto (fun t : ℝ => diffQuot a φ t u) (𝓝[>] 0) (𝓝 v) ↔
      ∃ hu : u ∈ (sqrtGen a φ ha).domain, v = -(2 : ℂ) • sqrtGen a φ ha ⟨u, hu⟩ := by
  constructor
  · exact mem_sqrtGen_domain_of_tendsto a φ ha u v
  · rintro ⟨hu, rfl⟩
    exact tendsto_diffQuot a φ ha ⟨u, hu⟩

/-- The generator `-2√B` as an unbounded operator on `L²(S¹)`. -/
def semigroupGen (ha : 0 < a) : L2Circle →ₗ.[ℂ] L2Circle := (-(2 : ℂ)) • sqrtGen a φ ha

/-- `semigroupGen` is the generator of `t ↦ e^{-2t√B}` in the sense of `C₀`-semigroups: its graph is
`{(u, v) : t⁻¹ (e^{-2t√B} u - u) → v as t ↓ 0}`. -/
theorem semigroupGen_iff (ha : 0 < a) (u v : L2Circle) :
    Tendsto (fun t : ℝ => diffQuot a φ t u) (𝓝[>] 0) (𝓝 v) ↔
      ∃ hu : u ∈ (semigroupGen a φ ha).domain, semigroupGen a φ ha ⟨u, hu⟩ = v := by
  rw [generator_iff a φ ha]
  constructor
  · rintro ⟨hu, rfl⟩
    exact ⟨hu, rfl⟩
  · rintro ⟨hu, rfl⟩
    exact ⟨hu, rfl⟩

end Generator

/-! ### Manuscript form -/

/-- **`eq:hol-integral`, the evanescent semigroup.** For `a > 0` and real `φ`, on `L²(S¹)`:
`e^{-2t√B}` (`t ≥ 0`) is a strongly continuous contraction semigroup, not continuous in operator
norm at `0`, equal to `cfc (evGen t) (B⁻¹)` for `t > 0`; its generator is `-2√B`, where
`√B = (cfc √· (B⁻¹))⁻¹` is self-adjoint, bounded below by `a`, with `dom √B = H¹(S¹)` and
`(√B)² = B`. -/
theorem hol_semigroup_generator (a φ : ℝ) (ha : 0 < a) :
    evanescent a φ 0 = ContinuousLinearMap.id ℂ L2Circle ∧
    (∀ s t : ℝ≥0, evanescent a φ (s + t) = (evanescent a φ s).comp (evanescent a φ t)) ∧
    (∀ t : ℝ≥0, ‖evanescent a φ t‖ ≤ 1) ∧
    (∀ u : L2Circle, Continuous fun t : ℝ≥0 => evanescent a φ t u) ∧
    (∀ t : ℝ≥0, 0 < t → ‖evanescent a φ t - ContinuousLinearMap.id ℂ L2Circle‖ = 1) ∧
    (∀ t : ℝ≥0, 0 < (t : ℝ) → evanescent a φ t = cfc (evGen t) (resolvent a φ ha)) ∧
    invSqrt a φ ha = cfc Real.sqrt (resolvent a φ ha) ∧
    IsSelfAdjoint (sqrtGen a φ ha) ∧
    ((sqrtGen a φ ha).domain : Set L2Circle) = H1Circle ∧
    (∀ u : (sqrtGen a φ ha).domain,
      a * ‖(u : L2Circle)‖ ^ 2 ≤ (⟪(u : L2Circle), sqrtGen a φ ha u⟫_ℂ).re) ∧
    (∀ u : L2Circle, u ∈ (generator a φ ha).domain ↔
      ∃ h : u ∈ (sqrtGen a φ ha).domain, sqrtGen a φ ha ⟨u, h⟩ ∈ (sqrtGen a φ ha).domain) ∧
    (∀ u : (generator a φ ha).domain,
      ∃ h : sqrtGen a φ ha ⟨u, generator_domain_le a φ ha u.2⟩ ∈ (sqrtGen a φ ha).domain,
        sqrtGen a φ ha ⟨_, h⟩ = generator a φ ha u) ∧
    (∀ u v : L2Circle, Tendsto (fun t : ℝ => diffQuot a φ t u) (𝓝[>] 0) (𝓝 v) ↔
      ∃ hu : u ∈ (sqrtGen a φ ha).domain, v = -(2 : ℂ) • sqrtGen a φ ha ⟨u, hu⟩) :=
  ⟨evanescent_zero a φ, evanescent_add a φ, evanescent_norm_le a φ, evanescent_continuous a φ,
    norm_evanescent_sub_id a φ, fun t ht => evanescent_eq_cfc a φ ha t ht, rfl,
    sqrtGen_isSelfAdjoint a φ ha, sqrtGen_domain_eq a φ ha, inner_sqrtGen_re a φ ha,
    mem_generator_domain_iff_sqrt a φ ha, sqrtGen_sq a φ ha, generator_iff a φ ha⟩

end Manuscript16.HolonomySemigroupGenerator20261128

end

#print axioms Manuscript16.HolonomySemigroupGenerator20261128.repr_multiplier
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.summable_sq_repr
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.norm_sq_eq_tsum
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.tendsto_tsum_mul_sq
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.tendsto_of_norm_sq
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.repr_evanescent
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.evanescentSymbol_continuous
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.evanescentSymbol_zero
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.exp_mem_Icc
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.evanescentSymbol_sub_norm_le
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.evanescent_norm_le
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.norm_sq_evanescent_sub
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.evanescent_continuous
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.evanescent_tendsto_zero
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.evanescent_sub_id_mode
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.norm_evanescent_sub_id_le
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.tendsto_sqrt_circleEig_atTop
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.norm_evanescent_sub_id
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.evanescent_not_tendsto_norm
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.sqrt_circleEig_pos
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.le_sqrt_circleEig
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.invSqrtSymbol
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.invSqrtSymbol_norm_le
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.invSqrt
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.invSqrt_eq_multiplier
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.repr_invSqrt
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.invSqrt_isSelfAdjoint
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.invSqrt_injective
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.sqrtGen
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.sqrtGen_isSelfAdjoint
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.mem_sqrtGen_domain
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.invSqrt_mem_domain
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.sqrtGen_invSqrt
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.invSqrt_sqrtGen
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.repr_sqrtGen
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.mem_sqrtGen_domain_iff
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.H1Circle
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.sqrtGen_domain_eq
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.inner_sqrtGen_re
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.mem_generator_domain_iff_summable
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.generator_domain_le
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.sqrtGen_sq
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.mem_generator_domain_iff_sqrt
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.diffQuot
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.repr_diffQuot
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.slope_bound
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.tendsto_slope
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.tendsto_diffQuot
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.mem_sqrtGen_domain_of_tendsto
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.generator_iff
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.semigroupGen
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.semigroupGen_iff
#print axioms Manuscript16.HolonomySemigroupGenerator20261128.hol_semigroup_generator
