import Mathlib
import Manuscript16.HolonomyCircleResolvent20261125
import Manuscript16.RobinDirichletRealisation20261125

/-!
# M16 §14.5 `eq:hol-integral`: the self-adjoint operator `B = (D - φ)² + a²` on `L²(S¹)` with Fourier domain `H²(S¹)`

`HolonomyCircleResolvent20261125` (#599, merged) builds on `L²(S¹)`, `S¹ = ℝ/2πℤ` with
normalised Haar measure, the bounded operator `resolvent a φ` (Fourier multiplier with symbol
`1/b_n`, `b_n = (n - φ)² + a²`, `a > 0`, `φ` real) and lists as not claimed "the self-adjoint
realisation of the unbounded operator `B = (D - φ)² + a²` on its domain `H²(S¹)` and the identity
`resolvent = B⁻¹` as the inverse of that unbounded operator" (`D = -i d/dθ`). This file proves it.

* `generator a φ`: the unbounded operator `B = resolvent⁻¹` on `L²(S¹)` (a Mathlib `LinearPMap`),
  with graph `{(resolvent f, f)}`, built with the merged abstract construction
  `RobinDirichletRealisation.realisation` (#611, `t + K⁻¹` for `K` bounded, self-adjoint, injective;
  here `t = 0`), not re-proved.
* `generator_isSelfAdjoint`: `B` is self-adjoint (`IsSelfAdjoint`, i.e. equal to its
  `LinearPMap.adjoint`, with dense domain).
* `generator_domain_eq`: **`dom B = H²(S¹)`**, where `H2Circle` is the Sobolev space `H²(S¹)` in its
  Fourier form `∑_{n∈ℤ} (1 + n²)² |⟪e_n, u⟫|² < ∞` (`e_n(θ) = e^{inθ}`).
* `generator_resolvent`, `resolvent_generator`: `B (resolvent f) = f` for every `f ∈ L²(S¹)` and
  `resolvent (B u) = u` for every `u ∈ dom B`, i.e. **`resolvent = B⁻¹`**.
* `inner_mode_generator`: `⟪e_n, B u⟫ = b_n ⟪e_n, u⟫` for every `u ∈ dom B`.
* `generator_mode`: `e_n ∈ dom B` and `B e_n = b_n e_n`; `generator_eigenvalue_iff`: the
  eigenvalues of `B` are exactly the numbers `b_n`, `n ∈ ℤ`.
* `generator_twistedOp`: for every `C²` function `u : ℝ → ℂ` of period `2π`, the class of `u` in
  `L²(S¹)` lies in `dom B` and **`B u = -u'' + 2iφ u' + (φ² + a²) u`**, i.e. `B` acts as the
  differential expression `(D - φ)² + a²` on every `C²` function on `S¹`, not only on the modes
  (proof: Fourier coefficients of derivatives, Mathlib `fourierCoeffOn_of_hasDerivAt`).
* `hol_integral_generator`: manuscript form, all of the above together.

Inputs used, not re-proved: the Fourier Hilbert basis of `L²(S¹)` and the formula for the Fourier
coefficients of a derivative (Mathlib); `resolvent` and its properties (#599); the abstract
self-adjointness of `t + K⁻¹` (#611).

Not claimed. `H2Circle` is the Fourier-coefficient definition of `H²(S¹)`; its equivalence with the
definition by weak derivatives is the classical characterisation of Sobolev spaces on the circle and
is not formalised. The trace-class membership of `resolvent` and the basis independence of
`∑_n ⟪e_n, resolvent e_n⟫` (Lidskii; Simon 2005) are not formalised (no Schatten classes in Mathlib
at the pinned commit). The operators `evanescent a φ t` of #599 remain Fourier multipliers; their
identification with `e^{-2t√B}` through a spectral theorem for unbounded operators is not claimed. No
statement about the holonomy of a specific Maxwell field, and no geometric statement, is derived.
-/

noncomputable section

open scoped ENNReal NNReal InnerProductSpace
open MeasureTheory Set Filter AddCircle

namespace Manuscript16.HolonomyCircleGenerator20261125

open Manuscript16.V166L2SpectralInverse Manuscript16.HolonomyMomentSeries20261124
open Manuscript16.HolonomyCircleResolvent20261125
open Manuscript16.RobinDirichletRealisation (realisation realisation_isSelfAdjoint
  mem_realisation_domain K_mem_domain realisation_sub_K K_realisation_sub)

/-! ### Fourier coefficients in `L²(S¹)` -/

theorem repr_eq_inner (u : L2Circle) (n : ℤ) :
    fourierONB.repr u n = ⟪circleMode n, u⟫_ℂ := by
  rw [fourierONB.repr_apply_apply, fourierONB_apply]

/-- An element of `L²(S¹)` is determined by its Fourier coefficients. -/
theorem ext_repr {u v : L2Circle} (h : ∀ n, fourierONB.repr u n = fourierONB.repr v n) :
    u = v := by
  apply fourierONB.repr.injective
  apply lp.ext
  funext n
  exact h n

/-- The Fourier coefficients of `resolvent f` are `b_n⁻¹ f̂_n`. -/
theorem repr_resolvent (a φ : ℝ) (ha : 0 < a) (f : L2Circle) (n : ℤ) :
    fourierONB.repr (resolvent a φ ha f) n =
      (((circleEig a φ n)⁻¹ : ℝ) : ℂ) * fourierONB.repr f n := by
  have h := multiplier_repr (resolventSymbol a φ) (a ^ 2)⁻¹ (by positivity)
    (resolventSymbol_norm_le a φ ha) f
  exact congrArg (fun v : L2 ℤ => (v : ℤ → ℂ) n) h

/-! ### The operator `B = resolvent⁻¹` -/

/-- **The operator `B = (D - φ)² + a²` on `L²(S¹)`**, `D = -i d/dθ`: the unbounded operator
`resolvent⁻¹`, with graph `{(resolvent f, f) : f ∈ L²(S¹)}` and domain `ran resolvent`. -/
def generator (a φ : ℝ) (ha : 0 < a) : L2Circle →ₗ.[ℂ] L2Circle :=
  realisation (resolvent a φ ha) 0

/-- `B` is self-adjoint. -/
theorem generator_isSelfAdjoint (a φ : ℝ) (ha : 0 < a) : IsSelfAdjoint (generator a φ ha) :=
  realisation_isSelfAdjoint (resolvent_isSelfAdjoint a φ ha) (resolvent_injective a φ ha)

theorem mem_generator_domain (a φ : ℝ) (ha : 0 < a) {u : L2Circle} :
    u ∈ (generator a φ ha).domain ↔ ∃ f, resolvent a φ ha f = u :=
  mem_realisation_domain (resolvent_injective a φ ha)

theorem resolvent_mem_domain (a φ : ℝ) (ha : 0 < a) (f : L2Circle) :
    resolvent a φ ha f ∈ (generator a φ ha).domain :=
  K_mem_domain (resolvent_injective a φ ha) f

/-- `B (resolvent f) = f` for every `f ∈ L²(S¹)`. -/
theorem generator_resolvent (a φ : ℝ) (ha : 0 < a) (f : L2Circle) :
    generator a φ ha ⟨resolvent a φ ha f, resolvent_mem_domain a φ ha f⟩ = f := by
  have h := realisation_sub_K (t := 0) (resolvent_injective a φ ha) f
  rw [Complex.ofReal_zero, zero_smul, sub_zero] at h
  exact h

/-- `resolvent (B u) = u` for every `u ∈ dom B`. -/
theorem resolvent_generator (a φ : ℝ) (ha : 0 < a) (u : (generator a φ ha).domain) :
    resolvent a φ ha (generator a φ ha u) = u := by
  have h := K_realisation_sub (t := 0) (resolvent_injective a φ ha) u
  rw [Complex.ofReal_zero, zero_smul, sub_zero] at h
  exact h

/-- The Fourier coefficients of `B u` are `b_n û_n`. -/
theorem repr_generator (a φ : ℝ) (ha : 0 < a) (u : (generator a φ ha).domain) (n : ℤ) :
    fourierONB.repr (generator a φ ha u) n =
      ((circleEig a φ n : ℝ) : ℂ) * fourierONB.repr (u : L2Circle) n := by
  have h := congrArg (fun v => fourierONB.repr v n) (resolvent_generator a φ ha u)
  simp only [repr_resolvent] at h
  rw [← h, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (circleEig_pos a φ ha n).ne',
    Complex.ofReal_one, one_mul]

/-- `⟪e_n, B u⟫ = b_n ⟪e_n, u⟫` for every `u ∈ dom B`. -/
theorem inner_mode_generator (a φ : ℝ) (ha : 0 < a) (u : (generator a φ ha).domain) (n : ℤ) :
    ⟪circleMode n, generator a φ ha u⟫_ℂ =
      ((circleEig a φ n : ℝ) : ℂ) * ⟪circleMode n, (u : L2Circle)⟫_ℂ := by
  rw [← repr_eq_inner, ← repr_eq_inner, repr_generator]

/-! ### The domain of `B` is `H²(S¹)` -/

/-- The Sobolev space `H²(S¹)` in Fourier form: `∑_{n∈ℤ} (1 + n²)² |⟪e_n, u⟫|² < ∞`. -/
def H2Circle : Set L2Circle :=
  {u | Summable fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ 2 * ‖⟪circleMode n, u⟫_ℂ‖ ^ 2}

theorem circleEig_le (a φ : ℝ) (n : ℤ) :
    circleEig a φ n ≤ (2 + 2 * φ ^ 2 + a ^ 2) * (1 + (n : ℝ) ^ 2) := by
  unfold circleEig
  nlinarith [sq_nonneg ((n : ℝ) + φ), sq_nonneg (n : ℝ), sq_nonneg φ, sq_nonneg a,
    mul_nonneg (sq_nonneg φ) (sq_nonneg (n : ℝ)), mul_nonneg (sq_nonneg a) (sq_nonneg (n : ℝ))]

theorem one_add_sq_le (a φ : ℝ) (ha : 0 < a) (n : ℤ) :
    1 + (n : ℝ) ^ 2 ≤ ((2 * a ^ 2 + 1 + 2 * φ ^ 2) / a ^ 2) * circleEig a φ n := by
  have ha2 : 0 < a ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ ha2]
  unfold circleEig
  nlinarith [sq_nonneg ((n : ℝ) - 2 * φ), sq_nonneg ((n : ℝ) - φ), sq_nonneg a, sq_nonneg φ,
    mul_nonneg (sq_nonneg a) (sq_nonneg ((n : ℝ) - 2 * φ)), mul_nonneg ha2.le ha2.le,
    mul_nonneg (sq_nonneg φ) (sq_nonneg ((n : ℝ) - φ)),
    mul_nonneg (sq_nonneg a) (sq_nonneg ((n : ℝ) - φ))]

/-- `∑ b_n² |û_n|² < ∞ ⇔ ∑ (1 + n²)² |û_n|² < ∞`. -/
theorem summable_circleEig_iff (a φ : ℝ) (ha : 0 < a) (u : L2Circle) :
    (Summable fun n : ℤ => (circleEig a φ n) ^ 2 * ‖fourierONB.repr u n‖ ^ 2) ↔
      Summable fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ 2 * ‖fourierONB.repr u n‖ ^ 2 := by
  constructor
  · intro h
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (sq_nonneg _))
      (fun n => ?_) (h.mul_left (((2 * a ^ 2 + 1 + 2 * φ ^ 2) / a ^ 2) ^ 2))
    have h1 := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (one_add_sq_le a φ ha n) 2)
      (sq_nonneg ‖fourierONB.repr u n‖)
    calc _ ≤ _ := h1
      _ = _ := by ring
  · intro h
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun n => ?_) (h.mul_left ((2 + 2 * φ ^ 2 + a ^ 2) ^ 2))
    have h1 := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (circleEig_pos a φ ha n).le (circleEig_le a φ n) 2)
      (sq_nonneg ‖fourierONB.repr u n‖)
    calc _ ≤ _ := h1
      _ = _ := by ring

/-- `u ∈ ran resolvent ⇔ ∑ b_n² |û_n|² < ∞`. -/
theorem mem_range_resolvent_iff (a φ : ℝ) (ha : 0 < a) (u : L2Circle) :
    (∃ f, resolvent a φ ha f = u) ↔
      Summable fun n : ℤ => (circleEig a φ n) ^ 2 * ‖fourierONB.repr u n‖ ^ 2 := by
  constructor
  · rintro ⟨f, rfl⟩
    have hs : Summable fun n : ℤ => ‖fourierONB.repr f n‖ ^ 2 := by
      have := fourierONB.orthonormal.inner_products_summable (x := f)
      simpa only [fourierONB.repr_apply_apply] using this
    refine hs.congr (fun n => ?_)
    have hb := (circleEig_pos a φ ha n).ne'
    rw [repr_resolvent, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (circleEig_pos a φ ha n).le), mul_pow, ← mul_assoc,
      ← mul_pow, mul_inv_cancel₀ hb, one_pow, one_mul]
  · intro hs
    have hw : Memℓp (fun n : ℤ => ((circleEig a φ n : ℝ) : ℂ) * fourierONB.repr u n) 2 := by
      refine memℓp_gen ?_
      refine hs.congr (fun n => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (circleEig_pos a φ ha n).le,
        ENNReal.toReal_ofNat, Real.rpow_two, mul_pow]
    refine ⟨fourierONB.repr.symm ⟨_, hw⟩, ext_repr (fun n => ?_)⟩
    rw [repr_resolvent, LinearIsometryEquiv.apply_symm_apply]
    change (((circleEig a φ n)⁻¹ : ℝ) : ℂ) * (((circleEig a φ n : ℝ) : ℂ) * fourierONB.repr u n) = _
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (circleEig_pos a φ ha n).ne',
      Complex.ofReal_one, one_mul]

/-- **`dom B = H²(S¹)`** (Fourier form of `H²(S¹)`). -/
theorem generator_domain_eq (a φ : ℝ) (ha : 0 < a) :
    ((generator a φ ha).domain : Set L2Circle) = H2Circle := by
  ext u
  change u ∈ (generator a φ ha).domain ↔ u ∈ H2Circle
  rw [mem_generator_domain, mem_range_resolvent_iff, summable_circleEig_iff a φ ha u]
  change _ ↔ Summable fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ 2 * ‖⟪circleMode n, u⟫_ℂ‖ ^ 2
  simp only [repr_eq_inner]

/-! ### Modes and eigenvalues -/

theorem circleMode_mem_domain (a φ : ℝ) (ha : 0 < a) (n : ℤ) :
    circleMode n ∈ (generator a φ ha).domain :=
  (mem_generator_domain a φ ha).mpr ⟨_, resolvent_inverts_on_mode a φ ha n⟩

/-- `B e_n = b_n e_n`. -/
theorem generator_mode (a φ : ℝ) (ha : 0 < a) (n : ℤ) :
    generator a φ ha ⟨circleMode n, circleMode_mem_domain a φ ha n⟩ =
      ((circleEig a φ n : ℝ) : ℂ) • circleMode n := by
  have he : (⟨circleMode n, circleMode_mem_domain a φ ha n⟩ : (generator a φ ha).domain) =
      ⟨resolvent a φ ha (((circleEig a φ n : ℝ) : ℂ) • circleMode n),
        resolvent_mem_domain a φ ha _⟩ :=
    Subtype.ext (resolvent_inverts_on_mode a φ ha n).symm
  rw [he, generator_resolvent]

/-- The eigenvalues of `B` are exactly the numbers `b_n = (n - φ)² + a²`, `n ∈ ℤ`. -/
theorem generator_eigenvalue_iff (a φ : ℝ) (ha : 0 < a) (μ : ℂ) :
    (∃ u : (generator a φ ha).domain,
        (u : L2Circle) ≠ 0 ∧ generator a φ ha u = μ • (u : L2Circle)) ↔
      ∃ n : ℤ, μ = ((circleEig a φ n : ℝ) : ℂ) := by
  constructor
  · rintro ⟨u, hu0, hu⟩
    have hex : ∃ n, fourierONB.repr (u : L2Circle) n ≠ 0 := by
      by_contra hcon
      apply hu0
      refine ext_repr (fun n => ?_)
      have hn : fourierONB.repr (u : L2Circle) n = 0 := by
        by_contra hne
        exact hcon ⟨n, hne⟩
      simp [hn]
    obtain ⟨n, hn⟩ := hex
    refine ⟨n, ?_⟩
    have h1 := repr_generator a φ ha u n
    rw [hu, LinearIsometryEquiv.map_smul] at h1
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at h1
    exact mul_right_cancel₀ hn h1
  · rintro ⟨n, rfl⟩
    refine ⟨⟨circleMode n, circleMode_mem_domain a φ ha n⟩, ?_, generator_mode a φ ha n⟩
    rw [← norm_ne_zero_iff, norm_circleMode]
    exact one_ne_zero

/-! ### `B` on `C²` functions on `S¹` -/

/-- `0 < 0 + 2π`: the interval `[0, 2π]` on which the Fourier coefficients are computed. -/
theorem zero_lt_two_pi' : (0 : ℝ) < 0 + 2 * Real.pi := lt_add_of_pos_right 0 Real.two_pi_pos

/-- The continuous function on `S¹ = ℝ/2πℤ` induced by a continuous `2π`-periodic `u : ℝ → ℂ`. -/
def liftC (u : ℝ → ℂ) (hc : Continuous u) (hp : Function.Periodic u (2 * Real.pi)) :
    C(AddCircle (2 * Real.pi), ℂ) :=
  ⟨AddCircle.liftIco (2 * Real.pi) 0 u, AddCircle.liftIco_continuous (hp 0).symm hc.continuousOn⟩

/-- `liftC u` takes the value `u θ` at the class of `θ`. -/
theorem liftC_coe (u : ℝ → ℂ) (hc : Continuous u) (hp : Function.Periodic u (2 * Real.pi))
    (θ : ℝ) : liftC u hc hp (θ : AddCircle (2 * Real.pi)) = u θ := by
  have hmem := toIcoMod_mem_Ico Real.two_pi_pos 0 θ
  have hcoe : ((toIcoMod Real.two_pi_pos 0 θ : ℝ) : AddCircle (2 * Real.pi)) =
      (θ : AddCircle (2 * Real.pi)) := by
    rw [← self_sub_toIcoDiv_zsmul Real.two_pi_pos 0 θ, QuotientAddGroup.mk_sub,
      QuotientAddGroup.mk_zsmul, AddCircle.coe_period, smul_zero, sub_zero]
  change AddCircle.liftIco (2 * Real.pi) 0 u (θ : AddCircle (2 * Real.pi)) = u θ
  rw [← hcoe, AddCircle.liftIco_coe_apply hmem, ← self_sub_toIcoDiv_zsmul Real.two_pi_pos 0 θ,
    hp.sub_zsmul_eq]

/-- The class in `L²(S¹)` of a continuous `2π`-periodic function `u : ℝ → ℂ`. -/
def liftL2 (u : ℝ → ℂ) (hc : Continuous u) (hp : Function.Periodic u (2 * Real.pi)) :
    L2Circle :=
  ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ (liftC u hc hp)

/-- The Fourier coefficients of the class of `u` are the coefficients of `u` on `[0, 2π]`. -/
theorem repr_liftL2 (u : ℝ → ℂ) (hc : Continuous u) (hp : Function.Periodic u (2 * Real.pi))
    (n : ℤ) : fourierONB.repr (liftL2 u hc hp) n = fourierCoeffOn zero_lt_two_pi' u n := by
  rw [fourierBasis_repr, liftL2, fourierCoeff_toLp]
  exact fourierCoeff_liftIco_eq u n

theorem periodic_deriv {u : ℝ → ℂ} (hp : Function.Periodic u (2 * Real.pi)) :
    Function.Periodic (deriv u) (2 * Real.pi) := by
  intro x
  rw [← deriv_comp_add_const, show (fun y => u (y + 2 * Real.pi)) = u from funext hp]

/-- `(u')^_n = i n û_n` for a `C¹` function `u` of period `2π`. -/
theorem fourierCoeffOn_deriv {u : ℝ → ℂ} (hd : Differentiable ℝ u) (hc : Continuous (deriv u))
    (hp : Function.Periodic u (2 * Real.pi)) (n : ℤ) :
    fourierCoeffOn zero_lt_two_pi' (deriv u) n =
      Complex.I * n * fourierCoeffOn zero_lt_two_pi' u n := by
  have hper : u (0 + 2 * Real.pi) - u 0 = 0 := by rw [hp 0, sub_self]
  by_cases hn : n = 0
  · subst hn
    rw [Int.cast_zero, mul_zero, zero_mul, fourierCoeffOn_eq_integral]
    simp only [neg_zero, fourier_zero, one_smul]
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => hd x) (hc.intervalIntegrable _ _), hper,
      smul_zero]
  · have h := fourierCoeffOn_of_hasDerivAt zero_lt_two_pi' hn (fun x _ => (hd x).hasDerivAt)
      (hc.intervalIntegrable _ _)
    rw [hper, mul_zero, zero_sub] at h
    rw [h]
    have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    push_cast
    ring

theorem contDiff_two_aux {u : ℝ → ℂ} (hu : ContDiff ℝ 2 u) :
    Differentiable ℝ u ∧ Differentiable ℝ (deriv u) ∧ Continuous (deriv (deriv u)) := by
  have h := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) u from hu)
  have h1 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (0 + 1) (deriv u) from h.2.2)
  exact ⟨h.1, h1.1, h1.2.2.continuous⟩

theorem twistedOp_continuous (a φ : ℝ) {u : ℝ → ℂ} (hu : ContDiff ℝ 2 u) :
    Continuous (twistedOp a φ u) := by
  obtain ⟨h0, h1, h2⟩ := contDiff_two_aux hu
  have hc0 := h0.continuous
  have hc1 := h1.continuous
  unfold twistedOp
  fun_prop

theorem twistedOp_periodic (a φ : ℝ) {u : ℝ → ℂ} (hp : Function.Periodic u (2 * Real.pi)) :
    Function.Periodic (twistedOp a φ u) (2 * Real.pi) := by
  intro θ
  simp only [twistedOp]
  rw [hp θ, periodic_deriv hp θ, periodic_deriv (periodic_deriv hp) θ]

/-- The Fourier coefficients of `-u'' + 2iφu' + (φ² + a²)u` are `b_n û_n`. -/
theorem repr_liftL2_twistedOp (a φ : ℝ) {u : ℝ → ℂ} (hu : ContDiff ℝ 2 u)
    (hp : Function.Periodic u (2 * Real.pi)) (n : ℤ) :
    fourierONB.repr (liftL2 (twistedOp a φ u) (twistedOp_continuous a φ hu)
        (twistedOp_periodic a φ hp)) n =
      ((circleEig a φ n : ℝ) : ℂ) * fourierONB.repr (liftL2 u hu.continuous hp) n := by
  obtain ⟨h0, h1, h2⟩ := contDiff_two_aux hu
  have p1 := periodic_deriv hp
  have p2 := periodic_deriv p1
  have hL : liftC (twistedOp a φ u) (twistedOp_continuous a φ hu) (twistedOp_periodic a φ hp) =
      -liftC (deriv (deriv u)) h2 p2 + (2 * Complex.I * φ) • liftC (deriv u) h1.continuous p1 +
        ((φ ^ 2 + a ^ 2 : ℝ) : ℂ) • liftC u hu.continuous hp := by
    ext x
    rfl
  rw [liftL2, hL]
  simp only [map_add, map_neg, map_smul, lp.coeFn_add, lp.coeFn_neg, lp.coeFn_smul,
    Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  rw [← liftL2, ← liftL2, ← liftL2, repr_liftL2, repr_liftL2, repr_liftL2,
    fourierCoeffOn_deriv h1 h2 p1 n, fourierCoeffOn_deriv h0 h1.continuous hp n]
  unfold circleEig
  push_cast
  linear_combination
    (-(n : ℂ) ^ 2 * fourierCoeffOn zero_lt_two_pi' u n +
      2 * φ * n * fourierCoeffOn zero_lt_two_pi' u n) * Complex.I_sq

/-- **`B` acts as `(D - φ)² + a²` on `C²(S¹)`.** For every `C²` function `u : ℝ → ℂ` of period
`2π`, its class in `L²(S¹)` lies in `dom B` and `B u = -u'' + 2iφ u' + (φ² + a²) u`. -/
theorem generator_twistedOp (a φ : ℝ) (ha : 0 < a) {u : ℝ → ℂ} (hu : ContDiff ℝ 2 u)
    (hp : Function.Periodic u (2 * Real.pi)) :
    ∃ h : liftL2 u hu.continuous hp ∈ (generator a φ ha).domain,
      generator a φ ha ⟨liftL2 u hu.continuous hp, h⟩ =
        liftL2 (twistedOp a φ u) (twistedOp_continuous a φ hu) (twistedOp_periodic a φ hp) := by
  set G := liftL2 (twistedOp a φ u) (twistedOp_continuous a φ hu) (twistedOp_periodic a φ hp)
    with hG
  have hRG : resolvent a φ ha G = liftL2 u hu.continuous hp := by
    refine ext_repr (fun n => ?_)
    rw [repr_resolvent, hG, repr_liftL2_twistedOp a φ hu hp n, ← mul_assoc, ← Complex.ofReal_mul,
      inv_mul_cancel₀ (circleEig_pos a φ ha n).ne', Complex.ofReal_one, one_mul]
  have hdom : liftL2 u hu.continuous hp ∈ (generator a φ ha).domain :=
    (mem_generator_domain a φ ha).mpr ⟨G, hRG⟩
  refine ⟨hdom, ?_⟩
  have he : (⟨liftL2 u hu.continuous hp, hdom⟩ : (generator a φ ha).domain) =
      ⟨resolvent a φ ha G, resolvent_mem_domain a φ ha G⟩ := Subtype.ext hRG.symm
  rw [he, generator_resolvent]

/-! ### Manuscript form -/

/-- **M16 `eq:hol-integral`, the operator `B = (D - φ)² + a²` on `L²(S¹)`.** For `a > 0` and real
`φ`: `B` is self-adjoint; `dom B = H²(S¹)` (Fourier form); `resolvent = B⁻¹` on both sides;
`B e_n = b_n e_n`; the eigenvalues of `B` are exactly the `b_n = (n - φ)² + a²`; and `B` acts on
every `C²` function on `S¹` as the differential expression `-d²/dθ² + 2iφ d/dθ + φ² + a²`. -/
theorem hol_integral_generator (a φ : ℝ) (ha : 0 < a) :
    IsSelfAdjoint (generator a φ ha) ∧
    ((generator a φ ha).domain : Set L2Circle) = H2Circle ∧
    (∀ f : L2Circle, ∃ h : resolvent a φ ha f ∈ (generator a φ ha).domain,
        generator a φ ha ⟨resolvent a φ ha f, h⟩ = f) ∧
    (∀ u : (generator a φ ha).domain, resolvent a φ ha (generator a φ ha u) = u) ∧
    (∀ n : ℤ, ∃ h : circleMode n ∈ (generator a φ ha).domain,
        generator a φ ha ⟨circleMode n, h⟩ = ((circleEig a φ n : ℝ) : ℂ) • circleMode n) ∧
    (∀ μ : ℂ, (∃ u : (generator a φ ha).domain,
        (u : L2Circle) ≠ 0 ∧ generator a φ ha u = μ • (u : L2Circle)) ↔
      ∃ n : ℤ, μ = ((circleEig a φ n : ℝ) : ℂ)) ∧
    (∀ (u : ℝ → ℂ) (hu : ContDiff ℝ 2 u) (hp : Function.Periodic u (2 * Real.pi)),
      ∃ h : liftL2 u hu.continuous hp ∈ (generator a φ ha).domain,
        generator a φ ha ⟨liftL2 u hu.continuous hp, h⟩ =
          liftL2 (twistedOp a φ u) (twistedOp_continuous a φ hu) (twistedOp_periodic a φ hp)) :=
  ⟨generator_isSelfAdjoint a φ ha, generator_domain_eq a φ ha,
    fun f => ⟨resolvent_mem_domain a φ ha f, generator_resolvent a φ ha f⟩,
    resolvent_generator a φ ha,
    fun n => ⟨circleMode_mem_domain a φ ha n, generator_mode a φ ha n⟩,
    generator_eigenvalue_iff a φ ha,
    fun _ hu hp => generator_twistedOp a φ ha hu hp⟩

end Manuscript16.HolonomyCircleGenerator20261125

#print axioms Manuscript16.HolonomyCircleGenerator20261125.repr_eq_inner
#print axioms Manuscript16.HolonomyCircleGenerator20261125.ext_repr
#print axioms Manuscript16.HolonomyCircleGenerator20261125.repr_resolvent
#print axioms Manuscript16.HolonomyCircleGenerator20261125.generator_isSelfAdjoint
#print axioms Manuscript16.HolonomyCircleGenerator20261125.mem_generator_domain
#print axioms Manuscript16.HolonomyCircleGenerator20261125.resolvent_mem_domain
#print axioms Manuscript16.HolonomyCircleGenerator20261125.generator_resolvent
#print axioms Manuscript16.HolonomyCircleGenerator20261125.resolvent_generator
#print axioms Manuscript16.HolonomyCircleGenerator20261125.repr_generator
#print axioms Manuscript16.HolonomyCircleGenerator20261125.inner_mode_generator
#print axioms Manuscript16.HolonomyCircleGenerator20261125.circleEig_le
#print axioms Manuscript16.HolonomyCircleGenerator20261125.one_add_sq_le
#print axioms Manuscript16.HolonomyCircleGenerator20261125.summable_circleEig_iff
#print axioms Manuscript16.HolonomyCircleGenerator20261125.mem_range_resolvent_iff
#print axioms Manuscript16.HolonomyCircleGenerator20261125.generator_domain_eq
#print axioms Manuscript16.HolonomyCircleGenerator20261125.circleMode_mem_domain
#print axioms Manuscript16.HolonomyCircleGenerator20261125.generator_mode
#print axioms Manuscript16.HolonomyCircleGenerator20261125.generator_eigenvalue_iff
#print axioms Manuscript16.HolonomyCircleGenerator20261125.zero_lt_two_pi'
#print axioms Manuscript16.HolonomyCircleGenerator20261125.liftC_coe
#print axioms Manuscript16.HolonomyCircleGenerator20261125.repr_liftL2
#print axioms Manuscript16.HolonomyCircleGenerator20261125.periodic_deriv
#print axioms Manuscript16.HolonomyCircleGenerator20261125.fourierCoeffOn_deriv
#print axioms Manuscript16.HolonomyCircleGenerator20261125.contDiff_two_aux
#print axioms Manuscript16.HolonomyCircleGenerator20261125.twistedOp_continuous
#print axioms Manuscript16.HolonomyCircleGenerator20261125.twistedOp_periodic
#print axioms Manuscript16.HolonomyCircleGenerator20261125.repr_liftL2_twistedOp
#print axioms Manuscript16.HolonomyCircleGenerator20261125.generator_twistedOp
#print axioms Manuscript16.HolonomyCircleGenerator20261125.hol_integral_generator
