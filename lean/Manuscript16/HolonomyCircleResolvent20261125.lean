import Mathlib
import Manuscript16.V166L2SpectralInverse
import Manuscript16.DiracMaxwellCoefficientModel20261124
import Manuscript16.HolonomyMomentSeries20261124

/-!
# M16 v16.6 §14.5 `eq:hol-integral`: operator realisation on `L²(S¹)` of the circle resolvent

`HolonomyMomentSeries20261124` (#598) sums the explicit real sequence `b_n = (n - φ)² + a²`,
`n ∈ ℤ`, and states explicitly that it does not realise `b_n` as the spectrum of an operator.
`CERTIFICATION_SCOPE_20261117_V166_REACTIVE_HOLONOMY.md` lists for `eq:hol-integral` as remaining
"abstract spectral theorem, trace summability, Tonelli and operator realisation". This file
gives the operator realisation on the actual Hilbert space `L²(S¹)`, `S¹ = ℝ/2πℤ` with
normalised Haar measure, with the Fourier Hilbert basis `e_n(θ) = e^{inθ}` (Mathlib
`fourierBasis`, `F : L²(S¹) ≃ₗᵢ ℓ²(ℤ)`).

* `multiplier d`: for a bounded symbol `d : ℤ → ℂ`, the bounded operator `F⁻¹ ∘ diag(d) ∘ F` on
  `L²(S¹)` (`diag` is the merged `V166L2SpectralInverse.diagonal`); `multiplier_mode`:
  `multiplier d e_n = d n • e_n`; `inner_mode_multiplier`: its matrix in the Fourier basis is
  diagonal; `multiplier_unique`: it is the only bounded operator with these eigenvectors
  (density of trigonometric polynomials, Mathlib `span_fourierLp_closure_eq_top`);
  `multiplier_isSelfAdjoint` (real symbol), `multiplier_injective` (nonvanishing symbol),
  `multiplier_isCompactOperator` (symbol tending to zero, through the merged
  `DiracMaxwellCoefficientModel20261124.diagonal_isCompactOperator`), norm bounds.
* `resolvent a φ`: the multiplier with symbol `1/b_n`, `a > 0`, `φ` real. It is a bounded,
  self-adjoint, injective, compact operator on `L²(S¹)` with `resolvent e_n = b_n⁻¹ • e_n`,
  `‖resolvent‖ ≤ 1/a²` (equality for `φ = 0`).
* `twistedOp_modeFun`: the differential expression `(D - φ)² + a² = -d²/dθ² + 2iφ d/dθ + φ² + a²`
  (`D = -i d/dθ`) acts on the actual function `θ ↦ e^{inθ}` (the lift to `ℝ` of `fourier n`,
  whose `L²` class is `e_n`) as multiplication by `b_n`; hence `resolvent` inverts
  `(D - φ)² + a²` on every Fourier mode.
* `resolvent_diagonal_hasSum`: `∑_{n∈ℤ} ⟪e_n, resolvent e_n⟫ = (π/a) sinh(2πa)/(cosh 2πa - cos 2πφ)`.
* `evanescent a φ t` (`t ≥ 0`): the multiplier with symbol `e^{-2t√b_n}`, i.e. `e^{-2t√B}` for
  `B = (D - φ)² + a²` in the Fourier diagonalisation; `evanescent_zero`, `evanescent_add`
  (semigroup law); `evanescent_diagonal_integral`:
  `∫₀^∞ z ∑_{n∈ℤ} ⟪e_n, e^{-2z√B} e_n⟫ dz = momentClosed a (πa) (cos 2πφ)`;
  `resolvent_diagonal_eq_four_integral`: `∑_n ⟪e_n, resolvent e_n⟫ = 4 ∫₀^∞ z ∑_n ⟪e_n, e^{-2z√B} e_n⟫ dz`.

Inputs used, not re-proved: the Fourier Hilbert basis of `L²(S¹)` and the density of
trigonometric polynomials (Mathlib), the closed forms of #598 (Mittag-Leffler expansion of the
cotangent, interchange of sum and integral).

Not claimed. The self-adjoint realisation of the unbounded operator `(D - φ)² + a²` on its
domain `H²(S¹)` and the identity `resolvent = ((D - φ)² + a²)⁻¹` as an inverse of that unbounded
operator are not formalised: the link with the differential expression is proved mode by mode
(`twistedOp_modeFun`, `resolvent_mode`) and the operator is characterised by its action on the
Fourier basis (`multiplier_unique`). The sums `∑_n ⟪e_n, T e_n⟫` are diagonal sums in the Fourier
basis; trace-class membership and basis independence of the trace (Lidskii; Simon 2005) are not
formalised (no Schatten classes in Mathlib at the pinned commit). No geometric statement about the
holonomy of a specific Maxwell field is derived.
-/

noncomputable section

open scoped ENNReal NNReal InnerProductSpace
open MeasureTheory Set Filter AddCircle

namespace Manuscript16.HolonomyCircleResolvent20261125

open Manuscript16.V166L2SpectralInverse Manuscript16.DiracMaxwellCoefficientModel20261124
open Manuscript16.HolonomyMomentSeries20261124 Manuscript16.ReactiveHolonomy

/-- The circle `S¹ = ℝ/2πℤ` has positive period. -/
instance fact_two_pi_pos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- `L²(S¹)`, `S¹ = ℝ/2πℤ`, normalised Haar measure. -/
abbrev L2Circle : Type := Lp ℂ 2 (@haarAddCircle (2 * Real.pi) _)

/-- The Fourier Hilbert basis `e_n(θ) = e^{inθ}` of `L²(S¹)` (Mathlib `fourierBasis`). -/
abbrev fourierONB : HilbertBasis ℤ ℂ L2Circle := @fourierBasis (2 * Real.pi) _

/-- The Fourier mode `e_n` as an element of `L²(S¹)`. -/
abbrev circleMode (n : ℤ) : L2Circle := @fourierLp (2 * Real.pi) _ 2 _ n

theorem fourierONB_apply (n : ℤ) : fourierONB n = circleMode n := by
  simp [fourierONB, circleMode]

theorem inner_circleMode (m n : ℤ) :
    ⟪circleMode m, circleMode n⟫_ℂ = if m = n then 1 else 0 := by
  classical
  exact orthonormal_iff_ite.mp (orthonormal_fourier (T := 2 * Real.pi)) m n

theorem norm_circleMode (n : ℤ) : ‖circleMode n‖ = 1 :=
  (orthonormal_fourier (T := 2 * Real.pi)).1 n

/-! ### Fourier multipliers on `L²(S¹)` -/

section Multiplier

variable (d : ℤ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hd : ∀ n, ‖d n‖ ≤ M)

/-- The Fourier multiplier with bounded symbol `d`: `F⁻¹ ∘ diag(d) ∘ F`. -/
def multiplier : L2Circle →L[ℂ] L2Circle :=
  (fourierONB.repr.symm.toLinearIsometry.toContinuousLinearMap).comp
    ((diagonal d M hM hd).comp fourierONB.repr.toLinearIsometry.toContinuousLinearMap)

theorem multiplier_apply (x : L2Circle) :
    multiplier d M hM hd x = fourierONB.repr.symm (diagonal d M hM hd (fourierONB.repr x)) :=
  rfl

theorem multiplier_repr (x : L2Circle) :
    fourierONB.repr (multiplier d M hM hd x) = diagonal d M hM hd (fourierONB.repr x) := by
  rw [multiplier_apply, LinearIsometryEquiv.apply_symm_apply]

theorem diagonal_single (n : ℤ) :
    diagonal d M hM hd (lp.single 2 n (1 : ℂ)) = d n • lp.single 2 n (1 : ℂ) := by
  apply lp.ext
  funext j
  change d j * (lp.single 2 n (1 : ℂ) : L2 ℤ) j = d n * (lp.single 2 n (1 : ℂ) : L2 ℤ) j
  by_cases hj : j = n
  · subst hj
    rfl
  · rw [lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ) hj, mul_zero, mul_zero]

/-- The Fourier modes are eigenvectors: `multiplier d e_n = d n • e_n`. -/
theorem multiplier_mode (n : ℤ) :
    multiplier d M hM hd (circleMode n) = d n • circleMode n := by
  classical
  apply fourierONB.repr.injective
  rw [multiplier_repr, ← fourierONB_apply, fourierONB.repr_self, diagonal_single,
    LinearIsometryEquiv.map_smul, fourierONB.repr_self]

/-- The matrix of `multiplier d` in the Fourier basis is `diag(d)`. -/
theorem inner_mode_multiplier (m n : ℤ) :
    ⟪circleMode m, multiplier d M hM hd (circleMode n)⟫_ℂ = if m = n then d n else 0 := by
  rw [multiplier_mode, inner_smul_right, inner_circleMode]
  split_ifs <;> simp

theorem inner_mode_multiplier_self (n : ℤ) :
    ⟪circleMode n, multiplier d M hM hd (circleMode n)⟫_ℂ = d n := by
  simp [inner_mode_multiplier]

theorem multiplier_norm_le : ‖multiplier d M hM hd‖ ≤ M := by
  refine ContinuousLinearMap.opNorm_le_bound _ hM (fun x => ?_)
  rw [← fourierONB.repr.norm_map (multiplier d M hM hd x), multiplier_repr,
    ← fourierONB.repr.norm_map x]
  exact ((diagonal d M hM hd).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (diagonal_norm_le d M hM hd) (norm_nonneg _))

theorem norm_le_multiplier_norm (n : ℤ) : ‖d n‖ ≤ ‖multiplier d M hM hd‖ := by
  calc ‖d n‖ = ‖multiplier d M hM hd (circleMode n)‖ := by
        rw [multiplier_mode, norm_smul, norm_circleMode, mul_one]
    _ ≤ ‖multiplier d M hM hd‖ * ‖circleMode n‖ := (multiplier d M hM hd).le_opNorm _
    _ = ‖multiplier d M hM hd‖ := by rw [norm_circleMode, mul_one]

/-- A bounded operator on `L²(S¹)` is determined by its values on the Fourier modes. -/
theorem multiplier_unique (S : L2Circle →L[ℂ] L2Circle)
    (hS : ∀ n, S (circleMode n) = d n • circleMode n) : S = multiplier d M hM hd := by
  have hdense : Dense ((Submodule.span ℂ (Set.range (@fourierLp (2 * Real.pi) _ 2 _)) :
      Submodule ℂ L2Circle) : Set L2Circle) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact span_fourierLp_closure_eq_top (by simp)
  refine ContinuousLinearMap.ext_on hdense ?_
  rintro _ ⟨n, rfl⟩
  exact (hS n).trans (multiplier_mode d M hM hd n).symm

/-- A real symbol gives a self-adjoint operator. -/
theorem multiplier_isSelfAdjoint (hreal : ∀ n, (starRingEnd ℂ) (d n) = d n) :
    IsSelfAdjoint (multiplier d M hM hd) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  change ⟪multiplier d M hM hd x, y⟫_ℂ = ⟪x, multiplier d M hM hd y⟫_ℂ
  rw [← fourierONB.repr.inner_map_map (multiplier d M hM hd x) y,
    ← fourierONB.repr.inner_map_map x (multiplier d M hM hd y), multiplier_repr, multiplier_repr,
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr (fun i => ?_)
  rw [diagonal_apply, diagonal_apply, ← smul_eq_mul (d i) (fourierONB.repr x i),
    ← smul_eq_mul (d i) (fourierONB.repr y i), inner_smul_left, inner_smul_right, hreal]

/-- A nonvanishing symbol gives an injective operator. -/
theorem multiplier_injective (hne : ∀ n, d n ≠ 0) : Function.Injective (multiplier d M hM hd) := by
  intro x y hxy
  apply fourierONB.repr.injective
  have h := congrArg fourierONB.repr hxy
  rw [multiplier_repr, multiplier_repr] at h
  apply lp.ext
  funext i
  have hi := congrArg (fun f : L2 ℤ => (f : ℤ → ℂ) i) h
  simp only [diagonal_apply] at hi
  exact mul_left_cancel₀ (hne i) hi

/-- A symbol tending to zero gives a compact operator. -/
theorem multiplier_isCompactOperator (hfin : ∀ ε : ℝ, 0 < ε → {n | ε < ‖d n‖}.Finite) :
    IsCompactOperator (multiplier d M hM hd) := by
  have h := ((diagonal_isCompactOperator d M hM hd hfin).comp_clm
    fourierONB.repr.toLinearIsometry.toContinuousLinearMap).clm_comp
      fourierONB.repr.symm.toLinearIsometry.toContinuousLinearMap
  unfold multiplier
  rw [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
  exact h

end Multiplier

/-! ### The resolvent of `(D - φ)² + a²` -/

theorem circleEig_ge (a φ : ℝ) (n : ℤ) : a ^ 2 ≤ circleEig a φ n := by
  unfold circleEig
  nlinarith [sq_nonneg ((n : ℝ) - φ)]

/-- The symbol `n ↦ 1/b_n`, `b_n = (n - φ)² + a²`. -/
def resolventSymbol (a φ : ℝ) (n : ℤ) : ℂ := (((circleEig a φ n)⁻¹ : ℝ) : ℂ)

theorem resolventSymbol_norm (a φ : ℝ) (ha : 0 < a) (n : ℤ) :
    ‖resolventSymbol a φ n‖ = (circleEig a φ n)⁻¹ := by
  rw [resolventSymbol, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (circleEig_pos a φ ha n).le)]

theorem resolventSymbol_norm_le (a φ : ℝ) (ha : 0 < a) (n : ℤ) :
    ‖resolventSymbol a φ n‖ ≤ (a ^ 2)⁻¹ := by
  rw [resolventSymbol_norm a φ ha]
  exact inv_anti₀ (by positivity) (circleEig_ge a φ n)

theorem resolventSymbol_finite (a φ : ℝ) (ha : 0 < a) (ε : ℝ) (hε : 0 < ε) :
    {n : ℤ | ε < ‖resolventSymbol a φ n‖}.Finite := by
  set r : ℝ := 1 / ε + 1 with hr
  refine (Set.finite_Icc (⌊φ - r⌋) (⌈φ + r⌉)).subset ?_
  intro n hn
  change ε < ‖resolventSymbol a φ n‖ at hn
  have hb := circleEig_pos a φ ha n
  rw [resolventSymbol_norm a φ ha] at hn
  have hlt : circleEig a φ n < 1 / ε := by
    have h1 : ε * circleEig a φ n < 1 := by
      have := mul_lt_mul_of_pos_right hn hb
      rwa [inv_mul_cancel₀ hb.ne'] at this
    rw [lt_div_iff₀ hε]
    linarith
  have hε' : 0 < 1 / ε := by positivity
  have habs : |(n : ℝ) - φ| < r := by
    by_contra h
    replace h := not_lt.mp h
    have h2 : r ^ 2 ≤ ((n : ℝ) - φ) ^ 2 := by
      rw [← sq_abs ((n : ℝ) - φ)]
      exact pow_le_pow_left₀ (by positivity) h 2
    have h3 : 1 / ε < r ^ 2 := by
      rw [hr]
      nlinarith
    unfold circleEig at hlt
    nlinarith [sq_nonneg a]
  rw [abs_lt] at habs
  rw [Set.mem_Icc]
  constructor
  · have : ((⌊φ - r⌋ : ℤ) : ℝ) < n := lt_of_le_of_lt (Int.floor_le _) (by linarith)
    exact_mod_cast this.le
  · have : (n : ℝ) < ((⌈φ + r⌉ : ℤ) : ℝ) := lt_of_lt_of_le (by linarith) (Int.le_ceil _)
    exact_mod_cast this.le

/-- **Operator realisation.** The bounded resolvent `((D - φ)² + a²)⁻¹` on `L²(S¹)`, as the
Fourier multiplier with symbol `1/b_n`. -/
def resolvent (a φ : ℝ) (ha : 0 < a) : L2Circle →L[ℂ] L2Circle :=
  multiplier (resolventSymbol a φ) (a ^ 2)⁻¹ (by positivity) (resolventSymbol_norm_le a φ ha)

theorem resolvent_mode (a φ : ℝ) (ha : 0 < a) (n : ℤ) :
    resolvent a φ ha (circleMode n) = (((circleEig a φ n)⁻¹ : ℝ) : ℂ) • circleMode n :=
  multiplier_mode _ _ _ _ n

/-- `resolvent` inverts `b_n` on the mode `e_n`: `resolvent (b_n • e_n) = e_n`. -/
theorem resolvent_inverts_on_mode (a φ : ℝ) (ha : 0 < a) (n : ℤ) :
    resolvent a φ ha (((circleEig a φ n : ℝ) : ℂ) • circleMode n) = circleMode n := by
  rw [ContinuousLinearMap.map_smul, resolvent_mode, smul_smul, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (circleEig_pos a φ ha n).ne', Complex.ofReal_one, one_smul]

theorem resolvent_isSelfAdjoint (a φ : ℝ) (ha : 0 < a) : IsSelfAdjoint (resolvent a φ ha) :=
  multiplier_isSelfAdjoint _ _ _ _ (fun _ => Complex.conj_ofReal _)

theorem resolvent_injective (a φ : ℝ) (ha : 0 < a) : Function.Injective (resolvent a φ ha) :=
  multiplier_injective _ _ _ _ (fun n => by
    rw [resolventSymbol, Complex.ofReal_ne_zero]
    exact inv_ne_zero (circleEig_pos a φ ha n).ne')

theorem resolvent_isCompactOperator (a φ : ℝ) (ha : 0 < a) :
    IsCompactOperator (resolvent a φ ha) :=
  multiplier_isCompactOperator _ _ _ _ (resolventSymbol_finite a φ ha)

theorem resolvent_norm_le (a φ : ℝ) (ha : 0 < a) : ‖resolvent a φ ha‖ ≤ (a ^ 2)⁻¹ :=
  multiplier_norm_le _ _ _ _

/-- At `φ = 0` the bound is attained on the constant mode: `‖resolvent a 0‖ = 1/a²`. -/
theorem resolvent_norm_phase_zero (a : ℝ) (ha : 0 < a) : ‖resolvent a 0 ha‖ = (a ^ 2)⁻¹ := by
  refine le_antisymm (resolvent_norm_le a 0 ha) ?_
  have h := norm_le_multiplier_norm (resolventSymbol a 0) (a ^ 2)⁻¹ (by positivity)
    (resolventSymbol_norm_le a 0 ha) 0
  rw [resolventSymbol_norm a 0 ha] at h
  have h0 : circleEig a 0 0 = a ^ 2 := by simp [circleEig]
  rw [h0] at h
  exact h

/-- The resolvent is unique among bounded operators with eigenvectors `e_n`, eigenvalues `1/b_n`. -/
theorem resolvent_unique (a φ : ℝ) (ha : 0 < a) (S : L2Circle →L[ℂ] L2Circle)
    (hS : ∀ n, S (((circleEig a φ n : ℝ) : ℂ) • circleMode n) = circleMode n) :
    S = resolvent a φ ha := by
  refine multiplier_unique _ _ _ _ S (fun n => ?_)
  have hb : (((circleEig a φ n : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (circleEig_pos a φ ha n).ne'
  have h := hS n
  rw [ContinuousLinearMap.map_smul] at h
  calc S (circleMode n) = (((circleEig a φ n : ℝ) : ℂ))⁻¹ •
        ((((circleEig a φ n : ℝ) : ℂ)) • S (circleMode n)) := by
          rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
    _ = resolventSymbol a φ n • circleMode n := by
          rw [h, resolventSymbol, Complex.ofReal_inv]

/-! ### The differential expression on the Fourier modes -/

/-- The mode `θ ↦ e^{inθ}` on `ℝ`, the lift of `fourier n` from `S¹ = ℝ/2πℤ`. -/
def modeFun (n : ℤ) (θ : ℝ) : ℂ := fourier n (θ : AddCircle (2 * Real.pi))

theorem circleMode_ae_eq (n : ℤ) :
    (circleMode n : AddCircle (2 * Real.pi) → ℂ) =ᵐ[haarAddCircle] fourier n :=
  coeFn_fourierLp 2 n

theorem modeFun_eq (n : ℤ) (θ : ℝ) : modeFun n θ = Complex.exp (Complex.I * n * θ) := by
  rw [modeFun, fourier_coe_apply]
  congr 1
  have : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  field_simp
  push_cast
  ring

theorem modeFun_hasDerivAt (n : ℤ) (θ : ℝ) :
    HasDerivAt (modeFun n) (Complex.I * n * modeFun n θ) θ := by
  have h := hasDerivAt_fourier (2 * Real.pi) n θ
  have : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  have e : Complex.I * n * modeFun n θ =
      2 * (Real.pi : ℂ) * Complex.I * n / ((2 * Real.pi : ℝ) : ℂ) *
        fourier n (θ : AddCircle (2 * Real.pi)) := by
    simp only [modeFun]
    field_simp
    push_cast
    ring
  rw [e]
  exact h

theorem deriv_modeFun (n : ℤ) : deriv (modeFun n) = fun θ => Complex.I * n * modeFun n θ :=
  funext fun θ => (modeFun_hasDerivAt n θ).deriv

/-- The differential expression `(D - φ)² + a² = -d²/dθ² + 2iφ d/dθ + φ² + a²`, `D = -i d/dθ`. -/
def twistedOp (a φ : ℝ) (u : ℝ → ℂ) (θ : ℝ) : ℂ :=
  -deriv (deriv u) θ + 2 * Complex.I * φ * deriv u θ + ((φ ^ 2 + a ^ 2 : ℝ) : ℂ) * u θ

/-- `(D - φ)² + a²` acts on `θ ↦ e^{inθ}` as multiplication by `b_n = (n - φ)² + a²`. -/
theorem twistedOp_modeFun (a φ : ℝ) (n : ℤ) (θ : ℝ) :
    twistedOp a φ (modeFun n) θ = ((circleEig a φ n : ℝ) : ℂ) * modeFun n θ := by
  have h2 : deriv (deriv (modeFun n)) θ = Complex.I * n * (Complex.I * n * modeFun n θ) := by
    rw [deriv_modeFun]
    exact ((modeFun_hasDerivAt n θ).const_mul (Complex.I * n)).deriv
  unfold twistedOp
  rw [h2, deriv_modeFun]
  unfold circleEig
  push_cast
  linear_combination (-(n : ℂ) ^ 2 * modeFun n θ + 2 * φ * n * modeFun n θ) * Complex.I_sq

/-! ### Diagonal sums in the Fourier basis -/

/-- `∑_{n∈ℤ} ⟪e_n, resolvent e_n⟫ = (π/a) sinh(2πa)/(cosh 2πa - cos 2πφ)`. -/
theorem resolvent_diagonal_hasSum (a φ : ℝ) (ha : 0 < a) :
    HasSum (fun n : ℤ => ⟪circleMode n, resolvent a φ ha (circleMode n)⟫_ℂ)
      ((resolventClosed a φ : ℝ) : ℂ) := by
  have h := Complex.hasSum_ofReal.mpr (circle_resolvent_hasSum a φ ha)
  convert h using 1
  funext n
  rw [resolvent, inner_mode_multiplier_self, resolventSymbol, one_div]

/-- The evanescent symbol `n ↦ e^{-2t√b_n}`, `t ≥ 0`. -/
def evanescentSymbol (a φ : ℝ) (t : ℝ≥0) (n : ℤ) : ℂ :=
  ((Real.exp (-(2 * Real.sqrt (circleEig a φ n) * t)) : ℝ) : ℂ)

theorem evanescentSymbol_norm_le (a φ : ℝ) (t : ℝ≥0) (n : ℤ) : ‖evanescentSymbol a φ t n‖ ≤ 1 := by
  rw [evanescentSymbol, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.exp_le_one_iff]
  have h1 := Real.sqrt_nonneg (circleEig a φ n)
  have h2 := t.2
  nlinarith

/-- `e^{-2t√B}` on `L²(S¹)`, `B = (D - φ)² + a²`, as the Fourier multiplier `e^{-2t√b_n}`. -/
def evanescent (a φ : ℝ) (t : ℝ≥0) : L2Circle →L[ℂ] L2Circle :=
  multiplier (evanescentSymbol a φ t) 1 zero_le_one (evanescentSymbol_norm_le a φ t)

theorem evanescent_mode (a φ : ℝ) (t : ℝ≥0) (n : ℤ) :
    evanescent a φ t (circleMode n) = evanescentSymbol a φ t n • circleMode n :=
  multiplier_mode _ _ _ _ n

theorem evanescent_zero (a φ : ℝ) : evanescent a φ 0 = ContinuousLinearMap.id ℂ L2Circle := by
  symm
  refine multiplier_unique _ _ _ _ _ (fun n => ?_)
  simp [evanescentSymbol]

/-- Semigroup law `e^{-2(s+t)√B} = e^{-2s√B} e^{-2t√B}`. -/
theorem evanescent_add (a φ : ℝ) (s t : ℝ≥0) :
    evanescent a φ (s + t) = (evanescent a φ s).comp (evanescent a φ t) := by
  symm
  refine multiplier_unique _ _ _ _ _ (fun n => ?_)
  rw [ContinuousLinearMap.comp_apply, evanescent_mode, ContinuousLinearMap.map_smul,
    evanescent_mode, smul_smul]
  congr 1
  rw [evanescentSymbol, evanescentSymbol, evanescentSymbol, ← Complex.ofReal_mul,
    ← Real.exp_add, NNReal.coe_add]
  congr 2
  ring

theorem evanescent_isSelfAdjoint (a φ : ℝ) (t : ℝ≥0) : IsSelfAdjoint (evanescent a φ t) :=
  multiplier_isSelfAdjoint _ _ _ _ (fun _ => Complex.conj_ofReal _)

/-- **`eq:hol-integral`, operator form.**
`∫₀^∞ z ∑_{n∈ℤ} ⟪e_n, e^{-2z√B} e_n⟫ dz = momentClosed a (πa) (cos 2πφ)`. -/
theorem evanescent_diagonal_integral (a φ : ℝ) (ha : 0 < a) :
    (∫ z : ℝ in Ioi 0,
        z * (∑' n : ℤ, ⟪circleMode n, evanescent a φ z.toNNReal (circleMode n)⟫_ℂ).re) =
      momentClosed a (Real.pi * a) (Real.cos (2 * Real.pi * φ)) := by
  rw [← evanescent_trace_integral a φ ha]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
  have hz' : ((z.toNNReal : ℝ≥0) : ℝ) = z := Real.coe_toNNReal z (le_of_lt hz)
  simp only [evanescent, inner_mode_multiplier_self, evanescentSymbol, hz']
  rw [← Complex.ofReal_tsum, Complex.ofReal_re, ← tsum_mul_left]

/-- **`eq:hol-integral`, resolvent form.**
`∑_n ⟪e_n, resolvent e_n⟫ = 4 ∫₀^∞ z ∑_n ⟪e_n, e^{-2z√B} e_n⟫ dz`. -/
theorem resolvent_diagonal_eq_four_integral (a φ : ℝ) (ha : 0 < a) :
    (∑' n : ℤ, ⟪circleMode n, resolvent a φ ha (circleMode n)⟫_ℂ).re =
      4 * ∫ z : ℝ in Ioi 0,
        z * (∑' n : ℤ, ⟪circleMode n, evanescent a φ z.toNNReal (circleMode n)⟫_ℂ).re := by
  rw [evanescent_diagonal_integral a φ ha, (resolvent_diagonal_hasSum a φ ha).tsum_eq,
    Complex.ofReal_re]
  have h1 := (circle_resolvent_hasSum a φ ha).div_const 4
  have h2 := moment_series_hasSum a φ ha
  have h3 : HasSum (fun n : ℤ => 1 / circleEig a φ n / 4)
      (momentClosed a (Real.pi * a) (Real.cos (2 * Real.pi * φ))) := by
    convert h2 using 1
    funext n
    rw [div_div, mul_comm]
  rw [← h1.unique h3]
  ring

end Manuscript16.HolonomyCircleResolvent20261125

#print axioms Manuscript16.HolonomyCircleResolvent20261125.fourierONB_apply
#print axioms Manuscript16.HolonomyCircleResolvent20261125.inner_circleMode
#print axioms Manuscript16.HolonomyCircleResolvent20261125.norm_circleMode
#print axioms Manuscript16.HolonomyCircleResolvent20261125.multiplier_repr
#print axioms Manuscript16.HolonomyCircleResolvent20261125.diagonal_single
#print axioms Manuscript16.HolonomyCircleResolvent20261125.multiplier_mode
#print axioms Manuscript16.HolonomyCircleResolvent20261125.inner_mode_multiplier
#print axioms Manuscript16.HolonomyCircleResolvent20261125.inner_mode_multiplier_self
#print axioms Manuscript16.HolonomyCircleResolvent20261125.multiplier_norm_le
#print axioms Manuscript16.HolonomyCircleResolvent20261125.norm_le_multiplier_norm
#print axioms Manuscript16.HolonomyCircleResolvent20261125.multiplier_unique
#print axioms Manuscript16.HolonomyCircleResolvent20261125.multiplier_isSelfAdjoint
#print axioms Manuscript16.HolonomyCircleResolvent20261125.multiplier_injective
#print axioms Manuscript16.HolonomyCircleResolvent20261125.multiplier_isCompactOperator
#print axioms Manuscript16.HolonomyCircleResolvent20261125.circleEig_ge
#print axioms Manuscript16.HolonomyCircleResolvent20261125.resolventSymbol_norm
#print axioms Manuscript16.HolonomyCircleResolvent20261125.resolventSymbol_norm_le
#print axioms Manuscript16.HolonomyCircleResolvent20261125.resolventSymbol_finite
#print axioms Manuscript16.HolonomyCircleResolvent20261125.resolvent_mode
#print axioms Manuscript16.HolonomyCircleResolvent20261125.resolvent_inverts_on_mode
#print axioms Manuscript16.HolonomyCircleResolvent20261125.resolvent_isSelfAdjoint
#print axioms Manuscript16.HolonomyCircleResolvent20261125.resolvent_injective
#print axioms Manuscript16.HolonomyCircleResolvent20261125.resolvent_isCompactOperator
#print axioms Manuscript16.HolonomyCircleResolvent20261125.resolvent_norm_le
#print axioms Manuscript16.HolonomyCircleResolvent20261125.resolvent_norm_phase_zero
#print axioms Manuscript16.HolonomyCircleResolvent20261125.resolvent_unique
#print axioms Manuscript16.HolonomyCircleResolvent20261125.circleMode_ae_eq
#print axioms Manuscript16.HolonomyCircleResolvent20261125.modeFun_eq
#print axioms Manuscript16.HolonomyCircleResolvent20261125.modeFun_hasDerivAt
#print axioms Manuscript16.HolonomyCircleResolvent20261125.deriv_modeFun
#print axioms Manuscript16.HolonomyCircleResolvent20261125.twistedOp_modeFun
#print axioms Manuscript16.HolonomyCircleResolvent20261125.resolvent_diagonal_hasSum
#print axioms Manuscript16.HolonomyCircleResolvent20261125.evanescentSymbol_norm_le
#print axioms Manuscript16.HolonomyCircleResolvent20261125.evanescent_mode
#print axioms Manuscript16.HolonomyCircleResolvent20261125.evanescent_zero
#print axioms Manuscript16.HolonomyCircleResolvent20261125.evanescent_add
#print axioms Manuscript16.HolonomyCircleResolvent20261125.evanescent_isSelfAdjoint
#print axioms Manuscript16.HolonomyCircleResolvent20261125.evanescent_diagonal_integral
#print axioms Manuscript16.HolonomyCircleResolvent20261125.resolvent_diagonal_eq_four_integral
