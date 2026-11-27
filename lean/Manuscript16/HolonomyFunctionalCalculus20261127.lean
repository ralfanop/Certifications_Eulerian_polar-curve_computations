import Mathlib
import Manuscript16.HolonomyCircleResolvent20261125
import Manuscript16.HolonomyCircleGenerator20261125

/-!
# M16 `eq:hol-integral`: `e^{-2t√B}` through the continuous functional calculus of `B⁻¹`

The register `audits/M16_M17_exact_head_audit_20261124.md` (section "Post-merge consistency of
`main` (#622)") lists as still open for `eq:hol-integral` "the functional calculus `e^{-2t√B}`":
in #599 (`HolonomyCircleResolvent20261125`) the operators `evanescent a φ t` are *defined* as the
Fourier multipliers with symbol `e^{-2t√b_n}`, `b_n = (n - φ)² + a²`, and #622
(`HolonomyCircleGenerator20261125`) realises `B = (D - φ)² + a²` as a self-adjoint operator on
`L²(S¹)` with `resolvent = B⁻¹`, but no theorem connects the two through a functional calculus.

Mathlib, at the pinned commit, has the continuous functional calculus `cfc` of self-adjoint elements
of a C⋆-algebra, in particular of bounded self-adjoint operators on a complex Hilbert space, but no
functional calculus of unbounded self-adjoint operators. For a self-adjoint `B ≥ a² > 0` with bounded
inverse `R = B⁻¹`, the operator `h(B)` of the spectral theorem equals `(h ∘ ι)(R)`, `ι(x) = 1/x`
(classical spectral theory, a published result cited, not formalised here). This file therefore
works with `R = resolvent a φ = B⁻¹` and Mathlib's `cfc`, and proves:

* `eig_mem_spectrum`: every `1/b_n` lies in the real spectrum of `R`;
* `diagHom`: `f ↦ multiplier (n ↦ f(1/b_n))` is a continuous star-algebra homomorphism
  `C(σ(R), ℝ) → B(L²(S¹))` sending the identity to `R`; by the uniqueness of the continuous
  functional calculus (Mathlib `cfcHom_eq_of_continuous_of_map_id`) it **is** `cfcHom` of `R`
  (`cfcHom_resolvent_eq`);
* `cfc_resolvent_mode`, `cfc_resolvent_eq_multiplier`: for every `g : ℝ → ℝ` continuous on `σ(R)`,
  `cfc g R e_n = g(1/b_n) e_n`, so `cfc g R` is the Fourier multiplier with symbol `g(1/b_n)`;
* `evGen t x = e^{-2t/√x}` (`x > 0`), `0` (`x ≤ 0`) is continuous on `ℝ` for `t > 0`
  (`evGen_continuous`), and `evGen t (1/b_n) = e^{-2t√b_n}`;
* `evanescent_eq_cfc`: **`evanescent a φ t = cfc (evGen t) (B⁻¹)` for every `t > 0`**, i.e. the
  multipliers of #599 are the operators `e^{-2t√B}` given by the continuous functional calculus of
  `B⁻¹`; `cfc_sqrt_resolvent_mode`: `cfc √· (B⁻¹) e_n = b_n^{-1/2} e_n` (`(B⁻¹)^{1/2} = (√B)⁻¹` on the
  Fourier basis);
* `cfc_resolvent_generator`: for every `g` and every `u ∈ dom B`, `cfc g (B⁻¹) u ∈ dom B` and
  `B (cfc g (B⁻¹) u) = cfc g (B⁻¹) (B u)`;
* `hol_integral_functional_calculus` (manuscript form): with `e^{-2z√B} := cfc (evGen z) (B⁻¹)`,
  `∫₀^∞ z ∑_{n∈ℤ} ⟪e_n, e^{-2z√B} e_n⟫ dz = momentClosed a (πa) (cos 2πφ)` and
  `∑_n ⟪e_n, B⁻¹ e_n⟫ = 4 ∫₀^∞ z ∑_n ⟪e_n, e^{-2z√B} e_n⟫ dz`.

Inputs used, not re-proved: Mathlib's continuous functional calculus and its uniqueness; the merged
modules #598, #599, #622 (Fourier multipliers, `resolvent`, `evanescent`, the closed forms, `B`).

Not claimed. A functional calculus of the unbounded operator `B` itself (Mathlib has none at the
pinned commit) and the identity `h(B) = (h ∘ ι)(B⁻¹)` of the spectral theorem (published result
cited); trace-class membership and basis independence of the diagonal sums (Lidskii; Simon 2005);
strong continuity of `t ↦ e^{-2t√B}` and the identification of its generator with `-2√B`; any
Maxwell or geometric statement; the correspondence with the printed display of `16.tex` (source not
in the repository).
-/

open scoped ENNReal NNReal InnerProductSpace Topology
open MeasureTheory Set Filter

namespace Manuscript16.HolonomyFunctionalCalculus20261127

open Manuscript16.ReactiveHolonomy Manuscript16.HolonomyMomentSeries20261124
open Manuscript16.HolonomyCircleResolvent20261125
open Manuscript16.HolonomyCircleGenerator20261125

noncomputable section

/-- The real algebra structure of `B(L²(S¹))` used by Mathlib's continuous functional calculus of
self-adjoint elements: restriction of scalars from `ℂ` (Mathlib `Algebra.complexToReal`). It is
selected explicitly because the `ℝ`-module structure of `Lp` gives a second, propositionally equal,
instance that the type-class search would otherwise find first. -/
local instance (priority := high) instAlgRealL2Circle : Algebra ℝ (L2Circle →L[ℂ] L2Circle) :=
  Algebra.complexToReal

theorem algebraMap_real (r : ℝ) :
    algebraMap ℝ (L2Circle →L[ℂ] L2Circle) r = (r : ℂ) • (1 : L2Circle →L[ℂ] L2Circle) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  rfl

/-! ### Eigenvalues lie in the spectrum -/

/-- An eigenvalue of a bounded operator on `L²(S¹)` lies in its real spectrum. -/
theorem mem_spectrum_of_eigenvector {T : L2Circle →L[ℂ] L2Circle} {r : ℝ} {v : L2Circle}
    (hv : v ≠ 0) (h : T v = (r : ℂ) • v) : r ∈ spectrum ℝ T := by
  rw [spectrum.mem_iff]
  rintro ⟨u, hu⟩
  apply hv
  have h0 : (u : L2Circle →L[ℂ] L2Circle) v = 0 := by
    rw [hu, algebraMap_real]
    change (r : ℂ) • v - T v = 0
    rw [h, sub_self]
  calc v = ((↑u⁻¹ : L2Circle →L[ℂ] L2Circle) * (u : L2Circle →L[ℂ] L2Circle)) v := by
        rw [Units.inv_mul]; rfl
    _ = (↑u⁻¹ : L2Circle →L[ℂ] L2Circle) ((u : L2Circle →L[ℂ] L2Circle) v) := rfl
    _ = 0 := by rw [h0, map_zero]

theorem circleMode_ne_zero (n : ℤ) : circleMode n ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_circleMode]
  exact one_ne_zero

/-- `1/b_n ∈ σ(B⁻¹)` for every `n ∈ ℤ`. -/
theorem eig_mem_spectrum (a φ : ℝ) (ha : 0 < a) (n : ℤ) :
    (circleEig a φ n)⁻¹ ∈ spectrum ℝ (resolvent a φ ha) :=
  mem_spectrum_of_eigenvector (circleMode_ne_zero n) (resolvent_mode a φ ha n)

/-! ### The diagonal star-algebra homomorphism -/

section Hom

variable (a φ : ℝ) (ha : 0 < a)

/-- The eigenvalue `1/b_n` as a point of `σ(B⁻¹)`. -/
def specPt (n : ℤ) : spectrum ℝ (resolvent a φ ha) :=
  ⟨(circleEig a φ n)⁻¹, eig_mem_spectrum a φ ha n⟩

/-- The symbol `n ↦ f(1/b_n)` of a continuous function on `σ(B⁻¹)`. -/
def diagSymbol (f : C(spectrum ℝ (resolvent a φ ha), ℝ)) (n : ℤ) : ℂ :=
  ((f (specPt a φ ha n) : ℝ) : ℂ)

theorem diagSymbol_norm_le (f : C(spectrum ℝ (resolvent a φ ha), ℝ)) (n : ℤ) :
    ‖diagSymbol a φ ha f n‖ ≤ ‖f‖ := by
  rw [diagSymbol, Complex.norm_real]
  exact f.norm_coe_le_norm _

/-- The Fourier multiplier with symbol `f(1/b_n)`. -/
def diagOp (f : C(spectrum ℝ (resolvent a φ ha), ℝ)) : L2Circle →L[ℂ] L2Circle :=
  multiplier (diagSymbol a φ ha f) ‖f‖ (norm_nonneg f) (diagSymbol_norm_le a φ ha f)

theorem diagOp_mode (f : C(spectrum ℝ (resolvent a φ ha), ℝ)) (n : ℤ) :
    diagOp a φ ha f (circleMode n) = diagSymbol a φ ha f n • circleMode n :=
  multiplier_mode _ _ _ _ n

theorem diagOp_ext {f : C(spectrum ℝ (resolvent a φ ha), ℝ)} {S : L2Circle →L[ℂ] L2Circle}
    (hS : ∀ n, S (circleMode n) = diagSymbol a φ ha f n • circleMode n) : diagOp a φ ha f = S :=
  (multiplier_unique _ _ _ _ S hS).symm

theorem diagOp_norm_le (f : C(spectrum ℝ (resolvent a φ ha), ℝ)) : ‖diagOp a φ ha f‖ ≤ ‖f‖ :=
  multiplier_norm_le _ _ _ _

theorem diagOp_isSelfAdjoint (f : C(spectrum ℝ (resolvent a φ ha), ℝ)) :
    IsSelfAdjoint (diagOp a φ ha f) :=
  multiplier_isSelfAdjoint _ _ _ _ (fun _ => Complex.conj_ofReal _)

/-- `f ↦ multiplier (n ↦ f(1/b_n))` as a star-algebra homomorphism `C(σ(B⁻¹), ℝ) → B(L²(S¹))`. -/
def diagHom : C(spectrum ℝ (resolvent a φ ha), ℝ) →⋆ₐ[ℝ] (L2Circle →L[ℂ] L2Circle) where
  toFun := diagOp a φ ha
  map_one' := diagOp_ext a φ ha (fun n => by
    change circleMode n = _
    simp [diagSymbol])
  map_mul' f g := diagOp_ext a φ ha (fun n => by
    change diagOp a φ ha f (diagOp a φ ha g (circleMode n)) = _
    rw [diagOp_mode, ContinuousLinearMap.map_smul, diagOp_mode, smul_smul]
    simp [diagSymbol, mul_comm])
  map_zero' := diagOp_ext a φ ha (fun n => by
    change (0 : L2Circle) = _
    simp [diagSymbol])
  map_add' f g := diagOp_ext a φ ha (fun n => by
    change diagOp a φ ha f (circleMode n) + diagOp a φ ha g (circleMode n) = _
    rw [diagOp_mode, diagOp_mode, ← add_smul]
    simp [diagSymbol])
  commutes' r := diagOp_ext a φ ha (fun n => by
    rw [algebraMap_real]
    change (r : ℂ) • circleMode n = _
    simp [diagSymbol])
  map_star' f := by
    have hf : star f = f := by
      ext x
      simp
    change diagOp a φ ha (star f) = star (diagOp a φ ha f)
    rw [hf, (diagOp_isSelfAdjoint a φ ha f).star_eq]

theorem diagHom_apply (f : C(spectrum ℝ (resolvent a φ ha), ℝ)) :
    diagHom a φ ha f = diagOp a φ ha f :=
  rfl

theorem diagHom_continuous : Continuous (diagHom a φ ha) :=
  AddMonoidHomClass.continuous_of_bound (diagHom a φ ha) 1 (fun f => by
    rw [one_mul, diagHom_apply]
    exact diagOp_norm_le a φ ha f)

theorem diagHom_id :
    diagHom a φ ha ((ContinuousMap.id ℝ).restrict (spectrum ℝ (resolvent a φ ha))) =
      resolvent a φ ha := by
  rw [diagHom_apply]
  exact diagOp_ext a φ ha (fun n => by rw [resolvent_mode]; rfl)

/-- **Uniqueness of the continuous functional calculus.** The continuous functional calculus of the
self-adjoint operator `B⁻¹ = resolvent a φ` is the diagonal homomorphism `diagHom`. -/
theorem cfcHom_resolvent_eq :
    cfcHom (resolvent_isSelfAdjoint a φ ha) = diagHom a φ ha :=
  cfcHom_eq_of_continuous_of_map_id (resolvent_isSelfAdjoint a φ ha) (diagHom a φ ha)
    (diagHom_continuous a φ ha) (diagHom_id a φ ha)

/-- `cfc g (B⁻¹) e_n = g(1/b_n) e_n` for every `g` continuous on `σ(B⁻¹)`. -/
theorem cfc_resolvent_mode (g : ℝ → ℝ) (hg : ContinuousOn g (spectrum ℝ (resolvent a φ ha)))
    (n : ℤ) :
    cfc g (resolvent a φ ha) (circleMode n) = ((g (circleEig a φ n)⁻¹ : ℝ) : ℂ) • circleMode n := by
  rw [cfc_apply g (resolvent a φ ha) (resolvent_isSelfAdjoint a φ ha) hg, cfcHom_resolvent_eq,
    diagHom_apply, diagOp_mode]
  rfl

/-- `cfc g (B⁻¹)` is the Fourier multiplier with symbol `g(1/b_n)`. -/
theorem cfc_resolvent_eq_multiplier (g : ℝ → ℝ)
    (hg : ContinuousOn g (spectrum ℝ (resolvent a φ ha))) (M : ℝ) (hM : 0 ≤ M)
    (hd : ∀ n, ‖((g (circleEig a φ n)⁻¹ : ℝ) : ℂ)‖ ≤ M) :
    cfc g (resolvent a φ ha) = multiplier (fun n => ((g (circleEig a φ n)⁻¹ : ℝ) : ℂ)) M hM hd :=
  multiplier_unique _ _ _ _ _ (cfc_resolvent_mode a φ ha g hg)

/-- `(B⁻¹)^{1/2} e_n = b_n^{-1/2} e_n`: the square root of `B⁻¹` given by the functional calculus is
`(√B)⁻¹` on the Fourier basis. -/
theorem cfc_sqrt_resolvent_mode (n : ℤ) :
    cfc Real.sqrt (resolvent a φ ha) (circleMode n) =
      (((Real.sqrt (circleEig a φ n))⁻¹ : ℝ) : ℂ) • circleMode n := by
  rw [cfc_resolvent_mode a φ ha _ Real.continuous_sqrt.continuousOn, Real.sqrt_inv]

/-- Every operator `cfc g (B⁻¹)` commutes with `B`: it maps `dom B` into `dom B` and
`B (cfc g (B⁻¹) u) = cfc g (B⁻¹) (B u)`. -/
theorem cfc_resolvent_generator (g : ℝ → ℝ) (u : (generator a φ ha).domain) :
    ∃ h : cfc g (resolvent a φ ha) u ∈ (generator a φ ha).domain,
      generator a φ ha ⟨cfc g (resolvent a φ ha) u, h⟩ =
        cfc g (resolvent a φ ha) (generator a φ ha u) := by
  have hc : Commute (cfc g (resolvent a φ ha)) (resolvent a φ ha) :=
    (Commute.refl (resolvent a φ ha)).cfc
      (by rw [(resolvent_isSelfAdjoint a φ ha).star_eq]; exact Commute.refl _) g
  have hu : (u : L2Circle) = resolvent a φ ha (generator a φ ha u) :=
    (resolvent_generator a φ ha u).symm
  have hTu : cfc g (resolvent a φ ha) (u : L2Circle) =
      resolvent a φ ha (cfc g (resolvent a φ ha) (generator a φ ha u)) := by
    calc cfc g (resolvent a φ ha) (u : L2Circle)
        = (cfc g (resolvent a φ ha) * resolvent a φ ha) (generator a φ ha u) := by
          change _ = cfc g (resolvent a φ ha) (resolvent a φ ha (generator a φ ha u))
          rw [← hu]
      _ = (resolvent a φ ha * cfc g (resolvent a φ ha)) (generator a φ ha u) := by rw [hc.eq]
      _ = resolvent a φ ha (cfc g (resolvent a φ ha) (generator a φ ha u)) := rfl
  have hmem := resolvent_mem_domain a φ ha (cfc g (resolvent a φ ha) (generator a φ ha u))
  have hmem' : cfc g (resolvent a φ ha) (u : L2Circle) ∈ (generator a φ ha).domain := by
    rw [hTu]
    exact hmem
  refine ⟨hmem', ?_⟩
  have hsub : (⟨cfc g (resolvent a φ ha) (u : L2Circle), hmem'⟩ : (generator a φ ha).domain) =
      ⟨resolvent a φ ha (cfc g (resolvent a φ ha) (generator a φ ha u)), hmem⟩ :=
    Subtype.ext hTu
  rw [hsub, generator_resolvent]

end Hom

/-! ### The evanescent semigroup -/

/-- `evGen t x = e^{-2t/√x}` for `x > 0`, `0` for `x ≤ 0`; `evGen t (1/b) = e^{-2t√b}`. -/
def evGen (t x : ℝ) : ℝ := if 0 < x then Real.exp (-(2 * t) / Real.sqrt x) else 0

theorem evGen_tendsto_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (fun x : ℝ => Real.exp (-(2 * t) / Real.sqrt x)) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h := Real.continuous_sqrt.tendsto 0
      rw [Real.sqrt_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx using Real.sqrt_pos.mpr hx
  have h2 : Tendsto (fun x : ℝ => (Real.sqrt x)⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.comp h1
  have h3 : Tendsto (fun x : ℝ => -(2 * t) / Real.sqrt x) (𝓝[>] 0) atBot := by
    have h := h2.const_mul_atTop_of_neg (show -(2 * t) < 0 by linarith)
    simpa only [div_eq_mul_inv] using h
  exact Real.tendsto_exp_atBot.comp h3

theorem evGen_continuous {t : ℝ} (ht : 0 < t) : Continuous (evGen t) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have he : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x] evGen t := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [evGen, not_lt.mpr (le_of_lt (show y < 0 from hy))]
    exact continuousAt_const.congr he
  · rw [continuousAt_iff_continuous_left'_right']
    have h0 : evGen t 0 = 0 := by simp [evGen]
    constructor
    · rw [ContinuousWithinAt, h0]
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with y hy
      simp [evGen, not_lt.mpr (le_of_lt (show y < 0 from hy))]
    · rw [ContinuousWithinAt, h0]
      refine (tendsto_congr' ?_).mpr (evGen_tendsto_zero ht)
      filter_upwards [self_mem_nhdsWithin] with y hy
      simp [evGen, show (0 : ℝ) < y from hy]
  · have he : (fun y : ℝ => Real.exp (-(2 * t) / Real.sqrt y)) =ᶠ[𝓝 x] evGen t := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [evGen, show (0 : ℝ) < y from hy]
    refine ContinuousAt.congr ?_ he
    exact Real.continuous_exp.continuousAt.comp
      (continuousAt_const.div Real.continuous_sqrt.continuousAt (Real.sqrt_pos.mpr hx).ne')

theorem evGen_inv_eig (t a φ : ℝ) (ha : 0 < a) (n : ℤ) :
    evGen t (circleEig a φ n)⁻¹ = Real.exp (-(2 * Real.sqrt (circleEig a φ n) * t)) := by
  have hb := circleEig_pos a φ ha n
  simp only [evGen, inv_pos.mpr hb, ↓reduceIte]
  rw [Real.sqrt_inv, div_inv_eq_mul]
  congr 1
  ring

/-- `e^{-2t√B} e_n = e^{-2t√b_n} e_n` for `e^{-2t√B} := cfc (evGen t) (B⁻¹)`, `t > 0`. -/
theorem cfc_evGen_mode (a φ : ℝ) (ha : 0 < a) {t : ℝ} (ht : 0 < t) (n : ℤ) :
    cfc (evGen t) (resolvent a φ ha) (circleMode n) =
      ((Real.exp (-(2 * Real.sqrt (circleEig a φ n) * t)) : ℝ) : ℂ) • circleMode n := by
  rw [cfc_resolvent_mode a φ ha _ (evGen_continuous ht).continuousOn, evGen_inv_eig t a φ ha n]

/-- **The multipliers of #599 are the operators `e^{-2t√B}` of the functional calculus.**
`evanescent a φ t = cfc (evGen t) (B⁻¹)` for every `t > 0`. -/
theorem evanescent_eq_cfc (a φ : ℝ) (ha : 0 < a) (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    evanescent a φ t = cfc (evGen t) (resolvent a φ ha) := by
  unfold evanescent
  exact (multiplier_unique _ _ _ _ _ (fun n => cfc_evGen_mode a φ ha ht n)).symm

/-- The integrands of `eq:hol-integral` agree on `(0, ∞)` for the two descriptions of
`e^{-2z√B}`. -/
theorem integrand_eq (a φ : ℝ) (ha : 0 < a) {z : ℝ} (hz : 0 < z) :
    z * (∑' n : ℤ, ⟪circleMode n, cfc (evGen z) (resolvent a φ ha) (circleMode n)⟫_ℂ).re =
      z * (∑' n : ℤ, ⟪circleMode n, evanescent a φ z.toNNReal (circleMode n)⟫_ℂ).re := by
  have hz' : ((z.toNNReal : ℝ≥0) : ℝ) = z := Real.coe_toNNReal z hz.le
  rw [evanescent_eq_cfc a φ ha z.toNNReal (by rw [hz']; exact hz), hz']

/-- **M16 `eq:hol-integral`, with `e^{-2z√B}` given by the continuous functional calculus of `B⁻¹`.**
For `a > 0` and real `φ`, with `B = (D - φ)² + a²` the self-adjoint operator of #622 and
`e^{-2z√B} := cfc (evGen z) (B⁻¹)`:
`e^{-2z√B} e_n = e^{-2z√b_n} e_n` (`z > 0`); `e^{-2z√B}` is the multiplier `evanescent` of #599;
`∫₀^∞ z ∑_{n∈ℤ} ⟪e_n, e^{-2z√B} e_n⟫ dz = momentClosed a (πa) (cos 2πφ)`; and
`∑_n ⟪e_n, B⁻¹ e_n⟫ = 4 ∫₀^∞ z ∑_n ⟪e_n, e^{-2z√B} e_n⟫ dz`. -/
theorem hol_integral_functional_calculus (a φ : ℝ) (ha : 0 < a) :
    (∀ f : L2Circle, ∃ h : resolvent a φ ha f ∈ (generator a φ ha).domain,
        generator a φ ha ⟨resolvent a φ ha f, h⟩ = f) ∧
    (∀ u : (generator a φ ha).domain, resolvent a φ ha (generator a φ ha u) = u) ∧
    (∀ (z : ℝ), 0 < z → ∀ n : ℤ, cfc (evGen z) (resolvent a φ ha) (circleMode n) =
        ((Real.exp (-(2 * Real.sqrt (circleEig a φ n) * z)) : ℝ) : ℂ) • circleMode n) ∧
    (∀ t : ℝ≥0, 0 < (t : ℝ) → evanescent a φ t = cfc (evGen t) (resolvent a φ ha)) ∧
    (∫ z : ℝ in Ioi 0,
        z * (∑' n : ℤ, ⟪circleMode n, cfc (evGen z) (resolvent a φ ha) (circleMode n)⟫_ℂ).re) =
      momentClosed a (Real.pi * a) (Real.cos (2 * Real.pi * φ)) ∧
    (∑' n : ℤ, ⟪circleMode n, resolvent a φ ha (circleMode n)⟫_ℂ).re =
      4 * ∫ z : ℝ in Ioi 0,
        z * (∑' n : ℤ, ⟪circleMode n, cfc (evGen z) (resolvent a φ ha) (circleMode n)⟫_ℂ).re := by
  have hint : (∫ z : ℝ in Ioi 0,
        z * (∑' n : ℤ, ⟪circleMode n, cfc (evGen z) (resolvent a φ ha) (circleMode n)⟫_ℂ).re) =
      ∫ z : ℝ in Ioi 0,
        z * (∑' n : ℤ, ⟪circleMode n, evanescent a φ z.toNNReal (circleMode n)⟫_ℂ).re :=
    setIntegral_congr_fun measurableSet_Ioi (fun z hz => integrand_eq a φ ha hz)
  refine ⟨fun f => ⟨resolvent_mem_domain a φ ha f, generator_resolvent a φ ha f⟩,
    resolvent_generator a φ ha, fun z hz n => cfc_evGen_mode a φ ha hz n,
    evanescent_eq_cfc a φ ha, ?_, ?_⟩
  · rw [hint]
    exact evanescent_diagonal_integral a φ ha
  · rw [hint]
    exact resolvent_diagonal_eq_four_integral a φ ha

end

end Manuscript16.HolonomyFunctionalCalculus20261127

#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.instAlgRealL2Circle
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.algebraMap_real
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.mem_spectrum_of_eigenvector
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.circleMode_ne_zero
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.eig_mem_spectrum
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.specPt
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.diagSymbol
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.diagSymbol_norm_le
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.diagOp
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.diagOp_mode
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.diagOp_ext
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.diagOp_norm_le
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.diagOp_isSelfAdjoint
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.diagHom
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.diagHom_apply
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.diagHom_continuous
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.diagHom_id
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.cfcHom_resolvent_eq
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.cfc_resolvent_mode
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.cfc_resolvent_eq_multiplier
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.cfc_sqrt_resolvent_mode
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.cfc_resolvent_generator
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.evGen
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.evGen_tendsto_zero
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.evGen_continuous
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.evGen_inv_eig
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.cfc_evGen_mode
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.evanescent_eq_cfc
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.integrand_eq
#print axioms Manuscript16.HolonomyFunctionalCalculus20261127.hol_integral_functional_calculus
