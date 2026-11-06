import Mathlib
import SpecialImaginaryPoint.GramKernelBispectral
import GegenbauerFock.GramIntegralComplete
import GegenbauerFock.UltrasphericalSturmLiouvillePolynomialCore
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2Nonzero
import GegenbauerFock.UltrasphericalLegendreDensityExact
import GegenbauerFock.OutputComplexHolomorphy

/-!
# Manuscript 14, Theorem 5.2 (domain-level commutation): statement and proof skeleton

This module fixes, in Lean 4, the exact statement of Theorem 5.2 of manuscript 14
(the Legendre–Gram operator `S_{1/2,c}` maps `H_{1/2}` into the domain of the perturbed
Gegenbauer operator `𝒜_c = D_{1/2} - c² M_{u²}` and commutes with it on the whole closed
domain), and reduces it to four analytic lemmas, each stated in full:

* `green_identity`            — the single Green identity on `C²` functions
                                 (two integrations by parts; the boundary terms carry the
                                 factor `1-u²`, which vanishes at `±1`) — **proved**
                                 (`ibp_once`, `green_identity`);
* `SFun_contDiff`             — `u ↦ (S f)(u)` is `C^∞` for every `f ∈ H`: the restriction
                                 of the certified entire Fock evaluation — **proved**;
  `SFun_hasDerivAt`           — the Leibniz derivative of the kernel form (one Mathlib
                                 lemma, `hasDerivAt_integral_of_dominated_loc_of_deriv_le`);
* `core_commutation`          — the pointwise identity `𝒜_c (S p) = S (𝒜_c p)` on the
                                 polynomial core (Leibniz twice, bispectral kernel balance,
                                 Green in the `v` variable);
* `smooth_mem_closure_domain` — every `C²` function lies in the domain of the graph closure of
                                 the polynomial operator `𝒜_c⁰`, on which the closure acts as
                                 the differential expression (Weierstrass approximation of
                                 `g''`, integrated twice; no Legendre coefficient analysis).

Bookkeeping facts:

* `polyLinear_injective`      — two polynomials with the same `L²(ν)` class coincide
                                 (`ν` has no atoms, so the zero set of the difference is
                                 infinite) — **proved**;
* `integral_nu`               — `∫ g dν = ½ ∫_{-1}^{1} g` — **proved** from the certified
                                 density of `ν`;
* `APMap_isClosable`          — `𝒜_c⁰` is closable (densely defined and symmetric on complex
                                 `L²`; the complex counterpart of
                                 `GegenbauerFock.Ultraspherical.sturmRealPMap_isClosable`).

The remaining steps are already kernel-checked in this repository:
the abstract closed-graph-core transport (`Manuscript14Gram.closed_graph_core_commutation`),
the bispectral kernel balance (`Manuscript14Gram.gram_bispectral_kernel_balance`), the
endpoint fluxes, and the bounded complex-`L²` Gram operator with its kernel-integral identity
(`GegenbauerFock.GeneralUltrasphericalFock.gram_eq_integralLp`).

**Status: skeleton in progress.**  Every declaration below is type-checked; the lemmas not
marked as proved carry `sorry`, and the final theorem therefore depends on `sorryAx`.  The axiom audit at the end of
the file prints this explicitly.  This file must NOT be cited as a certificate until that
audit shows no `sorryAx`.

Conventions.  `ν` is the normalised Lebesgue measure of `[-1,1]` (the ultraspherical law at
`λ = 1/2`), `H = L²(ν; ℂ)`.  The Sturm expression of the GegenbauerFock library is
`sturmPolynomial (1/2) p = (1 - X²) p'' - 2 X p' = [(1 - X²) p']'`, so the manuscript's
`D_{1/2} p = -[(1-u²)p']'` is `-sturmPolynomial (1/2) p` and
`𝒜_c p = -sturmPolynomial (1/2) p - c² X² p`.
-/

noncomputable section

open MeasureTheory Polynomial
open scoped Real ContDiff

namespace Manuscript14Gram.Theorem52

/-! ## The Hilbert space and the polynomial core -/

/-- `ν = ν_{1/2}`: the normalised Lebesgue measure of `[-1,1]`. -/
abbrev ν : Measure ℝ := GegenbauerFock.Ultraspherical.measure (1 / 2 : ℝ)

theorem half_pos : (0 : ℝ) < 1 / 2 := by norm_num

instance : IsProbabilityMeasure ν :=
  GegenbauerFock.Ultraspherical.probability (1 / 2 : ℝ) half_pos

/-- `H = H_{1/2}`, the complex `L²` space of `ν`. -/
abbrev H : Type := Lp ℂ 2 ν

/-- Almost every point of `ν` lies in `[-1,1]`. -/
theorem ae_mem_Icc : ∀ᵐ u ∂ν, u ∈ Set.Icc (-1 : ℝ) 1 :=
  GegenbauerFock.Ultraspherical.ae_mem_unit_interval (1 / 2 : ℝ)

/-- `ν` is the normalised Lebesgue measure of `(-1,1)`: `∫ g dν = ½ ∫_{-1}^{1} g` for every
`g : ℝ → ℂ` (from the certified density `measure_half_eq_uniformDensity`). -/
theorem integral_nu (g : ℝ → ℂ) :
    ∫ u, g u ∂ν = (1 / 2 : ℂ) * ∫ u in (-1 : ℝ)..1, g u := by
  have hmeas : Measurable (fun v : ℝ =>
      ENNReal.ofReal (GegenbauerFock.Ultraspherical.eulerianUniformDensity v)) := by
    apply ENNReal.measurable_ofReal.comp
    unfold GegenbauerFock.Ultraspherical.eulerianUniformDensity
    exact Measurable.ite measurableSet_Ioo measurable_const measurable_const
  change ∫ u, g u ∂(GegenbauerFock.Ultraspherical.measure (1 / 2 : ℝ)) = _
  rw [GegenbauerFock.Ultraspherical.measure_half_eq_uniformDensity,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (Filter.Eventually.of_forall fun v => ENNReal.ofReal_lt_top) g]
  have hpt : (fun v : ℝ =>
      (ENNReal.ofReal (GegenbauerFock.Ultraspherical.eulerianUniformDensity v)).toReal • g v)
      = Set.indicator (Set.Ioo (-1 : ℝ) 1) (fun v => (1 / 2 : ℂ) * g v) := by
    funext v
    unfold GegenbauerFock.Ultraspherical.eulerianUniformDensity
    by_cases hv : -1 < v ∧ v < 1
    · have hv' : v ∈ Set.Ioo (-1 : ℝ) 1 := hv
      rw [if_pos hv, ENNReal.toReal_ofReal (by norm_num), Set.indicator_of_mem hv',
        Complex.real_smul]
      push_cast
      ring
    · have hv' : v ∉ Set.Ioo (-1 : ℝ) 1 := hv
      rw [if_neg hv, ENNReal.ofReal_zero, ENNReal.toReal_zero, zero_smul,
        Set.indicator_of_notMem hv']
  rw [hpt, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    intervalIntegral.integral_const_mul]

/-- A continuous function is square integrable for `ν`, since `ν` lives on `[-1,1]`. -/
theorem memLp_of_continuous (g : ℝ → ℂ) (hg : Continuous g) : MemLp g 2 ν := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ u ∈ Set.Icc (-1 : ℝ) 1, ‖g u‖ ≤ M := by
    obtain ⟨M, hM⟩ :=
      (isCompact_Icc.image_of_continuousOn hg.norm.continuousOn).isBounded.bddAbove
    exact ⟨M, fun u hu => hM ⟨u, hu, rfl⟩⟩
  refine MemLp.of_bound hg.aestronglyMeasurable M ?_
  filter_upwards [ae_mem_Icc] with u hu
  exact hM u hu

/-- The `L²` class of a continuous function. -/
def cLp (g : ℝ → ℂ) (hg : Continuous g) : H := (memLp_of_continuous g hg).toLp g

theorem cLp_ae_eq (g : ℝ → ℂ) (hg : Continuous g) : (cLp g hg : ℝ → ℂ) =ᵐ[ν] g :=
  (memLp_of_continuous g hg).coeFn_toLp

/-- The complex polynomial `p` as a function on the real line. -/
def polyFun (p : ℂ[X]) : ℝ → ℂ := fun u => p.eval (u : ℂ)

theorem polyFun_continuous (p : ℂ[X]) : Continuous (polyFun p) :=
  p.continuous.comp Complex.continuous_ofReal

/-- The `L²` class of a complex polynomial. -/
def polyLp (p : ℂ[X]) : H := cLp (polyFun p) (polyFun_continuous p)

theorem polyLp_ae_eq (p : ℂ[X]) : (polyLp p : ℝ → ℂ) =ᵐ[ν] polyFun p :=
  cLp_ae_eq _ _

theorem polyLp_add (p q : ℂ[X]) : polyLp (p + q) = polyLp p + polyLp q := by
  apply Lp.ext
  refine (polyLp_ae_eq (p + q)).trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_add (polyLp p) (polyLp q)).symm
  refine Filter.EventuallyEq.trans ?_ ((polyLp_ae_eq p).add (polyLp_ae_eq q)).symm
  filter_upwards with u
  simp [polyFun]

theorem polyLp_smul (a : ℂ) (p : ℂ[X]) : polyLp (a • p) = a • polyLp p := by
  apply Lp.ext
  refine (polyLp_ae_eq (a • p)).trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_smul a (polyLp p)).symm
  refine Filter.EventuallyEq.trans ?_ ((polyLp_ae_eq p).const_smul a).symm
  filter_upwards with u
  simp [polyFun]

/-- Polynomial evaluation as a linear map `ℂ[X] → H`. -/
def polyLinear : ℂ[X] →ₗ[ℂ] H where
  toFun := polyLp
  map_add' := polyLp_add
  map_smul' := polyLp_smul

/-- Two polynomials with the same `L²(ν)` class are equal:
`ν` is absolutely continuous with a positive density on `(-1,1)`, so the difference vanishes
on an infinite set and is the zero polynomial. -/
theorem polyLinear_injective : Function.Injective polyLinear := by
  intro p q hpq
  by_contra hne
  have hd : p - q ≠ 0 := sub_ne_zero.mpr hne
  have : NullSingletonClass ν :=
    GegenbauerFock.Ultraspherical.measure_nullSingletonClass (1 / 2 : ℝ) half_pos
  have hpq' : polyLp p = polyLp q := hpq
  have hae : polyFun p =ᵐ[ν] polyFun q := by
    refine (polyLp_ae_eq p).symm.trans ?_
    rw [hpq']
    exact polyLp_ae_eq q
  have hz : ∀ᵐ u : ℝ ∂ν, (p - q).eval (u : ℂ) = 0 := by
    filter_upwards [hae] with u hu
    have hu' : p.eval (u : ℂ) = q.eval (u : ℂ) := hu
    simp [hu']
  have hroots : {z : ℂ | (p - q).eval z = 0}.Finite :=
    Polynomial.finite_setOfPred_isRoot hd
  have hfin : {u : ℝ | (p - q).eval (u : ℂ) = 0}.Finite :=
    hroots.preimage Complex.ofReal_injective.injOn
  have hn : ∀ᵐ u : ℝ ∂ν, (p - q).eval (u : ℂ) ≠ 0 := hfin.countable.ae_notMem ν
  have hfalse : ∀ᵐ u ∂ν, False := (hz.and hn).mono (fun _ h => h.2 h.1)
  obtain ⟨_, hu⟩ := hfalse.exists
  exact hu

/-- The polynomial core `𝒫 ⊂ H` as a submodule. -/
abbrev polyCore : Submodule ℂ H := LinearMap.range polyLinear

/-- `𝒫 ≃ ℂ[X]`, the inverse of polynomial evaluation. -/
def polyEquiv : ℂ[X] ≃ₗ[ℂ] polyCore := LinearEquiv.ofInjective polyLinear polyLinear_injective

/-! ## The operator `𝒜_c` -/

/-- The differential expression `𝒜_c g = -[(1-u²) g']' - c² u² g` on functions `ℝ → ℂ`. -/
def AExpr (c : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun u => -(deriv (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) * deriv g t) u)
    - ((c ^ 2 * u ^ 2 : ℝ) : ℂ) * g u

/-- `𝒜_c` on polynomials: `-sturmPolynomial (1/2) p - c² X² p`, as a linear map. -/
def APoly (c : ℝ) : ℂ[X] →ₗ[ℂ] ℂ[X] where
  toFun := fun p =>
    -((1 - X ^ 2) * derivative (derivative p) - C (2 : ℂ) * X * derivative p)
      - C ((c : ℂ) ^ 2) * X ^ 2 * p
  map_add' := by
    intro p q
    simp only [derivative_add, mul_add]
    ring
  map_smul' := by
    intro a p
    simp only [derivative_smul]
    simp only [smul_eq_C_mul, RingHom.id_apply]
    ring

/-- The polynomial-domain operator `𝒜_c⁰ : 𝒫 → H`, `polyLp p ↦ polyLp (APoly c p)`,
as a partially defined linear map with domain `𝒫`. -/
def APMap (c : ℝ) : H →ₗ.[ℂ] H where
  domain := polyCore
  toFun := polyLinear ∘ₗ APoly c ∘ₗ polyEquiv.symm.toLinearMap

theorem polyEquiv_apply (p : ℂ[X]) :
    polyEquiv p = ⟨polyLp p, LinearMap.mem_range_self polyLinear p⟩ := by
  apply Subtype.ext
  rfl

theorem polyEquiv_symm_apply (p : ℂ[X]) (hp : polyLp p ∈ polyCore) :
    polyEquiv.symm ⟨polyLp p, hp⟩ = p := by
  apply polyEquiv.injective
  rw [LinearEquiv.apply_symm_apply, polyEquiv_apply]

theorem APMap_apply (c : ℝ) (p : ℂ[X]) (hp : polyLp p ∈ polyCore) :
    APMap c ⟨polyLp p, hp⟩ = polyLp (APoly c p) := by
  show polyLinear (APoly c (polyEquiv.symm (⟨polyLp p, hp⟩ : polyCore))) = polyLinear (APoly c p)
  rw [polyEquiv_symm_apply]

/-- **Bookkeeping (sorry).**  `𝒜_c⁰` is closable: it is densely defined (Weierstrass) and
symmetric (Green on polynomials), hence contained in its closed adjoint.  This is the complex
counterpart of `GegenbauerFock.Ultraspherical.sturmRealPMap_isClosable`. -/
theorem APMap_isClosable (c : ℝ) : (APMap c).IsClosable := by
  sorry

/-- The closed operator `𝒜_c`: the graph closure of `𝒜_c⁰`. -/
def AClosed (c : ℝ) : H →ₗ.[ℂ] H := (APMap c).closure

theorem AClosed_isClosed (c : ℝ) : (AClosed c).IsClosed :=
  (APMap_isClosable c).closure_isClosed

/-- The polynomials are a graph core of `𝒜_c`. -/
theorem AClosed_hasCore (c : ℝ) : (AClosed c).HasCore (APMap c).domain :=
  LinearPMap.closureHasCore (APMap c)

theorem APMap_le_AClosed (c : ℝ) : APMap c ≤ AClosed c :=
  LinearPMap.le_closure (APMap c)

/-! ## The Gram operator `S_{1/2,c}` -/

/-- `S_{1/2,c}`: the certified bounded selfadjoint operator `gram (1/2) (1/(4c))` of the
GegenbauerFock library, whose kernel is `exp(u v/(4α)) = exp(c u v)`. -/
def S (c : ℝ) (hc : 0 < c) : H →L[ℂ] H :=
  GegenbauerFock.GeneralUltrasphericalFock.gram (1 / 2) (1 / (4 * c)) half_pos
    (by positivity)

/-- The kernel form `(S f)(u) = ∫ exp(c u v) f(v) dν(v)`, as a function of `u`. -/
def SFun (c : ℝ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ v : ℝ, (Real.exp (c * u * v) : ℂ) * f v ∂ν

/-- The kernel form coincides with the library's `gramKernelIntegral` at `α = 1/(4c)`
(parameter identity `u v / (4 · (1/(4c))) = c u v`). -/
theorem SFun_eq_gramKernelIntegral (c : ℝ) (hc : 0 < c) (f : H) (u : ℝ) :
    SFun c (f : ℝ → ℂ) u =
      GegenbauerFock.GeneralUltrasphericalFock.gramKernelIntegral (1 / 2) (1 / (4 * c)) f u := by
  unfold GegenbauerFock.GeneralUltrasphericalFock.gramKernelIntegral SFun
  congr 1
  funext v
  have hc' : c ≠ 0 := ne_of_gt hc
  have : u * v / (4 * (1 / (4 * c))) = c * u * v := by
    field_simp
    try ring
  rw [this, mul_comm]

/-- `S f` is the `L²` class of its kernel form (certified identity `gram_eq_integralLp`). -/
theorem S_apply_ae (c : ℝ) (hc : 0 < c) (f : H) :
    (S c hc f : ℝ → ℂ) =ᵐ[ν] SFun c (f : ℝ → ℂ) := by
  have h1 : S c hc f =
      GegenbauerFock.GeneralUltrasphericalFock.gramKernelIntegralLp (1 / 2) (1 / (4 * c))
        half_pos (by positivity) f :=
    GegenbauerFock.GeneralUltrasphericalFock.gram_eq_integralLp _ _ _ _ f
  rw [h1]
  unfold GegenbauerFock.GeneralUltrasphericalFock.gramKernelIntegralLp
  have h2 := (GegenbauerFock.GeneralUltrasphericalFock.gramKernelIntegral_memLp (1 / 2)
    (1 / (4 * c)) half_pos (by positivity) f).coeFn_toLp
  refine h2.trans ?_
  filter_upwards with u
  exact (SFun_eq_gramKernelIntegral c hc f u).symm

/-- **Lemma 2 (smoothness of `S f`).**  For every `f ∈ H`, `u ↦ (S f)(u)` is `C^n` for
every `n`: by the certified identity `evaluation_imaginary_eq_gramKernelIntegral` it is the
restriction to the segment `u ↦ -i u/(2α)` of the entire function `z ↦ ⟨k_z, C f⟩` of the
Fock model (`differentiable_evaluation_complex`), so no differentiation under the integral
sign is needed for smoothness. -/
theorem SFun_contDiff (c : ℝ) (hc : 0 < c) (f : H) (n : WithTop ℕ∞) :
    ContDiff ℝ n (SFun c (f : ℝ → ℂ)) := by
  have hα : (0 : ℝ) < 1 / (4 * c) := by positivity
  have hE : Differentiable ℂ (fun z : ℂ =>
      GegenbauerFock.FockEvaluation.evaluation (1 / (4 * c)) hα z
        (GegenbauerFock.GeneralUltrasphericalFock.C (1 / 2) (1 / (4 * c)) half_pos hα f)) :=
    GegenbauerFock.FockEvaluation.differentiable_evaluation_complex (1 / (4 * c)) hα _
  have hfun : SFun c (f : ℝ → ℂ) = fun u : ℝ =>
      GegenbauerFock.FockEvaluation.evaluation (1 / (4 * c)) hα
        (-Complex.I * (u : ℂ) / (2 * ((1 / (4 * c) : ℝ) : ℂ)))
        (GegenbauerFock.GeneralUltrasphericalFock.C (1 / 2) (1 / (4 * c)) half_pos hα f) := by
    funext u
    rw [SFun_eq_gramKernelIntegral c hc f u,
      ← GegenbauerFock.GeneralUltrasphericalFock.evaluation_imaginary_eq_gramKernelIntegral
        (1 / 2) (1 / (4 * c)) half_pos hα f u]
  rw [hfun]
  have hlin : ContDiff ℝ n (fun u : ℝ =>
      -Complex.I * (u : ℂ) / (2 * ((1 / (4 * c) : ℝ) : ℂ))) := by
    have h := ((contDiff_const (c := -Complex.I)).mul
      (Complex.ofRealCLM.contDiff (𝕜 := ℝ) (n := n))).div_const (2 * ((1 / (4 * c) : ℝ) : ℂ))
    simpa using h
  exact (hE.contDiff.restrict_scalars (𝕜 := ℝ)).comp hlin

/-- The Leibniz derivative of the kernel form: `(S f)'(u) = ∫ c v e^{c u v} f(v) dν(v)`.
Proof: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the kernel derivative
`∂_u e^{c u v} = c v e^{c u v}`, bounded on `[-1,1]` by `c e^{c(|u|+1)}`, and `f ∈ L¹(ν)`. -/
theorem SFun_hasDerivAt (c : ℝ) (hc : 0 < c) (f : H) (u : ℝ) :
    HasDerivAt (SFun c (f : ℝ → ℂ))
      (∫ v : ℝ, ((c * v : ℝ) : ℂ) * (Real.exp (c * u * v) : ℂ) * f v ∂ν) u := by
  have hfint : Integrable (f : ℝ → ℂ) ν := (Lp.memLp f).integrable one_le_two
  set M : ℝ := Real.exp (c * (|u| + 1)) with hM
  have hker : ∀ x ∈ Metric.ball u 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      Real.exp (c * x * v) ≤ M := by
    intro x hx v hv
    rw [hM, Real.exp_le_exp]
    have hdist : |x - u| < 1 := by
      have := Metric.mem_ball.mp hx
      rwa [Real.dist_eq] at this
    have h1 : |x| ≤ |u| + 1 := by
      calc |x| = |(x - u) + u| := by ring_nf
        _ ≤ |x - u| + |u| := abs_add_le _ _
        _ ≤ |u| + 1 := by linarith
    have h2 : |v| ≤ 1 := abs_le.mpr ⟨hv.1, hv.2⟩
    calc c * x * v ≤ |c * x * v| := le_abs_self _
      _ = c * (|x| * |v|) := by rw [abs_mul, abs_mul, abs_of_pos hc]; ring
      _ ≤ c * ((|u| + 1) * 1) := by gcongr
      _ = c * (|u| + 1) := by ring
  have hF_meas : ∀ x : ℝ,
      AEStronglyMeasurable (fun v : ℝ => (Real.exp (c * x * v) : ℂ) * f v) ν := by
    intro x
    exact (Continuous.aestronglyMeasurable (by fun_prop)).mul (Lp.aestronglyMeasurable f)
  have hF'_meas : ∀ x : ℝ, AEStronglyMeasurable
      (fun v : ℝ => ((c * v : ℝ) : ℂ) * (Real.exp (c * x * v) : ℂ) * f v) ν := by
    intro x
    exact (Continuous.aestronglyMeasurable (by fun_prop)).mul (Lp.aestronglyMeasurable f)
  have hFint : Integrable (fun v : ℝ => (Real.exp (c * u * v) : ℂ) * f v) ν := by
    refine hfint.bdd_mul (c := M) (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [ae_mem_Icc] with v hv
    rw [Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    exact hker u (Metric.mem_ball_self one_pos) v hv
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun x v => (Real.exp (c * x * v) : ℂ) * f v)
    (F' := fun x v => ((c * v : ℝ) : ℂ) * (Real.exp (c * x * v) : ℂ) * f v)
    (x₀ := u) (s := Metric.ball u 1) (bound := fun v => c * M * ‖f v‖)
    (Metric.ball_mem_nhds u one_pos) (Filter.Eventually.of_forall hF_meas) hFint
    (hF'_meas u) ?_ (hfint.norm.const_mul (c * M)) ?_
  · exact key.2
  · filter_upwards [ae_mem_Icc] with v hv x hx
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.abs_exp, abs_mul, abs_of_pos hc]
    have h2 : |v| ≤ 1 := abs_le.mpr ⟨hv.1, hv.2⟩
    have h3 := hker x hx v hv
    calc c * |v| * Real.exp (c * x * v) * ‖f v‖ ≤ c * 1 * M * ‖f v‖ := by gcongr
      _ = c * M * ‖f v‖ := by ring
  · filter_upwards with v x _
    have h1 : HasDerivAt (fun x : ℝ => c * x * v) (c * v) x := by
      simpa using ((hasDerivAt_id x).const_mul c).mul_const v
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (c * x * v))
        (Real.exp (c * x * v) * (c * v)) x := h1.exp
    have h3 := (h2.ofReal_comp).mul_const (f v)
    convert h3 using 1
    push_cast
    ring

/-! ## The four analytic lemmas -/

/-- `C¹`-regularity of the factor `t ↦ (1 - t²)` viewed in `ℂ`. -/
theorem contDiff_oneSubSq : ContDiff ℝ 1 (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ)) := by
  have h := (Complex.ofRealCLM.contDiff (𝕜 := ℝ) (n := 1)).comp
    ((contDiff_const (c := (1 : ℝ))).sub (contDiff_id.pow 2))
  simpa [Function.comp_def] using h

/-- One integration by parts on `[-1,1]`: `∫ [(1-u²) f']' g = -∫ (1-u²) f' g'`.  The boundary
term `g · (1-u²) f'` vanishes at `±1`. -/
theorem ibp_once (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    ∫ u in (-1 : ℝ)..1, deriv (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) * deriv f t) u * g u
      = -∫ u in (-1 : ℝ)..1, ((1 - u ^ 2 : ℝ) : ℂ) * deriv f u * deriv g u := by
  set φ : ℝ → ℂ := fun t => ((1 - t ^ 2 : ℝ) : ℂ) * deriv f t with hφdef
  have hf2 : ContDiff ℝ (1 + 1) f := by norm_num; exact hf
  have hfd : ContDiff ℝ 1 (deriv f) := hf2.deriv'
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hφC1 : ContDiff ℝ 1 φ := contDiff_oneSubSq.mul hfd
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := g) (v := φ) (u' := deriv g) (v' := deriv φ) (a := -1) (b := 1)
    (fun x _ => (hg1.differentiable one_ne_zero x).hasDerivAt)
    (fun x _ => (hφC1.differentiable one_ne_zero x).hasDerivAt)
    ((hg1.continuous_deriv le_rfl).intervalIntegrable _ _)
    ((hφC1.continuous_deriv le_rfl).intervalIntegrable _ _)
  have hφ1 : φ 1 = 0 := by norm_num [hφdef]
  have hφm1 : φ (-1) = 0 := by norm_num [hφdef]
  rw [hφ1, hφm1] at key
  simp only [mul_zero, sub_zero, zero_sub] at key
  calc ∫ u in (-1 : ℝ)..1, deriv φ u * g u
      = ∫ u in (-1 : ℝ)..1, g u * deriv φ u := by
        apply intervalIntegral.integral_congr
        intro u _
        ring
    _ = -∫ u in (-1 : ℝ)..1, deriv g u * φ u := key
    _ = -∫ u in (-1 : ℝ)..1, ((1 - u ^ 2 : ℝ) : ℂ) * deriv f u * deriv g u := by
        congr 1
        apply intervalIntegral.integral_congr
        intro u _
        simp only [hφdef]
        ring

/-- **Lemma 1 (Green).**  For `f, g` of class `C²` on the real line,
`∫_{-1}^{1} [(1-u²) f']' g = ∫_{-1}^{1} f [(1-u²) g']'`: both sides equal
`-∫_{-1}^{1} (1-u²) f' g'` by `ibp_once`. -/
theorem green_identity (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    ∫ u in (-1 : ℝ)..1, deriv (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) * deriv f t) u * g u
      = ∫ u in (-1 : ℝ)..1,
          f u * deriv (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) * deriv g t) u := by
  rw [ibp_once f g hf hg]
  have h2 := ibp_once g f hg hf
  have h3 : ∫ u in (-1 : ℝ)..1,
        f u * deriv (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) * deriv g t) u
      = ∫ u in (-1 : ℝ)..1,
        deriv (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) * deriv g t) u * f u := by
    apply intervalIntegral.integral_congr
    intro u _
    ring
  rw [h3, h2]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  ring

/-! ### Calculus of polynomials, of the kernel and of `S` on polynomials -/

/-- Derivative of a polynomial along the real line. -/
theorem polyFun_hasDerivAt (p : ℂ[X]) (u : ℝ) :
    HasDerivAt (polyFun p) ((derivative p).eval (u : ℂ)) u :=
  (Polynomial.hasDerivAt p (u : ℂ)).comp_ofReal

theorem polyFun_deriv (p : ℂ[X]) : deriv (polyFun p) = polyFun (derivative p) := by
  funext u
  exact (polyFun_hasDerivAt p u).deriv

theorem polyFun_contDiff (p : ℂ[X]) (n : WithTop ℕ∞) : ContDiff ℝ n (polyFun p) := by
  have h := ((Polynomial.differentiable p).contDiff (n := n)).restrict_scalars (𝕜 := ℝ)
    |>.comp (Complex.ofRealCLM.contDiff (𝕜 := ℝ) (n := n))
  unfold polyFun
  simpa [Function.comp_def] using h

/-- `(1-t²) · (polyFun p)'` is the polynomial `(1 - X²) p'`. -/
theorem oneSubSq_mul_deriv_polyFun (p : ℂ[X]) :
    (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) * deriv (polyFun p) t)
      = polyFun ((1 - X ^ 2) * derivative p) := by
  funext t
  rw [polyFun_deriv]
  simp only [polyFun, eval_mul, eval_sub, eval_one, eval_pow, eval_X]
  push_cast
  ring

/-- The kernel `t ↦ e^{c u t}` as a complex-valued function of the real variable `t`. -/
def ker (c u t : ℝ) : ℂ := (Real.exp (c * u * t) : ℂ)

theorem ker_hasDerivAt (c u t : ℝ) :
    HasDerivAt (ker c u) (((c * u : ℝ) : ℂ) * ker c u t) t := by
  have h1 : HasDerivAt (fun t : ℝ => c * u * t) (c * u) t := by
    simpa using (hasDerivAt_id t).const_mul (c * u)
  have h2 := (h1.exp).ofReal_comp
  have h3 : HasDerivAt (ker c u) ((Real.exp (c * u * t) * (c * u) : ℝ) : ℂ) t := h2
  convert h3 using 1
  unfold ker
  push_cast
  ring

theorem ker_contDiff (c u : ℝ) (n : WithTop ℕ∞) : ContDiff ℝ n (ker c u) := by
  have h := (Complex.ofRealCLM.contDiff (𝕜 := ℝ) (n := n)).comp
    (Real.contDiff_exp.comp ((contDiff_const (c := c * u)).mul contDiff_id))
  unfold ker
  simpa [Function.comp_def, Complex.ofReal_exp] using h

/-- Derivative of `(1-t²) (ker c u)'` at `v`: `[(-2 c u) v + c² u² (1 - v²)] e^{c u v}`. -/
theorem oneSubSq_mul_deriv_ker_hasDerivAt (c u v : ℝ) :
    HasDerivAt (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) * deriv (ker c u) t)
      ((((-2 * c * u) * v + c ^ 2 * u ^ 2 * (1 - v ^ 2) : ℝ) : ℂ) * ker c u v) v := by
  have hd : deriv (ker c u) = fun t => ((c * u : ℝ) : ℂ) * ker c u t := by
    funext t
    exact (ker_hasDerivAt c u t).deriv
  rw [hd]
  have ha : HasDerivAt (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ)) (((-(2 * v)) : ℝ) : ℂ) v := by
    have := ((hasDerivAt_pow 2 v).const_sub 1).ofReal_comp
    convert this using 1
    push_cast
    ring
  have hb := (ker_hasDerivAt c u v).const_mul (((c * u : ℝ) : ℂ))
  convert ha.mul hb using 1
  unfold ker
  push_cast
  ring

/-- Continuous functions are `ν`-integrable. -/
theorem integrable_of_continuous (g : ℝ → ℂ) (hg : Continuous g) : Integrable g ν :=
  (memLp_of_continuous g hg).integrable one_le_two

/-- The kernel form of `S` on the `L²` class of a polynomial is its kernel form on the
polynomial itself. -/
theorem SFun_polyLp (c : ℝ) (p : ℂ[X]) :
    SFun c (polyLp p : ℝ → ℂ) = SFun c (polyFun p) := by
  funext u
  unfold SFun
  apply integral_congr_ae
  filter_upwards [polyLp_ae_eq p] with v hv
  rw [hv]

theorem SFun_poly_contDiff (c : ℝ) (hc : 0 < c) (p : ℂ[X]) (n : WithTop ℕ∞) :
    ContDiff ℝ n (SFun c (polyFun p)) := by
  rw [← SFun_polyLp]
  exact SFun_contDiff c hc (polyLp p) n

/-- `(S p)' = c · S (X p)` on polynomials. -/
theorem SFun_poly_hasDerivAt (c : ℝ) (hc : 0 < c) (p : ℂ[X]) (u : ℝ) :
    HasDerivAt (SFun c (polyFun p)) ((c : ℂ) * SFun c (polyFun (X * p)) u) u := by
  have h := SFun_hasDerivAt c hc (polyLp p) u
  rw [SFun_polyLp] at h
  convert h using 1
  unfold SFun
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [polyLp_ae_eq p] with v hv
  rw [hv]
  simp only [polyFun, eval_mul, eval_X]
  push_cast
  ring

theorem SFun_poly_deriv (c : ℝ) (hc : 0 < c) (p : ℂ[X]) :
    deriv (SFun c (polyFun p)) = fun u => (c : ℂ) * SFun c (polyFun (X * p)) u := by
  funext u
  exact (SFun_poly_hasDerivAt c hc p u).deriv

/-- `S q (u) = ∫ e^{c u v} q(v) dν(v)` written with the kernel `ker`. -/
theorem SFun_poly_eq (c u : ℝ) (q : ℂ[X]) :
    SFun c (polyFun q) u = ∫ v, ker c u v * polyFun q v ∂ν := rfl

/-- **Lemma 3 (commutation on the core).**  For a polynomial `p`,
`𝒜_c (S p) = S (𝒜_c p)` pointwise.  Proof: `SFun_poly_hasDerivAt` twice gives
`𝒜_c (S p)(u) = ∫ e^{c u v} [2cu v - (1-u²)c² v² - c² u²] p(v) dν(v)`; `green_identity` in the
`v` variable (with `p` in place of `f` and the kernel in place of `g`) and `integral_nu`
give `S (𝒜_c p)(u) = ∫ e^{c u v} [2cu v - c² v² + c²u² v² - c² u²] p(v) dν(v)`; the two
polynomial weights coincide (this is the bispectral balance
`Manuscript14Gram.gram_differential_symbol_symmetric`). -/
theorem core_commutation (c : ℝ) (hc : 0 < c) (p : ℂ[X]) :
    ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      AExpr c (SFun c (polyFun p)) u = SFun c (polyFun (APoly c p)) u := by
  intro u _
  -- integrability of the integrands that occur
  have hint : ∀ q : ℂ[X], Integrable (fun v => ker c u v * polyFun q v) ν := fun q =>
    integrable_of_continuous _ (((ker_contDiff c u 0).continuous).mul (polyFun_continuous q))
  -- left-hand side: two derivatives of `S p`
  have hprod : HasDerivAt
      (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) * deriv (SFun c (polyFun p)) t)
      ((((-(2 * u)) : ℝ) : ℂ) * ((c : ℂ) * SFun c (polyFun (X * p)) u)
        + ((1 - u ^ 2 : ℝ) : ℂ) * ((c : ℂ) * ((c : ℂ) * SFun c (polyFun (X * (X * p))) u))) u := by
    rw [SFun_poly_deriv c hc p]
    have ha : HasDerivAt (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ)) (((-(2 * u)) : ℝ) : ℂ) u := by
      have := ((hasDerivAt_pow 2 u).const_sub 1).ofReal_comp
      convert this using 1
      push_cast
      ring
    exact ha.mul ((SFun_poly_hasDerivAt c hc (X * p) u).const_mul (c : ℂ))
  have hL : AExpr c (SFun c (polyFun p)) u
      = ∫ v, ker c u v * polyFun p v
          * (((2 * c * u) * v - (1 - u ^ 2) * c ^ 2 * v ^ 2 - c ^ 2 * u ^ 2 : ℝ) : ℂ) ∂ν := by
    unfold AExpr
    rw [hprod.deriv, SFun_poly_eq, SFun_poly_eq, SFun_poly_eq]
    have hsplit : ∫ v, ker c u v * polyFun p v
          * (((2 * c * u) * v - (1 - u ^ 2) * c ^ 2 * v ^ 2 - c ^ 2 * u ^ 2 : ℝ) : ℂ) ∂ν
        = ∫ v, (((2 * c * u : ℝ) : ℂ) * (ker c u v * polyFun (X * p) v)
            - (((1 - u ^ 2) * c ^ 2 : ℝ) : ℂ) * (ker c u v * polyFun (X * (X * p)) v))
            - ((c ^ 2 * u ^ 2 : ℝ) : ℂ) * (ker c u v * polyFun p v) ∂ν := by
      apply integral_congr_ae
      filter_upwards with v
      simp only [polyFun, eval_mul, eval_X]
      push_cast
      ring
    have h1 : Integrable (fun v => ((2 * c * u : ℝ) : ℂ) * (ker c u v * polyFun (X * p) v)) ν :=
      (hint _).const_mul _
    have h2 : Integrable (fun v => (((1 - u ^ 2) * c ^ 2 : ℝ) : ℂ)
        * (ker c u v * polyFun (X * (X * p)) v)) ν := (hint _).const_mul _
    have h3 : Integrable (fun v => ((c ^ 2 * u ^ 2 : ℝ) : ℂ) * (ker c u v * polyFun p v)) ν :=
      (hint _).const_mul _
    have h12 : Integrable (fun v => ((2 * c * u : ℝ) : ℂ) * (ker c u v * polyFun (X * p) v)
        - (((1 - u ^ 2) * c ^ 2 : ℝ) : ℂ) * (ker c u v * polyFun (X * (X * p)) v)) ν := h1.sub h2
    rw [hsplit, integral_sub h12 h3, integral_sub h1 h2, integral_const_mul,
      integral_const_mul, integral_const_mul]
    push_cast
    ring
  -- right-hand side: Green in the `v` variable
  have hG := green_identity (ker c u) (polyFun p) (ker_contDiff c u 2) (polyFun_contDiff p 2)
  rw [oneSubSq_mul_deriv_polyFun p, polyFun_deriv] at hG
  have hR : SFun c (polyFun (APoly c p)) u
      = ∫ v, ker c u v * polyFun p v
          * (((2 * c * u) * v - c ^ 2 * v ^ 2 + c ^ 2 * u ^ 2 * v ^ 2 - c ^ 2 * u ^ 2 : ℝ) : ℂ) ∂ν := by
    have h1 : SFun c (polyFun (APoly c p)) u
        = ∫ v, -(ker c u v * polyFun (derivative ((1 - X ^ 2) * derivative p)) v)
          - ((c : ℂ) ^ 2) * (ker c u v * polyFun (X ^ 2 * p) v) ∂ν := by
      rw [SFun_poly_eq]
      apply integral_congr_ae
      filter_upwards with v
      simp only [polyFun, APoly, LinearMap.coe_mk, AddHom.coe_mk, eval_sub, eval_neg, eval_mul,
        eval_add, eval_one, eval_zero, eval_pow, eval_X, eval_C, derivative_mul, derivative_sub,
        derivative_one, derivative_X_sq]
      push_cast
      ring
    have h2 : ∫ v, ker c u v * polyFun (derivative ((1 - X ^ 2) * derivative p)) v ∂ν
        = ∫ v, ker c u v * polyFun p v
            * ((((-2 * c * u) * v + c ^ 2 * u ^ 2 * (1 - v ^ 2) : ℝ) : ℂ)) ∂ν := by
      rw [integral_nu, integral_nu]
      congr 1
      rw [← hG]
      apply intervalIntegral.integral_congr
      intro v _
      beta_reduce
      rw [(oneSubSq_mul_deriv_ker_hasDerivAt c u v).deriv]
      ring
    have hn : Integrable (fun v => -(ker c u v
        * polyFun (derivative ((1 - X ^ 2) * derivative p)) v)) ν := (hint _).neg
    have hm : Integrable (fun v => ((c : ℂ) ^ 2) * (ker c u v * polyFun (X ^ 2 * p) v)) ν :=
      (hint _).const_mul _
    rw [h1, integral_sub hn hm, integral_neg, integral_const_mul, h2]
    have hsplit : ∫ v, ker c u v * polyFun p v
          * (((2 * c * u) * v - c ^ 2 * v ^ 2 + c ^ 2 * u ^ 2 * v ^ 2 - c ^ 2 * u ^ 2 : ℝ) : ℂ) ∂ν
        = ∫ v, -(ker c u v * polyFun p v
            * ((((-2 * c * u) * v + c ^ 2 * u ^ 2 * (1 - v ^ 2) : ℝ) : ℂ)))
            - ((c : ℂ) ^ 2) * (ker c u v * polyFun (X ^ 2 * p) v) ∂ν := by
      apply integral_congr_ae
      filter_upwards with v
      simp only [polyFun, eval_mul, eval_pow, eval_X]
      push_cast
      ring
    have hq : Integrable (fun v => -(ker c u v * polyFun p v
        * ((((-2 * c * u) * v + c ^ 2 * u ^ 2 * (1 - v ^ 2) : ℝ) : ℂ)))) ν := by
      refine (integrable_of_continuous _ ?_).neg
      exact ((ker_contDiff c u 0).continuous.mul (polyFun_continuous p)).mul (by fun_prop)
    rw [hsplit, integral_sub hq hm, integral_neg, integral_const_mul]
  rw [hL, hR]
  apply integral_congr_ae
  filter_upwards with v
  push_cast
  ring

/-- **Lemma 4 (domain inclusion).**  Every `C²` function `g` defines an element of the domain
of the closed operator `𝒜_c`, on which `𝒜_c` acts as the differential expression `AExpr c g`
(almost everywhere).  Proof: by Weierstrass, choose polynomials `q_n → g''` uniformly on
`[-1,1]`; put `p_n(u) = g(-1) + g'(-1)(u+1) + ∫_{-1}^{u}∫_{-1}^{t} q_n`.  Then
`p_n, p_n', p_n'' → g, g', g''` uniformly on `[-1,1]`, so `p_n → g` and `𝒜_c p_n → AExpr c g`
in `L²(ν)`, and the graph closure contains the limit.  No Legendre coefficient analysis is
needed. -/
theorem smooth_mem_closure_domain (c : ℝ) (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) :
    ∃ hmem : cLp g hg.continuous ∈ (AClosed c).domain,
      ((AClosed c) ⟨cLp g hg.continuous, hmem⟩ : ℝ → ℂ) =ᵐ[ν] AExpr c g := by
  sorry

/-! ## Theorem 5.2 -/

/-- **Theorem 5.2 (domain-level commutation), first half:** `S_{1/2,c} H ⊂ Dom(𝒜_c)`.
From `SFun_contDiff`, Lemma 4 and the kernel identity `S_apply_ae`; it is complete as soon
as Lemma 4 is. -/
theorem S_range_subset_domain (c : ℝ) (hc : 0 < c) (f : H) :
    S c hc f ∈ (AClosed c).domain := by
  have hs : ContDiff ℝ 2 (SFun c (f : ℝ → ℂ)) := SFun_contDiff c hc f 2
  have heq : S c hc f = cLp (SFun c (f : ℝ → ℂ)) hs.continuous := by
    apply Lp.ext
    exact (S_apply_ae c hc f).trans (cLp_ae_eq _ _).symm
  rw [heq]
  obtain ⟨hmem, _⟩ := smooth_mem_closure_domain c (SFun c (f : ℝ → ℂ)) hs
  exact hmem

/-- **Theorem 5.2 (domain-level commutation), second half:** for every `f ∈ Dom(𝒜_c)`,
`𝒜_c S_{1/2,c} f = S_{1/2,c} 𝒜_c f`.  Assembled from Lemmas 2, 3, 4 through the abstract
transport theorem `Manuscript14Gram.closed_graph_core_commutation`, with `D = Dom(𝒜_c)`,
`Core = 𝒫`, `hcore` from `AClosed_hasCore`, `hclosed` from `AClosed_isClosed`. -/
theorem gram_commutes_with_perturbed_legendre (c : ℝ) (hc : 0 < c)
    (f : (AClosed c).domain) :
    (AClosed c) ⟨S c hc f, S_range_subset_domain c hc f⟩ = S c hc ((AClosed c) f) := by
  sorry

#print axioms Manuscript14Gram.Theorem52.S_range_subset_domain
#print axioms Manuscript14Gram.Theorem52.gram_commutes_with_perturbed_legendre

end Manuscript14Gram.Theorem52

end
