import Mathlib
import SpecialImaginaryPoint.GramKernelBispectral
import GegenbauerFock.GramIntegralComplete
import GegenbauerFock.UltrasphericalSturmLiouvillePolynomialCore
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2Nonzero
import GegenbauerFock.UltrasphericalLegendreDensityExact
import GegenbauerFock.OutputComplexHolomorphy
import GegenbauerFock.UltrasphericalContinuousDensity

/-!
# Manuscript 14, Theorem 5.2 (domain-level commutation): complete kernel-checked proof

This module proves, in Lean 4, Theorem 5.2 of manuscript 14: the Legendre–Gram operator
`S_{1/2,c}` maps `H_{1/2}` into the domain of the perturbed Gegenbauer operator
`𝒜_c = D̄ - c² M_{u²}` (`S_range_subset_domain`) and commutes with it on the whole closed
domain (`gram_commutes_with_perturbed_legendre`), for every `c > 0`.  Here `D̄` is the graph
closure of the Legendre operator `D⁰ p = -[(1 - u²) p']'` on the polynomials of `L²(ν_{1/2}; ℂ)`,
`M_{u²}` the bounded multiplication operator, and `S_{1/2,c} = gram (1/2, 1/(4c))` the certified
Gram operator of the GegenbauerFock library (Definition 5.1 of the manuscript).

Structure of the proof.

* `green_identity` (`ibp_once`): the single Green identity on `C²` functions; the boundary
  terms carry the factor `1 - u²`, which vanishes at `±1`.
* `SFun_contDiff`: `u ↦ (S f)(u)` is `C^∞` for every `f ∈ H`, as the restriction of the certified
  entire Fock evaluation (`differentiable_evaluation_complex`) through the certified identity
  `evaluation_imaginary_eq_gramKernelIntegral`; `SFun_hasDerivAt`: the Leibniz derivative of
  the kernel form.
* `core_commutation`: `𝒜_c (S p) = S (𝒜_c p)` pointwise for polynomials `p` (Leibniz twice,
  the bispectral balance of the kernel as a polynomial identity, Green in the `v` variable).
* `polyCore_dense`, `DPMap_formalSymmetric`, `DPMap_isClosable`: the polynomials are dense
  (Weierstrass, real and imaginary parts, and the certified density of the bounded continuous
  functions), `D⁰` is symmetric (Green) and hence closable.
* `mem_closure_domain_of_adjoint_relation`: the abstract criterion `Dom(A*) ⊆ Dom(Ā)` for a
  symmetric `A` with `‖p‖ ≤ ‖A p + p‖` and `Ran(A + I)` dense; `DPMap_coercive`
  (`⟪D⁰ p, p⟫ = ½ ∫ (1-v²)|p'|² ≥ 0`) and `range_T_dense` (`D⁰ + I` is an injective, hence
  surjective, endomorphism of each `degreeLT`) supply its hypotheses, and
  `smooth_mem_closure_domain` (Lemma 4) follows from Green (`inner_DPoly_cLp`).
* The assembly uses the abstract transport theorem
  `Manuscript14Gram.closed_graph_core_commutation` with `D = Dom(D̄)`, `Core = 𝒫`,
  `hcore = Afun_core`, `hclosed = Afun_closed`, `hcomm = AClosed_S_polyLp`.

Imported certified inputs: `Manuscript14Gram.gram_differential_symbol_symmetric` (kernel
balance), the GegenbauerFock Gram operator with `gram_eq_integralLp`, the Fock holomorphy,
the density of ν, `measure_nullSingletonClass`, `boundedContinuous_toLp_denseRange` and
`eLpNorm_sub_le_of_uniform_error_unit_interval`.

**Status: complete.**  The axiom audit at the end of the file lists only `propext`,
`Classical.choice` and `Quot.sound` for both statements (no `sorryAx`, no
`Lean.ofReduceBool`).

Conventions.  `ν` is the normalised Lebesgue measure of `[-1,1]` (the ultraspherical law at
`λ = 1/2`), `H = L²(ν; ℂ)`.  The Sturm expression of the GegenbauerFock library is
`sturmPolynomial (1/2) p = (1 - X²) p'' - 2 X p' = [(1 - X²) p']'`, so the manuscript's
`D_{1/2} p = -[(1-u²)p']'` is `-sturmPolynomial (1/2) p` and
`𝒜_c p = -sturmPolynomial (1/2) p - c² X² p`.
-/

noncomputable section

open MeasureTheory Polynomial
open scoped Real ContDiff InnerProductSpace ENNReal

namespace Manuscript14Gram.Theorem52

/-! ## The Hilbert space and the polynomial core -/

/-- `ν = ν_{1/2}`: the normalised Lebesgue measure of `[-1,1]`. -/
abbrev ν : Measure ℝ := GegenbauerFock.Ultraspherical.measure (1 / 2 : ℝ)

theorem hhalf : (0 : ℝ) < 1 / 2 := by norm_num

instance : IsProbabilityMeasure ν :=
  GegenbauerFock.Ultraspherical.probability (1 / 2 : ℝ) hhalf

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
    GegenbauerFock.Ultraspherical.measure_nullSingletonClass (1 / 2 : ℝ) hhalf
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

theorem polyLp_mem (p : ℂ[X]) : polyLp p ∈ polyCore := ⟨p, rfl⟩

/-- `𝒫 ≃ ℂ[X]`, the inverse of polynomial evaluation. -/
def polyEquiv : ℂ[X] ≃ₗ[ℂ] polyCore := LinearEquiv.ofInjective polyLinear polyLinear_injective

/-! ## The operators `D_{1/2}`, `M_{u²}` and `𝒜_c` -/

/-- The differential expression `𝒜_c g = -[(1-u²) g']' - c² u² g` on functions `ℝ → ℂ`. -/
def AExpr (c : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun u => -(deriv (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) * deriv g t) u)
    - ((c ^ 2 * u ^ 2 : ℝ) : ℂ) * g u

/-- The differential expression `D_{1/2} g = -[(1-u²) g']'`. -/
def DExpr (g : ℝ → ℂ) : ℝ → ℂ :=
  fun u => -(deriv (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) * deriv g t) u)

theorem AExpr_eq (c : ℝ) (g : ℝ → ℂ) (u : ℝ) :
    AExpr c g u = DExpr g u - ((c ^ 2 * u ^ 2 : ℝ) : ℂ) * g u := rfl

/-- `D_{1/2}` on polynomials: `-sturmPolynomial (1/2) p = -[(1 - X²) p']'`, as a linear map. -/
def DPoly : ℂ[X] →ₗ[ℂ] ℂ[X] where
  toFun := fun p => -((1 - X ^ 2) * derivative (derivative p) - C (2 : ℂ) * X * derivative p)
  map_add' := by
    intro p q
    simp only [derivative_add]
    ring
  map_smul' := by
    intro a p
    simp only [derivative_smul]
    simp only [smul_eq_C_mul, RingHom.id_apply]
    ring

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

theorem APoly_eq (c : ℝ) (p : ℂ[X]) : APoly c p = DPoly p - C ((c : ℂ) ^ 2) * X ^ 2 * p := rfl

theorem DPoly_apply (p : ℂ[X]) :
    DPoly p = -((1 - X ^ 2) * derivative (derivative p) - C (2 : ℂ) * X * derivative p) := rfl

theorem DPoly_eq_neg_derivative (p : ℂ[X]) :
    DPoly p = -derivative ((1 - X ^ 2) * derivative p) := by
  rw [DPoly_apply, derivative_mul, derivative_sub, derivative_one, derivative_X_sq]
  ring

theorem polyEquiv_apply (p : ℂ[X]) :
    polyEquiv p = ⟨polyLp p, polyLp_mem p⟩ := by
  apply Subtype.ext
  rfl

theorem polyEquiv_symm_apply (p : ℂ[X]) (hp : polyLp p ∈ polyCore) :
    polyEquiv.symm ⟨polyLp p, hp⟩ = p := by
  apply polyEquiv.injective
  rw [LinearEquiv.apply_symm_apply, polyEquiv_apply]

/-- The polynomial-domain operator `D⁰ : 𝒫 → H`, `polyLp p ↦ polyLp (DPoly p)`, as a
partially defined linear map with domain `𝒫`. -/
abbrev DPMap : H →ₗ.[ℂ] H where
  domain := polyCore
  toFun := polyLinear ∘ₗ DPoly ∘ₗ polyEquiv.symm.toLinearMap

theorem DPMap_apply (p : ℂ[X]) (hp : polyLp p ∈ polyCore) :
    DPMap ⟨polyLp p, hp⟩ = polyLp (DPoly p) := by
  show polyLinear (DPoly (polyEquiv.symm (⟨polyLp p, hp⟩ : polyCore))) = polyLinear (DPoly p)
  rw [polyEquiv_symm_apply]

/-- The closed operator `D̄ = D_{1/2}`: the graph closure of `D⁰`.  (Its closability,
`DPMap_isClosable`, is proved below from symmetry and density.) -/
def DClosed : H →ₗ.[ℂ] H := DPMap.closure

theorem DPMap_le_DClosed : DPMap ≤ DClosed := LinearPMap.le_closure DPMap

/-- The polynomials are a graph core of `D̄`. -/
theorem DClosed_hasCore : DClosed.HasCore DPMap.domain := LinearPMap.closureHasCore DPMap

/-! ### The multiplication operator `M_{u²}` -/

/-- A bounded continuous function equal to `u²` on `[-1,1]`. -/
def usq (u : ℝ) : ℝ := (max (-1) (min u 1)) ^ 2

theorem usq_continuous : Continuous usq := by
  unfold usq
  fun_prop

theorem usq_eq {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) : usq u = u ^ 2 := by
  unfold usq
  rw [min_eq_left hu.2, max_eq_right hu.1]

theorem usq_abs_le_one (u : ℝ) : |usq u| ≤ 1 := by
  unfold usq
  have h1 : -1 ≤ max (-1) (min u 1) := le_max_left _ _
  have h2 : max (-1) (min u 1) ≤ 1 := max_le (by norm_num) (min_le_right _ _)
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith

/-- `u ↦ u² f(u)` with the bounded version of `u²`. -/
def mulUsqFun (f : ℝ → ℂ) : ℝ → ℂ := fun u => (usq u : ℂ) * f u

theorem usq_complex_continuous : Continuous (fun u : ℝ => (usq u : ℂ)) :=
  Complex.continuous_ofReal.comp usq_continuous

theorem mulUsqFun_norm_le (f : ℝ → ℂ) (u : ℝ) : ‖mulUsqFun f u‖ ≤ ‖f u‖ := by
  unfold mulUsqFun
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |usq u| * ‖f u‖ ≤ 1 * ‖f u‖ := by gcongr; exact usq_abs_le_one u
    _ = ‖f u‖ := one_mul _

theorem mulUsqFun_memLp (f : H) : MemLp (mulUsqFun f) 2 ν :=
  (Lp.memLp f).of_le (usq_complex_continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun u => mulUsqFun_norm_le f u)

/-- `M_{u²}` as a linear map. -/
def MLin : H →ₗ[ℂ] H where
  toFun := fun f => (mulUsqFun_memLp f).toLp (mulUsqFun f)
  map_add' := by
    intro f g
    apply Lp.ext
    refine (mulUsqFun_memLp (f + g)).coeFn_toLp.trans ?_
    refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_add _ _).symm
    refine Filter.EventuallyEq.trans ?_
      ((mulUsqFun_memLp f).coeFn_toLp.add (mulUsqFun_memLp g).coeFn_toLp).symm
    filter_upwards [Lp.coeFn_add f g] with u hu
    simp only [mulUsqFun, Pi.add_apply, hu]
    ring
  map_smul' := by
    intro a f
    apply Lp.ext
    refine (mulUsqFun_memLp (a • f)).coeFn_toLp.trans ?_
    refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_smul a _).symm
    refine Filter.EventuallyEq.trans ?_ ((mulUsqFun_memLp f).coeFn_toLp.const_smul a).symm
    filter_upwards [Lp.coeFn_smul a f] with u hu
    simp only [mulUsqFun, Pi.smul_apply, hu, smul_eq_mul, RingHom.id_apply]
    ring

theorem MLin_apply_ae (f : H) :
    (MLin f : ℝ → ℂ) =ᵐ[ν] fun u => ((u ^ 2 : ℝ) : ℂ) * f u := by
  refine (mulUsqFun_memLp f).coeFn_toLp.trans ?_
  filter_upwards [ae_mem_Icc] with u hu
  simp only [mulUsqFun, usq_eq hu]

theorem MLin_norm_le (f : H) : ‖MLin f‖ ≤ ‖f‖ := by
  change ‖(mulUsqFun_memLp f).toLp (mulUsqFun f)‖ ≤ ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
  exact eLpNorm_mono_ae (mulUsqFun_memLp f).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => mulUsqFun_norm_le f u)

/-- The bounded operator `M_{u²}`, `‖M‖ ≤ 1`. -/
def M : H →L[ℂ] H := MLin.mkContinuous 1 (fun f => by simpa using MLin_norm_le f)

theorem M_apply_ae (f : H) : (M f : ℝ → ℂ) =ᵐ[ν] fun u => ((u ^ 2 : ℝ) : ℂ) * f u :=
  MLin_apply_ae f

/-- `𝒜_c := D̄ - c² M_{u²}` on `Dom(D̄)` (Definition 5.1 of the manuscript). -/
abbrev AClosed (c : ℝ) : H →ₗ.[ℂ] H where
  domain := DClosed.domain
  toFun := DClosed.toFun - ((c : ℂ) ^ 2) • (M.toLinearMap.comp DClosed.domain.subtype)

theorem AClosed_domain (c : ℝ) : (AClosed c).domain = DClosed.domain := rfl

theorem AClosed_apply (c : ℝ) (x : DClosed.domain) :
    AClosed c x = DClosed x - ((c : ℂ) ^ 2) • M x := rfl

/-! ## The Gram operator `S_{1/2,c}` -/

/-- `S_{1/2,c}`: the certified bounded selfadjoint operator `gram (1/2) (1/(4c))` of the
GegenbauerFock library, whose kernel is `exp(u v/(4α)) = exp(c u v)`. -/
def S (c : ℝ) (hc : 0 < c) : H →L[ℂ] H :=
  GegenbauerFock.GeneralUltrasphericalFock.gram (1 / 2) (1 / (4 * c)) hhalf
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
        hhalf (by positivity) f :=
    GegenbauerFock.GeneralUltrasphericalFock.gram_eq_integralLp _ _ _ _ f
  rw [h1]
  unfold GegenbauerFock.GeneralUltrasphericalFock.gramKernelIntegralLp
  have h2 := (GegenbauerFock.GeneralUltrasphericalFock.gramKernelIntegral_memLp (1 / 2)
    (1 / (4 * c)) hhalf (by positivity) f).coeFn_toLp
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
        (GegenbauerFock.GeneralUltrasphericalFock.C (1 / 2) (1 / (4 * c)) hhalf hα f)) :=
    GegenbauerFock.FockEvaluation.differentiable_evaluation_complex (1 / (4 * c)) hα _
  have hfun : SFun c (f : ℝ → ℂ) = fun u : ℝ =>
      GegenbauerFock.FockEvaluation.evaluation (1 / (4 * c)) hα
        (-Complex.I * (u : ℂ) / (2 * ((1 / (4 * c) : ℝ) : ℂ)))
        (GegenbauerFock.GeneralUltrasphericalFock.C (1 / 2) (1 / (4 * c)) hhalf hα f) := by
    funext u
    rw [SFun_eq_gramKernelIntegral c hc f u,
      ← GegenbauerFock.GeneralUltrasphericalFock.evaluation_imaginary_eq_gramKernelIntegral
        (1 / 2) (1 / (4 * c)) hhalf hα f u]
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

/-! ## Symmetry of `D⁰`, density of the polynomials and closability -/

/-- Complex conjugation of a polynomial. -/
def pconj (p : ℂ[X]) : ℂ[X] := p.map (starRingEnd ℂ)

theorem polyFun_pconj (p : ℂ[X]) (v : ℝ) :
    polyFun (pconj p) v = (starRingEnd ℂ) (polyFun p v) := by
  have h := Polynomial.eval₂_at_apply (p := p) (starRingEnd ℂ) (v : ℂ)
  rw [Complex.conj_ofReal] at h
  unfold polyFun pconj
  rw [Polynomial.eval_map]
  exact h

theorem DPoly_pconj (p : ℂ[X]) : DPoly (pconj p) = pconj (DPoly p) := by
  rw [DPoly_apply, DPoly_apply]
  unfold pconj
  simp only [Polynomial.derivative_map, Polynomial.map_neg, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_ofNat, map_ofNat]

theorem polyFun_DPoly (p : ℂ[X]) (v : ℝ) : polyFun (DPoly p) v = DExpr (polyFun p) v := by
  rw [DPoly_eq_neg_derivative]
  unfold DExpr
  rw [oneSubSq_mul_deriv_polyFun, polyFun_deriv]
  simp [polyFun, eval_neg]

/-- The `L²(ν)` inner product of two continuous functions. -/
theorem inner_cLp (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    ⟪cLp f hf, cLp g hg⟫_ℂ = ∫ v, (starRingEnd ℂ) (f v) * g v ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cLp_ae_eq f hf, cLp_ae_eq g hg] with v hfv hgv
  rw [hfv, hgv, RCLike.inner_apply']

theorem DExpr_continuous (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) : Continuous (DExpr g) := by
  have hg2 : ContDiff ℝ (1 + 1) g := by norm_num; exact hg
  have h : ContDiff ℝ 1 (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) * deriv g t) :=
    contDiff_oneSubSq.mul hg2.deriv'
  exact (h.continuous_deriv le_rfl).neg

/-- Green's identity in the `L²(ν)` inner product: `⟪D⁰ p, g⟫ = ⟪p, D g⟫` for `g ∈ C²`. -/
theorem inner_DPoly_cLp (p : ℂ[X]) (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) :
    ⟪polyLp (DPoly p), cLp g hg.continuous⟫_ℂ
      = ⟪polyLp p, cLp (DExpr g) (DExpr_continuous g hg)⟫_ℂ := by
  unfold polyLp
  rw [inner_cLp, inner_cLp, integral_nu, integral_nu]
  congr 1
  have hG := green_identity (polyFun (pconj p)) g (polyFun_contDiff _ 2) hg
  rw [oneSubSq_mul_deriv_polyFun, polyFun_deriv] at hG
  have e1 : ∀ v : ℝ, (starRingEnd ℂ) (polyFun (DPoly p) v)
      = -(polyFun (derivative ((1 - X ^ 2) * derivative (pconj p))) v) := by
    intro v
    rw [← polyFun_pconj, ← DPoly_pconj, DPoly_eq_neg_derivative]
    simp [polyFun, eval_neg]
  have e2 : ∀ v : ℝ, (starRingEnd ℂ) (polyFun p v) = polyFun (pconj p) v :=
    fun v => (polyFun_pconj p v).symm
  simp_rw [e1, e2]
  unfold DExpr
  simp only [neg_mul, mul_neg, intervalIntegral.integral_neg]
  rw [hG]

/-- `D⁰` is symmetric on the polynomials. -/
theorem DPMap_formalSymmetric : DPMap.IsFormalAdjoint DPMap := by
  intro x y
  obtain ⟨p, hp⟩ := LinearMap.mem_range.mp x.2
  obtain ⟨q, hq⟩ := LinearMap.mem_range.mp y.2
  have hx : x = ⟨polyLp p, polyLp_mem p⟩ := Subtype.ext hp.symm
  have hy : y = ⟨polyLp q, polyLp_mem q⟩ := Subtype.ext hq.symm
  subst hx
  subst hy
  rw [DPMap_apply, DPMap_apply]
  show ⟪polyLp (DPoly p), polyLp q⟫_ℂ = ⟪polyLp p, polyLp (DPoly q)⟫_ℂ
  have h := inner_DPoly_cLp p (polyFun q) (polyFun_contDiff q 2)
  have h2 : cLp (DExpr (polyFun q)) (DExpr_continuous _ (polyFun_contDiff q 2))
      = polyLp (DPoly q) := by
    apply Lp.ext
    refine (cLp_ae_eq _ _).trans ?_
    refine Filter.EventuallyEq.trans ?_ (polyLp_ae_eq (DPoly q)).symm
    filter_upwards with v
    exact (polyFun_DPoly q v).symm
  rw [← h2]
  exact h

/-- Complex Weierstrass on `[-1,1]`: every bounded continuous `f : ℝ → ℂ` is uniformly
approximated by complex polynomials (real and imaginary parts separately). -/
theorem exists_poly_near (f : BoundedContinuousFunction ℝ ℂ) (eps : ℝ) (heps : 0 < eps) :
    ∃ P : ℂ[X], ∀ u ∈ Set.Icc (-1 : ℝ) 1, ‖f u - polyFun P u‖ < eps := by
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn (-1 : ℝ) 1 (fun u => (f u).re)
    ((Complex.continuous_re.comp f.continuous).continuousOn) (eps / 2) (half_pos heps)
  obtain ⟨Q, hQ⟩ := exists_polynomial_near_of_continuousOn (-1 : ℝ) 1 (fun u => (f u).im)
    ((Complex.continuous_im.comp f.continuous).continuousOn) (eps / 2) (half_pos heps)
  refine ⟨P.map Complex.ofRealHom + C Complex.I * Q.map Complex.ofRealHom, ?_⟩
  intro u hu
  have hPu : (P.map Complex.ofRealHom).eval (u : ℂ) = ((P.eval u : ℝ) : ℂ) := by
    rw [Polynomial.eval_map, ← Complex.ofRealHom_eq_coe]
    exact Polynomial.eval₂_at_apply (p := P) Complex.ofRealHom u
  have hQu : (Q.map Complex.ofRealHom).eval (u : ℂ) = ((Q.eval u : ℝ) : ℂ) := by
    rw [Polynomial.eval_map, ← Complex.ofRealHom_eq_coe]
    exact Polynomial.eval₂_at_apply (p := Q) Complex.ofRealHom u
  have hre : (f u - polyFun (P.map Complex.ofRealHom + C Complex.I * Q.map Complex.ofRealHom) u).re
      = (f u).re - P.eval u := by
    simp [polyFun, hPu, hQu]
  have him : (f u - polyFun (P.map Complex.ofRealHom + C Complex.I * Q.map Complex.ofRealHom) u).im
      = (f u).im - Q.eval u := by
    simp [polyFun, hPu, hQu]
  calc ‖f u - polyFun (P.map Complex.ofRealHom + C Complex.I * Q.map Complex.ofRealHom) u‖
      ≤ |(f u - polyFun (P.map Complex.ofRealHom + C Complex.I * Q.map Complex.ofRealHom) u).re|
        + |(f u - polyFun (P.map Complex.ofRealHom + C Complex.I * Q.map Complex.ofRealHom) u).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ < eps / 2 + eps / 2 := by
        rw [hre, him]
        apply add_lt_add
        · rw [abs_sub_comm]; exact hP u hu
        · rw [abs_sub_comm]; exact hQ u hu
    _ = eps := by ring

/-- The polynomials are dense in `H` (Weierstrass and the certified density of the bounded
continuous functions, `boundedContinuous_toLp_denseRange`). -/
theorem polyCore_dense : Dense (polyCore : Set H) := by
  have hRange : Set.range (GegenbauerFock.Ultraspherical.boundedContinuousToLp (1 / 2) hhalf)
      ⊆ closure (polyCore : Set H) := by
    rintro y ⟨f, rfl⟩
    rw [Metric.mem_closure_iff]
    intro eps heps
    obtain ⟨P, hP⟩ := exists_poly_near f (eps / 2) (half_pos heps)
    refine ⟨polyLp P, polyLp_mem P, ?_⟩
    rw [dist_eq_norm]
    have hf : ((GegenbauerFock.Ultraspherical.boundedContinuousToLp (1 / 2) hhalf f : H)
        : ℝ → ℂ) =ᵐ[ν] f := by
      change ((BoundedContinuousFunction.toLp (2 : ℝ≥0∞) ν ℂ f : H) : ℝ → ℂ) =ᵐ[ν] f
      exact BoundedContinuousFunction.coeFn_toLp (2 : ℝ≥0∞) ν ℂ f
    have hdiff : ((GegenbauerFock.Ultraspherical.boundedContinuousToLp (1 / 2) hhalf f
        - polyLp P : H) : ℝ → ℂ) =ᵐ[ν] fun u => f u - polyFun P u := by
      filter_upwards [Lp.coeFn_sub
        (GegenbauerFock.Ultraspherical.boundedContinuousToLp (1 / 2) hhalf f) (polyLp P),
        hf, polyLp_ae_eq P] with u hsub hfu hpu
      rw [hsub, Pi.sub_apply, hfu, hpu]
    rw [Lp.norm_def, eLpNorm_congr_ae hdiff]
    have hb := GegenbauerFock.Ultraspherical.eLpNorm_sub_le_of_uniform_error_unit_interval
      (1 / 2) hhalf f (polyFun P) f.continuous (polyFun_continuous P) (eps / 2)
      (fun u hu => (hP u hu).le)
    calc (eLpNorm (fun u => f u - polyFun P u) 2 ν).toReal
        ≤ (ENNReal.ofReal (eps / 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      _ = eps / 2 := ENNReal.toReal_ofReal (half_pos heps).le
      _ < eps := half_lt_self heps
  have hD := GegenbauerFock.Ultraspherical.boundedContinuous_toLp_denseRange (1 / 2) hhalf
  intro x
  have hx : x ∈ closure (Set.range
      (GegenbauerFock.Ultraspherical.boundedContinuousToLp (1 / 2) hhalf)) := by
    rw [hD.closure_range]
    trivial
  exact closure_minimal hRange isClosed_closure hx

theorem DPMap_domain_dense : Dense (DPMap.domain : Set H) := polyCore_dense

/-- `D⁰` is closable: densely defined and symmetric, hence contained in its closed adjoint
(the complex counterpart of `GegenbauerFock.Ultraspherical.sturmRealPMap_isClosable`). -/
theorem DPMap_isClosable : DPMap.IsClosable := by
  have hdense := DPMap_domain_dense
  have hle : DPMap ≤ DPMap.adjoint := DPMap_formalSymmetric.le_adjoint hdense
  have hclosed : DPMap.adjoint.IsClosed := LinearPMap.adjoint_isClosed hdense
  exact hclosed.isClosable.leIsClosable hle

theorem DClosed_isClosed : DClosed.IsClosed := DPMap_isClosable.closure_isClosed

/-! ## Lemma 4: the domain of `D̄` contains the `C²` functions -/

/-- **Abstract closure criterion.**  Let `A` be a closable, symmetric, densely defined operator
on a Hilbert space with `‖p‖ ≤ ‖A p + p‖` on its domain and `Ran(A + I)` dense.  Then every
`g` satisfying the adjoint relation `⟪A p, g⟫ = ⟪p, h⟫` for all `p` in the domain lies in the
domain of the closure, and the closure sends `g` to `h`.  (This is the inclusion
`Dom(A*) ⊆ Dom(Ā)`, i.e. essential selfadjointness, in the form needed here.) -/
theorem mem_closure_domain_of_adjoint_relation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →ₗ.[ℂ] E) (hA : A.IsClosable) (hsymm : A.IsFormalAdjoint A)
    (hcoerc : ∀ p : A.domain, ‖(p : E)‖ ≤ ‖A p + (p : E)‖)
    (hdense : Dense (Set.range (fun p : A.domain => A p + (p : E))))
    (g h : E) (hrel : ∀ p : A.domain, ⟪A p, g⟫_ℂ = ⟪(p : E), h⟫_ℂ) :
    ∃ hmem : g ∈ A.closure.domain, A.closure ⟨g, hmem⟩ = h := by
  obtain ⟨q, hqmem, hqlim⟩ := mem_closure_iff_seq_limit.mp (hdense (h + g))
  simp only [Set.mem_range] at hqmem
  choose p hp using hqmem
  have hT : Filter.Tendsto (fun n => A (p n) + (p n : E)) Filter.atTop (nhds (h + g)) := by
    have hfun : (fun n => A (p n) + (p n : E)) = q := funext hp
    rw [hfun]
    exact hqlim
  have hcauchy : CauchySeq (fun n => (p n : E)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hT.cauchySeq ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have hc := hcoerc (p m - p n)
    rw [LinearPMap.map_sub, Submodule.coe_sub] at hc
    rw [dist_eq_norm]
    calc ‖(p m : E) - (p n : E)‖
        ≤ ‖(A (p m) - A (p n)) + ((p m : E) - (p n : E))‖ := hc
      _ = ‖(A (p m) + (p m : E)) - (A (p n) + (p n : E))‖ := by congr 1; abel
      _ < ε := by rw [← dist_eq_norm]; exact hN m hm n hn
  obtain ⟨g', hg'⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hAp : Filter.Tendsto (fun n => A (p n)) Filter.atTop (nhds ((h + g) - g')) := by
    have h1 := hT.sub hg'
    simpa only [add_sub_cancel_right] using h1
  have hgraph : (g', (h + g) - g') ∈ A.closure.graph := by
    rw [← hA.graph_closure_eq_closure_graph]
    show (g', (h + g) - g') ∈ closure (A.graph : Set (E × E))
    refine mem_closure_of_tendsto (hg'.prodMk_nhds hAp) ?_
    filter_upwards with n
    exact LinearPMap.mem_graph A (p n)
  have hgg : g' = g := by
    rw [← sub_eq_zero]
    apply Dense.eq_zero_of_inner_right (𝕜 := ℂ) hdense
    rintro _ ⟨r, rfl⟩
    have h1 : Filter.Tendsto (fun n => ⟪A r + (r : E), (p n : E)⟫_ℂ) Filter.atTop
        (nhds ⟪A r + (r : E), g'⟫_ℂ) := tendsto_const_nhds.inner hg'
    have h2 : Filter.Tendsto (fun n => ⟪A r + (r : E), (p n : E)⟫_ℂ) Filter.atTop
        (nhds ⟪(r : E), h + g⟫_ℂ) := by
      have h3 : (fun n => ⟪A r + (r : E), (p n : E)⟫_ℂ)
          = fun n => ⟪(r : E), A (p n) + (p n : E)⟫_ℂ := by
        funext n
        rw [inner_add_left (𝕜 := ℂ), inner_add_right (𝕜 := ℂ), hsymm r (p n)]
      rw [h3]
      exact tendsto_const_nhds.inner hT
    have h4 : ⟪A r + (r : E), g'⟫_ℂ = ⟪(r : E), h + g⟫_ℂ := tendsto_nhds_unique h1 h2
    rw [inner_sub_right (𝕜 := ℂ), h4, inner_add_left (𝕜 := ℂ), hrel r,
      inner_add_right (𝕜 := ℂ), sub_self]
  obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff A.closure).mp hgraph
  dsimp only at hz1 hz2
  rw [hgg] at hz1 hz2
  have hmem : g ∈ A.closure.domain := by
    rw [← hz1]
    exact z.2
  refine ⟨hmem, ?_⟩
  have hz : (⟨g, hmem⟩ : A.closure.domain) = z := Subtype.ext hz1.symm
  rw [hz, hz2]
  abel

/-- `⟪D⁰ p, p⟫ = ½ ∫_{-1}^{1} (1-v²) |p'(v)|² dv ≥ 0`. -/
theorem DPMap_inner_self_nonneg (x : DPMap.domain) :
    0 ≤ RCLike.re ⟪DPMap x, (x : H)⟫_ℂ := by
  obtain ⟨p, hp⟩ := LinearMap.mem_range.mp x.2
  have hx : x = ⟨polyLp p, polyLp_mem p⟩ := Subtype.ext hp.symm
  subst hx
  rw [DPMap_apply]
  show 0 ≤ RCLike.re ⟪polyLp (DPoly p), polyLp p⟫_ℂ
  unfold polyLp
  rw [inner_cLp, integral_nu]
  have hG := ibp_once (polyFun (pconj p)) (polyFun p) (polyFun_contDiff _ 2) (polyFun_contDiff _ 2)
  rw [oneSubSq_mul_deriv_polyFun, polyFun_deriv] at hG
  have e1 : ∀ v : ℝ, (starRingEnd ℂ) (polyFun (DPoly p) v)
      = -(polyFun (derivative ((1 - X ^ 2) * derivative (pconj p))) v) := by
    intro v
    rw [← polyFun_pconj, ← DPoly_pconj, DPoly_eq_neg_derivative]
    simp [polyFun, eval_neg]
  simp_rw [e1]
  simp only [neg_mul, intervalIntegral.integral_neg]
  rw [hG, neg_neg]
  have e3 : ∀ v : ℝ, ((1 - v ^ 2 : ℝ) : ℂ) * deriv (polyFun (pconj p)) v * deriv (polyFun p) v
      = (((1 - v ^ 2) * ‖deriv (polyFun p) v‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    have hconj : deriv (polyFun (pconj p)) v = (starRingEnd ℂ) (deriv (polyFun p) v) := by
      rw [polyFun_deriv, polyFun_deriv, ← polyFun_pconj]
      unfold pconj
      rw [Polynomial.derivative_map]
    rw [hconj, mul_assoc, Complex.conj_mul']
    push_cast
    ring
  simp_rw [e3]
  rw [intervalIntegral.integral_ofReal]
  have hnn : 0 ≤ ∫ v in (-1 : ℝ)..1, (1 - v ^ 2) * ‖deriv (polyFun p) v‖ ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro v hv
    have h1 : 0 ≤ 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
    positivity
  have hcast : (1 / 2 : ℂ) * ((∫ v in (-1 : ℝ)..1, (1 - v ^ 2) * ‖deriv (polyFun p) v‖ ^ 2 : ℝ) : ℂ)
      = (((1 / 2) * ∫ v in (-1 : ℝ)..1, (1 - v ^ 2) * ‖deriv (polyFun p) v‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, RCLike.re_to_complex, Complex.ofReal_re]
  exact mul_nonneg (by norm_num) hnn

/-- Coercivity of `D⁰ + I`: `‖p‖ ≤ ‖D⁰ p + p‖`. -/
theorem DPMap_coercive (x : DPMap.domain) : ‖(x : H)‖ ≤ ‖DPMap x + (x : H)‖ := by
  have h := DPMap_inner_self_nonneg x
  have hsq : ‖(x : H)‖ ^ 2 ≤ ‖DPMap x + (x : H)‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ)]
    nlinarith [sq_nonneg ‖DPMap x‖]
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq

/-- `D⁰` does not raise the degree. -/
theorem natDegree_DPoly_le (p : ℂ[X]) : (DPoly p).natDegree ≤ p.natDegree := by
  rw [DPoly_apply, natDegree_neg]
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · by_cases h2 : p.natDegree ≤ 1
    · have h0 : (derivative p).natDegree = 0 := by
        have := natDegree_derivative_le p
        omega
      rw [derivative_of_natDegree_zero h0, mul_zero, natDegree_zero]
      exact Nat.zero_le _
    · push_neg at h2
      have hd1 := natDegree_derivative_le p
      have hd2 := natDegree_derivative_le (derivative p)
      have h12 : (1 - X ^ 2 : ℂ[X]).natDegree ≤ 2 := by
        refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · simp
        · simp
      calc ((1 - X ^ 2) * derivative (derivative p)).natDegree
          ≤ (1 - X ^ 2 : ℂ[X]).natDegree + (derivative (derivative p)).natDegree :=
            natDegree_mul_le
        _ ≤ 2 + (p.natDegree - 1 - 1) :=
            Nat.add_le_add h12 (hd2.trans (Nat.sub_le_sub_right hd1 1))
        _ ≤ p.natDegree := by omega
  · by_cases h0 : p.natDegree = 0
    · rw [derivative_of_natDegree_zero h0, mul_zero, natDegree_zero]
      exact Nat.zero_le _
    · have hd1 := natDegree_derivative_le p
      calc (C (2 : ℂ) * X * derivative p).natDegree
          ≤ (C (2 : ℂ) * X : ℂ[X]).natDegree + (derivative p).natDegree := natDegree_mul_le
        _ ≤ 1 + (p.natDegree - 1) :=
            Nat.add_le_add ((natDegree_C_mul_le _ _).trans natDegree_X_le) hd1
        _ ≤ p.natDegree := by omega

/-- `T = D⁰ + I` on polynomials. -/
def TPoly : ℂ[X] →ₗ[ℂ] ℂ[X] := DPoly + LinearMap.id

theorem TPoly_apply (p : ℂ[X]) : TPoly p = DPoly p + p := rfl

theorem TPoly_mem_degreeLT {N : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ N) :
    TPoly p ∈ degreeLT ℂ N := by
  rw [mem_degreeLT] at hp ⊢
  rw [TPoly_apply]
  by_cases hp0 : p = 0
  · subst hp0
    simpa using hp
  have hD : (DPoly p).degree ≤ p.degree := by
    calc (DPoly p).degree ≤ ((DPoly p).natDegree : WithBot ℕ) := degree_le_natDegree
      _ ≤ (p.natDegree : WithBot ℕ) := by exact_mod_cast natDegree_DPoly_le p
      _ = p.degree := (degree_eq_natDegree hp0).symm
  calc (DPoly p + p).degree ≤ max (DPoly p).degree p.degree := degree_add_le _ _
    _ ≤ p.degree := max_le hD le_rfl
    _ < N := hp

/-- `T` is injective on polynomials, by coercivity in `L²(ν)`. -/
theorem TPoly_injective : Function.Injective TPoly := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  change DPoly p + p = 0 at hp
  have hx := DPMap_coercive ⟨polyLp p, polyLp_mem p⟩
  rw [DPMap_apply] at hx
  change ‖polyLp p‖ ≤ ‖polyLp (DPoly p) + polyLp p‖ at hx
  have h0 : polyLp (DPoly p) + polyLp p = 0 := by
    rw [← polyLp_add, hp]
    exact polyLinear.map_zero
  rw [h0, norm_zero] at hx
  have h1 : polyLp p = 0 := norm_le_zero_iff.mp hx
  exact polyLinear_injective (h1.trans polyLinear.map_zero.symm)

/-- `T` restricted to the polynomials of degree `≤ N`. -/
def TN (N : ℕ) : degreeLT ℂ (N + 1) →ₗ[ℂ] degreeLT ℂ (N + 1) :=
  TPoly.restrict (fun _ hp => TPoly_mem_degreeLT hp)

/-- `T` is surjective on polynomials: on each finite-dimensional space `degreeLT (N+1)` it is
an injective endomorphism. -/
theorem TPoly_surjective : Function.Surjective TPoly := by
  intro q
  have hq : q ∈ degreeLT ℂ (q.natDegree + 1) := by
    rw [mem_degreeLT]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_self q.natDegree)
  haveI : FiniteDimensional ℂ (degreeLT ℂ (q.natDegree + 1)) :=
    (degreeLTEquiv ℂ (q.natDegree + 1)).symm.finiteDimensional
  have hinj : Function.Injective (TN q.natDegree) := by
    intro x y hxy
    apply Subtype.ext
    apply TPoly_injective
    have h := congrArg Subtype.val hxy
    simpa [TN, LinearMap.restrict_apply] using h
  obtain ⟨x, hx⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨q, hq⟩
  refine ⟨x.1, ?_⟩
  have h := congrArg Subtype.val hx
  simpa [TN, LinearMap.restrict_apply] using h

/-- `Ran(D⁰ + I)` contains the polynomials, hence is dense in `H`. -/
theorem range_T_dense : Dense (Set.range (fun p : DPMap.domain => DPMap p + (p : H))) := by
  apply Dense.mono _ polyCore_dense
  intro y hy
  obtain ⟨q, hq⟩ := LinearMap.mem_range.mp hy
  obtain ⟨p, hp⟩ := TPoly_surjective q
  refine ⟨⟨polyLp p, polyLp_mem p⟩, ?_⟩
  show DPMap ⟨polyLp p, polyLp_mem p⟩ + polyLp p = y
  rw [DPMap_apply, ← polyLp_add, ← hq]
  show polyLp (DPoly p + p) = polyLinear q
  rw [← hp]
  rfl

/-- **Lemma 4 (domain inclusion).**  Every `C²` function `g` defines an element of the domain
of the closed operator `D̄`, on which `D̄` acts as the differential expression `DExpr g`
(almost everywhere): the adjoint relation `⟪D⁰ p, g⟫ = ⟪p, D g⟫` (Green, `inner_DPoly_cLp`)
and the abstract criterion `mem_closure_domain_of_adjoint_relation`. -/
theorem smooth_mem_closure_domain (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) :
    ∃ hmem : cLp g hg.continuous ∈ DClosed.domain,
      ((DClosed ⟨cLp g hg.continuous, hmem⟩ : H) : ℝ → ℂ) =ᵐ[ν] DExpr g := by
  have hrel : ∀ x : DPMap.domain, ⟪DPMap x, cLp g hg.continuous⟫_ℂ
      = ⟪(x : H), cLp (DExpr g) (DExpr_continuous g hg)⟫_ℂ := by
    intro x
    obtain ⟨p, hp⟩ := LinearMap.mem_range.mp x.2
    have hx : x = ⟨polyLp p, polyLp_mem p⟩ := Subtype.ext hp.symm
    subst hx
    rw [DPMap_apply]
    exact inner_DPoly_cLp p g hg
  obtain ⟨hmem, hval⟩ := mem_closure_domain_of_adjoint_relation DPMap DPMap_isClosable
    DPMap_formalSymmetric DPMap_coercive range_T_dense _ _ hrel
  refine ⟨hmem, ?_⟩
  show ((DPMap.closure ⟨cLp g hg.continuous, hmem⟩ : H) : ℝ → ℂ) =ᵐ[ν] DExpr g
  rw [hval]
  exact cLp_ae_eq _ _

/-! ## Theorem 5.2 -/

/-- `S f` is the `L²` class of its (smooth) kernel form. -/
theorem S_eq_cLp (c : ℝ) (hc : 0 < c) (f : H) :
    S c hc f = cLp (SFun c (f : ℝ → ℂ)) (SFun_contDiff c hc f 2).continuous := by
  apply Lp.ext
  exact (S_apply_ae c hc f).trans (cLp_ae_eq _ _).symm

/-- **Theorem 5.2 (domain-level commutation), first half:** `S_{1/2,c} H ⊂ Dom(𝒜_c)`.
From `SFun_contDiff`, Lemma 4 and the kernel identity `S_apply_ae`. -/
theorem S_range_subset_domain (c : ℝ) (hc : 0 < c) (f : H) :
    S c hc f ∈ (AClosed c).domain := by
  rw [AClosed_domain, S_eq_cLp]
  obtain ⟨hmem, _⟩ := smooth_mem_closure_domain (SFun c (f : ℝ → ℂ)) (SFun_contDiff c hc f 2)
  exact hmem

/-- `D̄` agrees with `D⁰` on polynomials. -/
theorem DClosed_polyLp (q : ℂ[X]) (hq : polyLp q ∈ DClosed.domain) :
    DClosed ⟨polyLp q, hq⟩ = polyLp (DPoly q) := by
  rw [← DPMap_apply q (polyLp_mem q)]
  exact (DPMap_le_DClosed.2 (x := ⟨polyLp q, polyLp_mem q⟩)
    (y := ⟨polyLp q, hq⟩) rfl).symm

/-- `M_{u²}` on polynomials. -/
theorem M_polyLp (q : ℂ[X]) : M (polyLp q) = polyLp (X ^ 2 * q) := by
  apply Lp.ext
  refine (M_apply_ae (polyLp q)).trans ?_
  refine Filter.EventuallyEq.trans ?_ (polyLp_ae_eq (X ^ 2 * q)).symm
  filter_upwards [polyLp_ae_eq q] with u hu
  rw [hu]
  simp only [polyFun, eval_mul, eval_pow, eval_X]
  push_cast
  ring

theorem polyLp_APoly (c : ℝ) (q : ℂ[X]) :
    polyLp (APoly c q) = polyLp (DPoly q) - ((c : ℂ) ^ 2) • polyLp (X ^ 2 * q) := by
  rw [APoly_eq, ← polyLp_smul, smul_eq_C_mul, ← mul_assoc]
  exact polyLinear.map_sub _ _

/-- `𝒜_c` on polynomials is `APoly c`. -/
theorem AClosed_polyLp (c : ℝ) (q : ℂ[X]) (hq : polyLp q ∈ DClosed.domain) :
    AClosed c ⟨polyLp q, hq⟩ = polyLp (APoly c q) := by
  rw [AClosed_apply, DClosed_polyLp, M_polyLp, polyLp_APoly]

open Classical in
/-- The total function realising `𝒜_c` (zero outside the domain), for the abstract transport
theorem. -/
def Afun (c : ℝ) : H → H :=
  fun x => if h : x ∈ DClosed.domain then AClosed c ⟨x, h⟩ else 0

theorem Afun_apply (c : ℝ) (x : H) (h : x ∈ DClosed.domain) :
    Afun c x = AClosed c ⟨x, h⟩ := by
  simp [Afun, h]

/-- The core commutation on `H`: `𝒜_c (S p) = S (𝒜_c p)` for polynomials, from Lemmas 3, 4
and the kernel identities. -/
theorem AClosed_S_polyLp (c : ℝ) (hc : 0 < c) (q : ℂ[X]) (hq : polyLp q ∈ DClosed.domain) :
    AClosed c ⟨S c hc (polyLp q), S_range_subset_domain c hc (polyLp q)⟩
      = S c hc (AClosed c ⟨polyLp q, hq⟩) := by
  rw [AClosed_polyLp]
  have hs : ContDiff ℝ 2 (SFun c (polyLp q : ℝ → ℂ)) := SFun_contDiff c hc (polyLp q) 2
  obtain ⟨hmem, hval⟩ := smooth_mem_closure_domain (SFun c (polyLp q : ℝ → ℂ)) hs
  have hsub : (⟨S c hc (polyLp q), S_range_subset_domain c hc (polyLp q)⟩ : DClosed.domain)
      = ⟨cLp (SFun c (polyLp q : ℝ → ℂ)) hs.continuous, hmem⟩ :=
    Subtype.ext (S_eq_cLp c hc (polyLp q))
  rw [AClosed_apply, hsub]
  apply Lp.ext
  have hM : ((M (cLp (SFun c (polyLp q : ℝ → ℂ)) hs.continuous) : H) : ℝ → ℂ)
      =ᵐ[ν] fun u => ((u ^ 2 : ℝ) : ℂ) * SFun c (polyFun q) u := by
    refine (M_apply_ae _).trans ?_
    filter_upwards [cLp_ae_eq (SFun c (polyLp q : ℝ → ℂ)) hs.continuous] with u hu
    rw [hu, SFun_polyLp]
  have hR : ((S c hc (polyLp (APoly c q)) : H) : ℝ → ℂ) =ᵐ[ν] SFun c (polyFun (APoly c q)) := by
    have h0 := S_apply_ae c hc (polyLp (APoly c q))
    rw [SFun_polyLp] at h0
    exact h0
  filter_upwards [Lp.coeFn_sub (DClosed ⟨cLp (SFun c (polyLp q : ℝ → ℂ)) hs.continuous, hmem⟩)
      (((c : ℂ) ^ 2) • M (cLp (SFun c (polyLp q : ℝ → ℂ)) hs.continuous)),
    Lp.coeFn_smul ((c : ℂ) ^ 2) (M (cLp (SFun c (polyLp q : ℝ → ℂ)) hs.continuous)),
    hval, hM, hR, ae_mem_Icc]
    with u hsub' hsmul hD hMu hRu hu
  rw [hsub', Pi.sub_apply, hsmul, Pi.smul_apply, hD, hMu, hRu, SFun_polyLp,
    ← core_commutation c hc q u hu, AExpr_eq, smul_eq_mul]
  push_cast
  ring

/-- `hcore` for the transport theorem: every `f ∈ Dom(D̄)` is the limit of polynomials `p n`
with `𝒜_c p n → 𝒜_c f` (graph closure, plus continuity of `M`). -/
theorem Afun_core (c : ℝ) (f : H) (hf : f ∈ DClosed.domain) :
    ∃ p : ℕ → H, (∀ n, p n ∈ (polyCore : Set H)) ∧
      Filter.Tendsto p Filter.atTop (nhds f) ∧
      Filter.Tendsto (fun n => Afun c (p n)) Filter.atTop (nhds (Afun c f)) := by
  have hgraph : (f, DClosed ⟨f, hf⟩) ∈ closure (DPMap.graph : Set (H × H)) := by
    have h : ((((⟨f, hf⟩ : DPMap.closure.domain) : H)), DPMap.closure ⟨f, hf⟩)
        ∈ DPMap.closure.graph :=
      LinearPMap.mem_graph DPMap.closure ⟨f, hf⟩
    rw [← DPMap_isClosable.graph_closure_eq_closure_graph] at h
    exact h
  obtain ⟨z, hz, hzlim⟩ := mem_closure_iff_seq_limit.mp hgraph
  have hz' : ∀ n, ∃ y : DPMap.domain, (y : H) = (z n).1 ∧ DPMap y = (z n).2 :=
    fun n => (LinearPMap.mem_graph_iff DPMap).mp (hz n)
  choose y hy1 hy2 using hz'
  refine ⟨fun n => (z n).1, fun n => ?_, ?_, ?_⟩
  · show (z n).1 ∈ polyCore
    rw [← hy1 n]
    exact (y n).2
  · exact (continuous_fst.tendsto _).comp hzlim
  · have hmem : ∀ n, (z n).1 ∈ DClosed.domain := fun n => by
      rw [← hy1 n]
      exact DPMap_le_DClosed.1 (y n).2
    have hA : ∀ n, Afun c ((z n).1) = (z n).2 - ((c : ℂ) ^ 2) • M ((z n).1) := by
      intro n
      rw [Afun_apply c _ (hmem n), AClosed_apply]
      congr 1
      rw [← hy2 n]
      exact (DPMap_le_DClosed.2 (x := y n) (y := ⟨(z n).1, hmem n⟩) (hy1 n)).symm
    rw [Afun_apply c f hf, AClosed_apply]
    simp_rw [hA]
    refine Filter.Tendsto.sub ((continuous_snd.tendsto _).comp hzlim) ?_
    exact Filter.Tendsto.const_smul
      ((M.continuous.tendsto f).comp ((continuous_fst.tendsto _).comp hzlim)) _

/-- `hclosed` for the transport theorem: `𝒜_c` is closed (graph closure of `D⁰` plus the
bounded perturbation). -/
theorem Afun_closed (c : ℝ) (x y : H)
    (h : ∃ p : ℕ → H, (∀ n, p n ∈ DClosed.domain) ∧
      Filter.Tendsto p Filter.atTop (nhds x) ∧
      Filter.Tendsto (fun n => Afun c (p n)) Filter.atTop (nhds y)) :
    x ∈ DClosed.domain ∧ Afun c x = y := by
  obtain ⟨p, hp, hpx, hpy⟩ := h
  have hD : ∀ n, DClosed ⟨p n, hp n⟩ = Afun c (p n) + ((c : ℂ) ^ 2) • M (p n) := by
    intro n
    rw [Afun_apply c _ (hp n), AClosed_apply]
    abel
  have hlim : Filter.Tendsto (fun n => DClosed ⟨p n, hp n⟩) Filter.atTop
      (nhds (y + ((c : ℂ) ^ 2) • M x)) := by
    simp_rw [hD]
    exact hpy.add (Filter.Tendsto.const_smul ((M.continuous.tendsto x).comp hpx) _)
  have hcl : IsClosed (DClosed.graph : Set (H × H)) := DClosed_isClosed
  have hgraph : (x, y + ((c : ℂ) ^ 2) • M x) ∈ (DClosed.graph : Set (H × H)) := by
    refine hcl.mem_of_tendsto (hpx.prodMk_nhds hlim) ?_
    filter_upwards with n
    exact LinearPMap.mem_graph DClosed ⟨p n, hp n⟩
  obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff DClosed).mp hgraph
  dsimp only at hz1 hz2
  have hx : x ∈ DClosed.domain := by
    rw [← hz1]
    exact z.2
  refine ⟨hx, ?_⟩
  rw [Afun_apply c x hx, AClosed_apply]
  have hzx : (⟨x, hx⟩ : DClosed.domain) = z := Subtype.ext hz1.symm
  rw [hzx, hz2, hz1]
  abel

/-- **Theorem 5.2 (domain-level commutation), second half:** for every `f ∈ Dom(𝒜_c)`,
`𝒜_c S_{1/2,c} f = S_{1/2,c} 𝒜_c f`.  Assembled from Lemmas 3 and 4 through the abstract
transport theorem `Manuscript14Gram.closed_graph_core_commutation`, with `D = Dom(D̄)`,
`Core = 𝒫`, `hcore = Afun_core`, `hclosed = Afun_closed`, `hcomm = AClosed_S_polyLp`. -/
theorem gram_commutes_with_perturbed_legendre (c : ℝ) (hc : 0 < c)
    (f : (AClosed c).domain) :
    (AClosed c) ⟨S c hc f, S_range_subset_domain c hc f⟩ = S c hc ((AClosed c) f) := by
  have hmain := Manuscript14Gram.closed_graph_core_commutation
    (DClosed.domain : Set H) (polyCore : Set H) (Afun c) (S c hc)
    (Afun_core c) (Afun_closed c) DPMap_le_DClosed.1 ?_ f f.2
  · have h := hmain.2
    rw [Afun_apply c _ (S_range_subset_domain c hc f), Afun_apply c _ f.2] at h
    exact h
  · intro x hx
    obtain ⟨q, hq⟩ := LinearMap.mem_range.mp hx
    have hxq : x = polyLp q := hq.symm
    subst hxq
    refine ⟨S_range_subset_domain c hc (polyLp q), ?_⟩
    rw [Afun_apply c _ (S_range_subset_domain c hc (polyLp q)),
      Afun_apply c _ (DPMap_le_DClosed.1 hx)]
    exact AClosed_S_polyLp c hc q (DPMap_le_DClosed.1 hx)

#print axioms Manuscript14Gram.Theorem52.S_range_subset_domain
#print axioms Manuscript14Gram.Theorem52.gram_commutes_with_perturbed_legendre

end Manuscript14Gram.Theorem52

end
