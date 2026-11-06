import Mathlib
import SpecialImaginaryPoint.GramKernelBispectral
import GegenbauerFock.GramIntegralComplete
import GegenbauerFock.UltrasphericalSturmLiouvillePolynomialCore

/-!
# Manuscript 14, Theorem 5.2 (domain-level commutation): statement and proof skeleton

This module fixes, in Lean 4, the exact statement of Theorem 5.2 of manuscript 14
(the Legendre–Gram operator `S_{1/2,c}` maps `H_{1/2}` into the domain of the perturbed
Gegenbauer operator `𝒜_c = D_{1/2} - c² M_{u²}` and commutes with it on the whole closed
domain), and reduces it to four analytic lemmas, each stated in full and left as `sorry`:

* `green_identity`            — the single Green identity on `C²` functions
                                 (two integrations by parts; the boundary terms carry the
                                 factor `1-u²`, which vanishes at `±1`);
* `gramSeries_smooth`         — `S f` is an explicit entire power series in `u` for every
                                 `f ∈ H` (series–integral interchange, no differentiation
                                 under the integral sign);
* `core_commutation`          — the pointwise identity `𝒜_c (S p) = S (𝒜_c p)` on the
                                 polynomial core (bispectral kernel balance + Green in the
                                 `v` variable);
* `smooth_mem_closure_domain` — every `C²` function lies in the domain of the graph closure of
                                 the polynomial operator `𝒜_c⁰`, on which the closure acts as
                                 the differential expression (Weierstrass approximation of
                                 `g''`, integrated twice; no Legendre coefficient analysis).

Two bookkeeping facts are also left as `sorry` and are listed as such:

* `polyLp_injective`          — two polynomials with the same `L²(ν)` class coincide
                                 (`ν` has no atoms, so the zero set of the difference is
                                 infinite);
* `APMap_isClosable`          — `𝒜_c⁰` is closable (densely defined and symmetric on complex
                                 `L²`; the complex counterpart of
                                 `GegenbauerFock.Ultraspherical.sturmRealPMap_isClosable`).

The remaining steps are already kernel-checked in this repository:
the abstract closed-graph-core transport (`Manuscript14Gram.closed_graph_core_commutation`),
the bispectral kernel balance (`Manuscript14Gram.gram_bispectral_kernel_balance`), the
endpoint fluxes, and the bounded complex-`L²` Gram operator with its kernel-integral identity
(`GegenbauerFock.GeneralUltrasphericalFock.gram_eq_integralLp`).

**Status: skeleton.**  Every declaration below is type-checked; the lemmas named above carry
`sorry`, and the final theorem therefore depends on `sorryAx`.  The axiom audit at the end of
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

/-- **Bookkeeping (sorry).**  Two polynomials with the same `L²(ν)` class are equal:
`ν` is absolutely continuous with a positive density on `(-1,1)`, so the difference vanishes
on an infinite set and is the zero polynomial. -/
theorem polyLinear_injective : Function.Injective polyLinear := by
  sorry

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
    simp only [derivative_smul, smul_eq_C_mul, RingHom.id_apply]
    ring

/-- The polynomial-domain operator `𝒜_c⁰ : 𝒫 → H`, `polyLp p ↦ polyLp (APoly c p)`,
as a partially defined linear map with domain `𝒫`. -/
def APMap (c : ℝ) : H →ₗ.[ℂ] H where
  domain := polyCore
  toFun := polyLinear ∘ₗ APoly c ∘ₗ polyEquiv.symm.toLinearMap

theorem polyEquiv_apply (p : ℂ[X]) :
    polyEquiv p = ⟨polyLp p, LinearMap.mem_range_self polyLinear p⟩ := by
  apply Subtype.ext
  exact LinearEquiv.ofInjective_apply polyLinear_injective p

theorem APMap_apply (c : ℝ) (p : ℂ[X]) :
    APMap c ⟨polyLp p, LinearMap.mem_range_self polyLinear p⟩ = polyLp (APoly c p) := by
  rw [← polyEquiv_apply]
  show polyLinear (APoly c (polyEquiv.symm (polyEquiv p))) = polyLinear (APoly c p)
  rw [polyEquiv.symm_apply_apply]

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

/-- `S f` is the `L²` class of its kernel form (certified identity `gram_eq_integralLp`,
plus the parameter identity `u v / (4 · (1/(4c))) = c u v`). -/
theorem S_apply_ae (c : ℝ) (hc : 0 < c) (f : H) :
    (S c hc f : ℝ → ℂ) =ᵐ[ν] SFun c (f : ℝ → ℂ) := by
  have h1 : S c hc f =
      GegenbauerFock.GeneralUltrasphericalFock.gramKernelIntegralLp (1 / 2) (1 / (4 * c))
        half_pos (by positivity) f :=
    GegenbauerFock.GeneralUltrasphericalFock.gram_eq_integralLp _ _ _ _ f
  rw [h1]
  unfold GegenbauerFock.GeneralUltrasphericalFock.gramKernelIntegralLp
  refine (GegenbauerFock.GeneralUltrasphericalFock.gramKernelIntegral_memLp _ _ _ _
    f).coeFn_toLp.trans ?_
  filter_upwards with u
  unfold GegenbauerFock.GeneralUltrasphericalFock.gramKernelIntegral SFun
  congr 1
  funext v
  have hc' : c ≠ 0 := ne_of_gt hc
  have : u * v / (4 * (1 / (4 * c))) = c * u * v := by
    field_simp
    ring
  rw [this, mul_comm]

/-! ## The four analytic lemmas -/

/-- **Lemma 1 (Green).**  For `f, g` of class `C²` on the real line,
`∫_{-1}^{1} [(1-u²) f']' g = ∫_{-1}^{1} f [(1-u²) g']'`.  Two integrations by parts
(`intervalIntegral.integral_mul_deriv_eq_deriv_mul`); the boundary terms contain the factor
`1 - u²`, which vanishes at `±1`.  The endpoint-flux lemmas
`Manuscript14Gram.gram_endpoint_flux_plus/minus` are these boundary terms for the kernel. -/
theorem green_identity (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    ∫ u in (-1 : ℝ)..1, deriv (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) * deriv f t) u * g u
      = ∫ u in (-1 : ℝ)..1,
          f u * deriv (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) * deriv g t) u := by
  sorry

/-- The `k`-th moment `m_k(f) = ∫ v^k f(v) dν(v)` of `f ∈ L²(ν)`; for a polynomial `f` it is
an exact rational combination of the coefficients. -/
def moment (f : ℝ → ℂ) (k : ℕ) : ℂ := ∫ v : ℝ, (v : ℂ) ^ k * f v ∂ν

/-- The explicit entire series `u ↦ ∑_k c^k u^k / k! · m_k(f)`. -/
def gramSeries (c : ℝ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑' k : ℕ, ((c : ℂ) ^ k * (u : ℂ) ^ k / (Nat.factorial k : ℂ)) * moment f k

/-- **Lemma 2 (series representation, no differentiation under the integral).**
For every `f ∈ H`, `(S f)(u) = ∑_k c^k u^k/k! · m_k(f)` for every real `u`, and the series
is a `C^∞` function of `u`.  Proof: `exp(c u v) = ∑ (c u v)^k/k!`; the interchange with the
`ν`-integral is dominated convergence with the summable majorant `(c|u|)^k/k! · ‖f‖_{L¹}`
on `[-1,1]` (`MeasureTheory.hasSum_integral_of_dominated_convergence`, the pattern of
`Manuscript14Sonine.sonine_interval_hasSum`); the resulting power series has infinite radius
of convergence, since `|m_k(f)| ≤ ‖f‖_{L²}` by Cauchy–Schwarz. -/
theorem gramSeries_smooth (c : ℝ) (hc : 0 < c) (f : H) :
    (∀ u : ℝ, SFun c (f : ℝ → ℂ) u = gramSeries c (f : ℝ → ℂ) u) ∧
      ContDiff ℝ ∞ (gramSeries c (f : ℝ → ℂ)) := by
  sorry

/-- **Lemma 3 (commutation on the core).**  For a polynomial `p`,
`𝒜_c (S p) = S (𝒜_c p)` pointwise on `[-1,1]`.  Proof: by Lemma 2, `𝒜_c` acts on `S p`
termwise; the bispectral balance `Manuscript14Gram.gram_bispectral_kernel_balance` moves the
differential expression from `u` to `v`, and Lemma 1 in the `v` variable (with `p` in place
of `g`) moves it onto `p`. -/
theorem core_commutation (c : ℝ) (hc : 0 < c) (p : ℂ[X]) :
    ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      AExpr c (gramSeries c (polyFun p)) u = SFun c (polyFun (APoly c p)) u := by
  sorry

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
From Lemmas 2 and 4 and the kernel identity `S_apply_ae`. -/
theorem S_range_subset_domain (c : ℝ) (hc : 0 < c) (f : H) :
    S c hc f ∈ (AClosed c).domain := by
  sorry

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
