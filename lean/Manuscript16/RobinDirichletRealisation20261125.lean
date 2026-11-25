import Mathlib
import Manuscript16.RobinDirichletInjective20261125
import Manuscript16.RobinDirichletWeakResolvent20261125

/-!
# M16 v16.5 §14.2, Proposition 14.2: self-adjoint operators `H_D`, `H_R` on `L²(0,∞)` whose resolvents at `t` are the Green operators

Fix `c = ‖κ‖²`, `β > 0`, `t < c − β²` and `a = √(c − t)`.  The integral operators `K_D = KDop`,
`K_R = KRop` of the printed Green kernels are bounded (#605), self-adjoint and positive (#606),
injective with dense range (#607), and left inverses of `−d²/dz² + a²` on the Dirichlet and Robin
cores (#610).  This file builds from them two unbounded operators on `L²(0,∞)` (Mathlib
`LinearPMap`s)

* `H_D = t + K_D⁻¹` with domain `ran K_D`,
* `H_R = t + K_R⁻¹` with domain `ran K_R`,

and proves:

* `HD_isSelfAdjoint`, `HR_isSelfAdjoint`: both are self-adjoint in Mathlib's sense
  (`IsSelfAdjoint`, i.e. equal to their adjoint `LinearPMap.adjoint`, with dense domain);
* `HD_resolvent`, `HR_resolvent`: `(H − t) K f = f` for every `f ∈ L²(0,∞)` and `K (H − t) u = u` for
  every `u` in the domain, i.e. `(H_D − t)⁻¹ = K_D`, `(H_R − t)⁻¹ = K_R` as operators on `L²(0,∞)`;
* `HD_core`, `HR_core`: every `C²` test function with compact support and `φ(0) = 0`
  (resp. `φ'(0) = −β φ(0)`) lies in the domain of `H_D` (resp. `H_R`), with
  `H φ = −φ'' + c φ` almost everywhere on `(0,∞)`: the operators extend `−d²/dz² + c` on the
  Dirichlet and Robin cores;
* hence, with `KRop_sub_KDop` of #605 (not re-proved), `(H_R − t)⁻¹ − (H_D − t)⁻¹ = K_R − K_D` is the
  rank-one operator `(a − β)⁻¹ |v_a⟩⟨v_a|` (`robinDiff`) of #603;
* the manuscript form `prop14_2_selfadjoint_realisation`.

The abstract part (Part A) is the elementary graph computation behind "`t + K⁻¹` is self-adjoint
when `K` is bounded, self-adjoint and injective"; it is a standard fact and is proved here only as
glue, through Mathlib's characterisation of the adjoint graph.

Not claimed: that `H_D`, `H_R` coincide with the realisations of `−d²/dz² + c` on the Sobolev
domains `{u ∈ H²(0,∞) : u(0) = 0}` and `{u ∈ H²(0,∞) : u'(0) = −β u(0)}` (no trace theorem, no
Sobolev space is used), essential self-adjointness on the two cores, and independence of `H_D`,
`H_R` from the auxiliary level `t` (each is built from the Green operator at one fixed `t`); the
essential spectrum; Schatten-ideal membership; any Maxwell or geometric identification.
-/

namespace Manuscript16.RobinDirichletRealisation

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal ComplexInnerProductSpace
open Manuscript16.RobinDirichletRankOne Manuscript16.RobinDirichletL2Bounded
  Manuscript16.RobinDirichletPositive Manuscript16.RobinDirichletInjective
  Manuscript16.RobinDirichletWeakResolvent

noncomputable section

/-! ### Part A: `t + K⁻¹` for a bounded self-adjoint injective `K` -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The linear map `f ↦ (K f, f + t K f)`. -/
def graphMap (K : E →L[ℂ] E) (t : ℝ) : E →ₗ[ℂ] E × E :=
  LinearMap.prod (K : E →ₗ[ℂ] E) (LinearMap.id + (t : ℂ) • (K : E →ₗ[ℂ] E))

/-- The graph `{(K f, f + t K f) : f ∈ E}`. -/
def graphSub (K : E →L[ℂ] E) (t : ℝ) : Submodule ℂ (E × E) := LinearMap.range (graphMap K t)

theorem mem_graphSub {K : E →L[ℂ] E} {t : ℝ} {x : E × E} :
    x ∈ graphSub K t ↔ ∃ f : E, K f = x.1 ∧ f + (t : ℂ) • K f = x.2 := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f, rfl, rfl⟩
  · rintro ⟨f, h1, h2⟩
    exact ⟨f, Prod.ext h1 h2⟩

theorem graphSub_fst_eq_zero {K : E →L[ℂ] E} (hK : Function.Injective K) (t : ℝ) :
    ∀ (x : E × E) (_hx : x ∈ graphSub K t) (_hx' : x.fst = 0), x.snd = 0 := by
  intro x hx h0
  obtain ⟨f, h1, h2⟩ := mem_graphSub.mp hx
  have hf : f = 0 := hK (by rw [h1, h0, map_zero])
  rw [← h2, hf, map_zero, smul_zero, add_zero]

/-- The operator `t + K⁻¹` with domain `ran K`, as a Mathlib `LinearPMap`. -/
def realisation (K : E →L[ℂ] E) (t : ℝ) : E →ₗ.[ℂ] E := (graphSub K t).toLinearPMap

variable {K : E →L[ℂ] E} {t : ℝ}

theorem realisation_graph (hK : Function.Injective K) :
    (realisation K t).graph = graphSub K t :=
  Submodule.toLinearPMap_graph_eq _ (graphSub_fst_eq_zero hK t)

theorem mem_realisation_domain (hK : Function.Injective K) {u : E} :
    u ∈ (realisation K t).domain ↔ ∃ f, K f = u := by
  rw [LinearPMap.mem_domain_iff, realisation_graph hK]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨f, h1, -⟩ := mem_graphSub.mp hy
    exact ⟨f, h1⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f + (t : ℂ) • K f, mem_graphSub.mpr ⟨f, rfl, rfl⟩⟩

/-- The domain of `t + K⁻¹` is the range of `K`. -/
theorem realisation_domain (hK : Function.Injective K) :
    ((realisation K t).domain : Set E) = Set.range K := by
  ext u
  exact mem_realisation_domain hK

theorem K_mem_domain (hK : Function.Injective K) (f : E) : K f ∈ (realisation K t).domain :=
  (mem_realisation_domain hK).mpr ⟨f, rfl⟩

/-- `(t + K⁻¹)(K f) = f + t K f`. -/
theorem realisation_apply_K (hK : Function.Injective K) (f : E) :
    realisation K t ⟨K f, K_mem_domain hK f⟩ = f + (t : ℂ) • K f := by
  symm
  rw [LinearPMap.image_iff, realisation_graph hK]
  exact mem_graphSub.mpr ⟨f, rfl, rfl⟩

/-- `(H − t)(K f) = f` for every `f`. -/
theorem realisation_sub_K (hK : Function.Injective K) (f : E) :
    realisation K t ⟨K f, K_mem_domain hK f⟩ - (t : ℂ) • K f = f := by
  rw [realisation_apply_K hK f, add_sub_cancel_right]

/-- `K ((H − t) u) = u` for every `u` in the domain. -/
theorem K_realisation_sub (hK : Function.Injective K) (u : (realisation K t).domain) :
    K (realisation K t u - (t : ℂ) • (u : E)) = u := by
  obtain ⟨f, hf⟩ := (mem_realisation_domain hK).mp u.2
  have hu : u = ⟨K f, K_mem_domain hK f⟩ := Subtype.ext hf.symm
  rw [hu, realisation_sub_K hK f]

/-- A self-adjoint injective bounded operator has dense range. -/
theorem denseRange_of_isSelfAdjoint' [CompleteSpace E] (hK : IsSelfAdjoint K) (hinj : Function.Injective K) :
    DenseRange K := by
  have h1 : K.rangeᗮ = ⊥ := by
    rw [ContinuousLinearMap.orthogonal_range, hK.adjoint_eq]
    exact LinearMap.ker_eq_bot.mpr hinj
  have h2 : K.range.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.mpr h1
  have h3 := (Submodule.dense_iff_topologicalClosure_eq_top).mpr h2
  rwa [LinearMap.coe_range] at h3

theorem realisation_dense_domain [CompleteSpace E] (hK : IsSelfAdjoint K) (hinj : Function.Injective K) :
    Dense ((realisation K t).domain : Set E) := by
  rw [realisation_domain hinj]
  exact denseRange_of_isSelfAdjoint' hK hinj

theorem inner_K_symm [CompleteSpace E] (hK : IsSelfAdjoint K) (x y : E) : ⟪K x, y⟫ = ⟪x, K y⟫ :=
  hK.isSymmetric x y

/-- **`t + K⁻¹` is self-adjoint** when `K` is bounded, self-adjoint and injective and `t` is real. -/
theorem realisation_isSelfAdjoint [CompleteSpace E] (hK : IsSelfAdjoint K) (hinj : Function.Injective K) :
    IsSelfAdjoint (realisation K t) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (realisation_dense_domain hK hinj),
    realisation_graph hinj]
  have hconj : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  ext ⟨x₁, x₂⟩
  rw [Submodule.mem_adjoint_iff]
  constructor
  · intro h
    -- `⟪f, x₁ + t K x₁ − K x₂⟫ = 0` for every `f`
    have key : ∀ f : E, ⟪f, x₁ + (t : ℂ) • K x₁ - K x₂⟫ = 0 := by
      intro f
      have := h (K f) (f + (t : ℂ) • K f) (mem_graphSub.mpr ⟨f, rfl, rfl⟩)
      simp only at this
      rw [inner_add_left, inner_smul_left, hconj, inner_K_symm hK, inner_K_symm hK] at this
      rw [inner_sub_right, inner_add_right, inner_smul_right]
      linear_combination this
    have hz : x₁ + (t : ℂ) • K x₁ - K x₂ = 0 :=
      inner_self_eq_zero.mp (key _)
    have h1 : K x₂ - (t : ℂ) • K x₁ = x₁ := by
      rw [sub_eq_zero] at hz
      rw [← hz, add_sub_cancel_right]
    refine mem_graphSub.mpr ⟨x₂ - (t : ℂ) • x₁, ?_, ?_⟩
    · simp only [map_sub, map_smul]
      exact h1
    · simp only [map_sub, map_smul]
      rw [h1, sub_add_cancel]
  · intro hx a b hab
    obtain ⟨g, hg1, hg2⟩ := mem_graphSub.mp hx
    obtain ⟨f, hf1, hf2⟩ := mem_graphSub.mp hab
    simp only at hg1 hg2 hf1 hf2 ⊢
    rw [← hg1, ← hg2, ← hf1, ← hf2, inner_add_left, inner_smul_left, hconj, inner_add_right,
      inner_smul_right, inner_K_symm hK f g]
    ring

end Abstract

/-! ### Part B: the Dirichlet and Robin operators on `L²(0,∞)` -/

variable {a β : ℝ}

/-- `H_D = t + K_D⁻¹` on `L²(0,∞)`, domain `ran K_D`. -/
def HD (ha : 0 < a) (t : ℝ) : L2 →ₗ.[ℂ] L2 := realisation (KDop ha) t

/-- `H_R = t + K_R⁻¹` on `L²(0,∞)`, domain `ran K_R`. -/
def HR (ha : 0 < a) (β t : ℝ) : L2 →ₗ.[ℂ] L2 := realisation (KRop ha β) t

theorem HD_isSelfAdjoint (ha : 0 < a) (t : ℝ) : IsSelfAdjoint (HD ha t) :=
  realisation_isSelfAdjoint (KDop_isSelfAdjoint ha) (KDop_injective ha)

theorem HR_isSelfAdjoint (ha : 0 < a) (hab : β < a) (t : ℝ) : IsSelfAdjoint (HR ha β t) :=
  realisation_isSelfAdjoint (KRop_isSelfAdjoint ha hab) (KRop_injective ha hab)

theorem HD_domain (ha : 0 < a) (t : ℝ) :
    ((HD ha t).domain : Set L2) = Set.range (KDop ha) :=
  realisation_domain (KDop_injective ha)

theorem HR_domain (ha : 0 < a) (hab : β < a) (t : ℝ) :
    ((HR ha β t).domain : Set L2) = Set.range (KRop ha β) :=
  realisation_domain (KRop_injective ha hab)

/-- `(H_D − t)⁻¹ = K_D`: `(H_D − t) K_D f = f` for every `f ∈ L²(0,∞)` and `K_D (H_D − t) u = u`
for every `u` in the domain. -/
theorem HD_resolvent (ha : 0 < a) (t : ℝ) :
    (∀ f : L2, HD ha t ⟨KDop ha f, K_mem_domain (KDop_injective ha) f⟩ - (t : ℂ) • KDop ha f = f) ∧
    (∀ u : (HD ha t).domain, KDop ha (HD ha t u - (t : ℂ) • (u : L2)) = u) :=
  ⟨realisation_sub_K (KDop_injective ha), K_realisation_sub (KDop_injective ha)⟩

/-- `(H_R − t)⁻¹ = K_R`. -/
theorem HR_resolvent (ha : 0 < a) (hab : β < a) (t : ℝ) :
    (∀ f : L2, HR ha β t ⟨KRop ha β f, K_mem_domain (KRop_injective ha hab) f⟩ -
        (t : ℂ) • KRop ha β f = f) ∧
    (∀ u : (HR ha β t).domain, KRop ha β (HR ha β t u - (t : ℂ) • (u : L2)) = u) :=
  ⟨realisation_sub_K (KRop_injective ha hab), K_realisation_sub (KRop_injective ha hab)⟩

/-- On test functions, `−φ'' + a² φ + t φ = −φ'' + c φ` almost everywhere on `(0,∞)` when
`a² = c − t`. -/
theorem toLp_Hloc_add_ae {c t : ℝ} (ht : t < c - β ^ 2) {φ : ℝ → ℝ} (hφ : IsTest φ) :
    (((hφ.memLp_Hloc (aOf c t)).toLp _ + (t : ℂ) • hφ.memLp.toLp _ : L2) : ℝ → ℂ) =ᵐ[μ]
      fun z => ((-deriv (deriv φ) z + c * φ z : ℝ) : ℂ) := by
  filter_upwards [Lp.coeFn_add ((hφ.memLp_Hloc (aOf c t)).toLp _) ((t : ℂ) • hφ.memLp.toLp _),
    Lp.coeFn_smul (t : ℂ) (hφ.memLp.toLp _), (hφ.memLp_Hloc (aOf c t)).coeFn_toLp,
    hφ.memLp.coeFn_toLp] with z h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, Hloc_aOf ht]
  push_cast
  ring

/-- `H_D` extends `−d²/dz² + c` on the Dirichlet core: for a `C²` test function with compact
support and `φ(0) = 0`, `φ ∈ dom H_D` and `H_D φ = −φ'' + c φ` a.e. on `(0,∞)`. -/
theorem HD_core {c t : ℝ} (ht : t < c - β ^ 2) (ha : 0 < aOf c t) {φ : ℝ → ℝ} (hφ : IsTest φ)
    (hφ0 : φ 0 = 0) :
    ∃ h : hφ.memLp.toLp _ ∈ (HD ha t).domain,
      (HD ha t ⟨hφ.memLp.toLp _, h⟩ : ℝ → ℂ) =ᵐ[μ]
        fun z => ((-deriv (deriv φ) z + c * φ z : ℝ) : ℂ) := by
  have hK := KDop_Hloc ha hφ hφ0
  refine ⟨hK ▸ K_mem_domain (KDop_injective ha) _, ?_⟩
  have happ := realisation_apply_K (t := t) (KDop_injective ha) ((hφ.memLp_Hloc (aOf c t)).toLp _)
  have heq : (HD ha t ⟨hφ.memLp.toLp _, hK ▸ K_mem_domain (KDop_injective ha) _⟩ : L2) =
      (hφ.memLp_Hloc (aOf c t)).toLp _ + (t : ℂ) • hφ.memLp.toLp _ := by
    have hsub : (⟨hφ.memLp.toLp _, hK ▸ K_mem_domain (KDop_injective ha) _⟩ :
        (HD ha t).domain) = ⟨KDop ha ((hφ.memLp_Hloc (aOf c t)).toLp _),
          K_mem_domain (KDop_injective ha) _⟩ := Subtype.ext hK.symm
    rw [hsub]
    exact happ.trans (by rw [hK])
  rw [heq]
  exact toLp_Hloc_add_ae ht hφ

/-- `H_R` extends `−d²/dz² + c` on the Robin core: for a `C²` test function with compact support
and `φ'(0) = −β φ(0)`, `φ ∈ dom H_R` and `H_R φ = −φ'' + c φ` a.e. on `(0,∞)`. -/
theorem HR_core {c t : ℝ} (ht : t < c - β ^ 2) (ha : 0 < aOf c t) (hab : β < aOf c t)
    {φ : ℝ → ℝ} (hφ : IsTest φ) (hφR : deriv φ 0 = -β * φ 0) :
    ∃ h : hφ.memLp.toLp _ ∈ (HR ha β t).domain,
      (HR ha β t ⟨hφ.memLp.toLp _, h⟩ : ℝ → ℂ) =ᵐ[μ]
        fun z => ((-deriv (deriv φ) z + c * φ z : ℝ) : ℂ) := by
  have hK := KRop_Hloc ha hab hφ hφR
  refine ⟨hK ▸ K_mem_domain (KRop_injective ha hab) _, ?_⟩
  have happ := realisation_apply_K (t := t) (KRop_injective ha hab)
    ((hφ.memLp_Hloc (aOf c t)).toLp _)
  have heq : (HR ha β t ⟨hφ.memLp.toLp _, hK ▸ K_mem_domain (KRop_injective ha hab) _⟩ : L2) =
      (hφ.memLp_Hloc (aOf c t)).toLp _ + (t : ℂ) • hφ.memLp.toLp _ := by
    have hsub : (⟨hφ.memLp.toLp _, hK ▸ K_mem_domain (KRop_injective ha hab) _⟩ :
        (HR ha β t).domain) = ⟨KRop ha β ((hφ.memLp_Hloc (aOf c t)).toLp _),
          K_mem_domain (KRop_injective ha hab) _⟩ := Subtype.ext hK.symm
    rw [hsub]
    exact happ.trans (by rw [hK])
  rw [heq]
  exact toLp_Hloc_add_ae ht hφ

/-! ### Manuscript form -/

/-- Proposition 14.2 (§14.2), self-adjoint form: with `c = ‖κ‖²`, `β > 0`, `t < c − β²` and
`a = √(c − t)`, the operators `H_D = t + K_D⁻¹` and `H_R = t + K_R⁻¹` on `L²(0,∞)` are self-adjoint,
`(H_D − t)⁻¹ = K_D` and `(H_R − t)⁻¹ = K_R`, they extend `−d²/dz² + c` on the Dirichlet and Robin
cores, and `(H_R − t)⁻¹ − (H_D − t)⁻¹ = robinDiff`. -/
theorem prop14_2_selfadjoint_realisation {κ : EuclideanSpace ℝ (Fin 2)} {t : ℝ} (hβ : 0 < β)
    (ht : t < ‖κ‖ ^ 2 - β ^ 2) :
    IsSelfAdjoint (HD (aOf_pos hβ ht) t) ∧ IsSelfAdjoint (HR (aOf_pos hβ ht) β t) ∧
    ((HD (aOf_pos hβ ht) t).domain : Set L2) = Set.range (KDop (aOf_pos hβ ht)) ∧
    ((HR (aOf_pos hβ ht) β t).domain : Set L2) = Set.range (KRop (aOf_pos hβ ht) β) ∧
    (∀ u : (HD (aOf_pos hβ ht) t).domain,
      KDop (aOf_pos hβ ht) (HD (aOf_pos hβ ht) t u - (t : ℂ) • (u : L2)) = u) ∧
    (∀ u : (HR (aOf_pos hβ ht) β t).domain,
      KRop (aOf_pos hβ ht) β (HR (aOf_pos hβ ht) β t u - (t : ℂ) • (u : L2)) = u) ∧
    (∀ φ : ℝ → ℝ, ∀ hφ : IsTest φ, φ 0 = 0 →
      ∃ h : hφ.memLp.toLp _ ∈ (HD (aOf_pos hβ ht) t).domain,
        (HD (aOf_pos hβ ht) t ⟨hφ.memLp.toLp _, h⟩ : ℝ → ℂ) =ᵐ[μ]
          fun z => ((-deriv (deriv φ) z + ‖κ‖ ^ 2 * φ z : ℝ) : ℂ)) ∧
    (∀ φ : ℝ → ℝ, ∀ hφ : IsTest φ, deriv φ 0 = -β * φ 0 →
      ∃ h : hφ.memLp.toLp _ ∈ (HR (aOf_pos hβ ht) β t).domain,
        (HR (aOf_pos hβ ht) β t ⟨hφ.memLp.toLp _, h⟩ : ℝ → ℂ) =ᵐ[μ]
          fun z => ((-deriv (deriv φ) z + ‖κ‖ ^ 2 * φ z : ℝ) : ℂ)) ∧
    KRop (aOf_pos hβ ht) β - KDop (aOf_pos hβ ht) = robinDiff (aOf_pos hβ ht) β := by
  have hab := lt_aOf hβ ht
  have ha := aOf_pos hβ ht
  exact ⟨HD_isSelfAdjoint ha t, HR_isSelfAdjoint ha hab t, HD_domain ha t, HR_domain ha hab t,
    (HD_resolvent ha t).2, (HR_resolvent ha hab t).2,
    fun φ hφ hφ0 => HD_core ht ha hφ hφ0, fun φ hφ hφR => HR_core ht ha hab hφ hφR,
    KRop_sub_KDop ha β⟩

end

end Manuscript16.RobinDirichletRealisation

#print axioms Manuscript16.RobinDirichletRealisation.mem_graphSub
#print axioms Manuscript16.RobinDirichletRealisation.graphSub_fst_eq_zero
#print axioms Manuscript16.RobinDirichletRealisation.realisation_graph
#print axioms Manuscript16.RobinDirichletRealisation.mem_realisation_domain
#print axioms Manuscript16.RobinDirichletRealisation.realisation_domain
#print axioms Manuscript16.RobinDirichletRealisation.K_mem_domain
#print axioms Manuscript16.RobinDirichletRealisation.realisation_apply_K
#print axioms Manuscript16.RobinDirichletRealisation.realisation_sub_K
#print axioms Manuscript16.RobinDirichletRealisation.K_realisation_sub
#print axioms Manuscript16.RobinDirichletRealisation.denseRange_of_isSelfAdjoint'
#print axioms Manuscript16.RobinDirichletRealisation.realisation_dense_domain
#print axioms Manuscript16.RobinDirichletRealisation.inner_K_symm
#print axioms Manuscript16.RobinDirichletRealisation.realisation_isSelfAdjoint
#print axioms Manuscript16.RobinDirichletRealisation.HD_isSelfAdjoint
#print axioms Manuscript16.RobinDirichletRealisation.HR_isSelfAdjoint
#print axioms Manuscript16.RobinDirichletRealisation.HD_domain
#print axioms Manuscript16.RobinDirichletRealisation.HR_domain
#print axioms Manuscript16.RobinDirichletRealisation.HD_resolvent
#print axioms Manuscript16.RobinDirichletRealisation.HR_resolvent
#print axioms Manuscript16.RobinDirichletRealisation.toLp_Hloc_add_ae
#print axioms Manuscript16.RobinDirichletRealisation.HD_core
#print axioms Manuscript16.RobinDirichletRealisation.HR_core
#print axioms Manuscript16.RobinDirichletRealisation.prop14_2_selfadjoint_realisation
