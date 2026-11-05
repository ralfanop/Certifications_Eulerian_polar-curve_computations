import GegenbauerFock.Section7Intertwining
import GegenbauerFock.GaussianAreaIntrinsicEvaluationSharpNorm
import GegenbauerFock.GaussianAreaIntrinsicEvaluationContinuous
import GegenbauerFock.UltrasphericalSturmLiouvilleRealClosedCore
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealSpectralModes
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2HilbertBasis
import GegenbauerFock.UltrasphericalSturmLiouvilleExactGegenbauerSpectralClosure
import GegenbauerFock.OutputEntireCoefficientUniqueness
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Manuscript 13, Section 7.2 — the closed maximal Fock realization (Theorem 7.3, Corollary 7.4)

Notation.
* `Fock α` is the library's Bargmann–Fock space: the closed subspace
  `GaussianArea.entireGaussianL2Submodule α` of `L²(ℂ, (α/π)e^{-α|z|²} dA)` of classes with an
  entire representative; `rep α F = GaussianArea.entireRepresentative α F` is that (unique)
  entire representative.
* `fockDiffMax λ α` is the maximal realization of Definition 7.1 / Eq. (7.6):
  `Dom = {F ∈ Fock : 𝒟_λ F ∈ Fock}`, i.e. there is `G ∈ Fock` with
  `rep G = 𝒟_λ (rep F)` pointwise on `ℂ`; then `fockDiffMax F = G`.
  It is a Mathlib `LinearPMap`; `mem_graph_iff` characterises its graph concretely.
* `H_λ = L²([-1,1], ν_λ; ℂ)` is `Lp ℂ 2 (Ultraspherical.measure λ)`.
  The library realizes the Gegenbauer operator on the *real* space `L²(ν_λ; ℝ)` as the closure
  `A = (Ultraspherical.sturmRealPartialOperator λ).closure` of the polynomial operator
  `L_λ p = (1-u²)p'' - (2λ+1)up'`, i.e. `A = -D_λ`; its domain is exactly the diagonal
  weighted-ℓ² domain (`Ultraspherical.sturmRealClosed_eq_exact_monicGegenbauer_spectral_realization`)
  and the polynomials are a graph core (`Ultraspherical.sturmRealPartialOperator_closed_graph_eq`).
  The complex selfadjoint `D_λ` of Proposition 5.1 is the complexification:
  `Dom(D_λ) = {u + i v : u, v ∈ Dom A}` and `D_λ (u + i v) = -(A u + i A v)`.
  The real-to-complex map is `cxL λ` (pointwise `ofReal`).

Main results.
* `theorem_7_3_closed`, `theorem_7_3_dense`, `theorem_7_3_intertwining` (Theorem 7.3);
* `corollary_7_4_ne_zero`, `corollary_7_4_eigen`, `corollary_7_4_complete` (Corollary 7.4).
-/

noncomputable section

open MeasureTheory Polynomial Metric
open GegenbauerFock.Section7Intertwining

namespace GegenbauerFock.Section7Closed

/-! ## Notation -/

/-- The Bargmann–Fock space of the library (entire Gaussian-L² classes). -/
abbrev Fock (alpha : ℝ) : Type := GaussianArea.entireGaussianL2Submodule alpha

/-- The canonical entire representative of a Fock vector. -/
abbrev rep (alpha : ℝ) (F : Fock alpha) : ℂ → ℂ := GaussianArea.entireRepresentative alpha F

/-- The complex source Hilbert space `H_λ = L²(ν_λ; ℂ)`. -/
abbrev Hc (lam : ℝ) : Type := Lp ℂ 2 (Ultraspherical.measure lam)

/-- The real weighted space `L²(ν_λ; ℝ)` carrying the library's Sturm–Liouville operator. -/
abbrev Hr (lam : ℝ) : Type := Lp ℝ 2 (Ultraspherical.measure lam)

theorem rep_differentiable (alpha : ℝ) (F : Fock alpha) : Differentiable ℂ (rep alpha F) :=
  GaussianArea.entireRepresentative_differentiable alpha F

theorem rep_add (alpha : ℝ) (ha : 0 < alpha) (F G : Fock alpha) :
    rep alpha (F + G) = rep alpha F + rep alpha G :=
  GaussianArea.entireRepresentative_add alpha ha F G

theorem rep_smul (alpha : ℝ) (ha : 0 < alpha) (c : ℂ) (F : Fock alpha) :
    rep alpha (c • F) = c • rep alpha F :=
  GaussianArea.entireRepresentative_smul alpha ha c F

theorem rep_zero (alpha : ℝ) (ha : 0 < alpha) : rep alpha 0 = 0 :=
  (GaussianArea.entireRepresentativeLinear alpha ha).map_zero

theorem rep_injective (alpha : ℝ) : Function.Injective (rep alpha) :=
  GaussianArea.entireRepresentative_injective alpha

/-! ## Algebra of the differential expression on entire functions -/

theorem differentiable_deriv {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (deriv f) := fun _ =>
  ((hf.differentiableOn (s := Set.univ)).deriv isOpen_univ).differentiableAt Filter.univ_mem

theorem deriv_add_fun {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    deriv (f + g) = deriv f + deriv g := by
  funext z
  exact ((hf z).hasDerivAt.add (hg z).hasDerivAt).deriv

theorem fockDiff_add (lam : ℝ) {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) :
    fockDiff lam (f + g) = fockDiff lam f + fockDiff lam g := by
  have h1 : deriv (f + g) = deriv f + deriv g := deriv_add_fun hf hg
  have h2 : deriv (deriv (f + g)) = deriv (deriv f) + deriv (deriv g) := by
    rw [h1]
    exact deriv_add_fun (differentiable_deriv hf) (differentiable_deriv hg)
  funext z
  unfold fockDiff
  rw [h2, h1]
  simp only [Pi.add_apply]
  ring

theorem fockDiff_smul (lam : ℝ) (c : ℂ) (f : ℂ → ℂ) :
    fockDiff lam (c • f) = c • fockDiff lam f := by
  have h1 : deriv (c • f) = fun z => c * deriv f z := by
    change deriv (fun x => c * f x) = _
    exact deriv_const_mul_field' c
  have h2 : deriv (deriv (c • f)) = fun z => c * deriv (deriv f) z := by
    rw [h1]
    exact deriv_const_mul_field' c
  funext z
  unfold fockDiff
  rw [h2, h1]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem fockDiff_zero (lam : ℝ) : fockDiff lam (0 : ℂ → ℂ) = 0 := by
  have h := fockDiff_smul lam 0 (0 : ℂ → ℂ)
  rw [zero_smul, zero_smul] at h
  exact h

/-! ## The maximal realization `𝒟_λ^max` (Eq. (7.6)) -/

/-- `Dom(𝒟_λ^max) = {F ∈ Fock : 𝒟_λ F ∈ Fock}`. -/
def maxDomain (lam alpha : ℝ) (ha : 0 < alpha) : Submodule ℂ (Fock alpha) where
  carrier := {F | ∃ G : Fock alpha, rep alpha G = fockDiff lam (rep alpha F)}
  zero_mem' := ⟨0, by
    rw [rep_zero alpha ha, fockDiff_zero]⟩
  add_mem' := by
    rintro F₁ F₂ ⟨G₁, h₁⟩ ⟨G₂, h₂⟩
    refine ⟨G₁ + G₂, ?_⟩
    rw [rep_add alpha ha, rep_add alpha ha, h₁, h₂,
      fockDiff_add lam (rep_differentiable alpha F₁) (rep_differentiable alpha F₂)]
  smul_mem' := by
    rintro c F ⟨G, h⟩
    refine ⟨c • G, ?_⟩
    rw [rep_smul alpha ha, rep_smul alpha ha, h, fockDiff_smul]

theorem mem_maxDomain_iff (lam alpha : ℝ) (ha : 0 < alpha) (F : Fock alpha) :
    F ∈ maxDomain lam alpha ha ↔ ∃ G : Fock alpha, rep alpha G = fockDiff lam (rep alpha F) :=
  Iff.rfl

/-- The chosen image `𝒟_λ F ∈ Fock` of a domain vector. -/
def maxImage (lam alpha : ℝ) (ha : 0 < alpha) (x : maxDomain lam alpha ha) : Fock alpha :=
  Classical.choose ((mem_maxDomain_iff lam alpha ha x).mp x.2)

theorem maxImage_spec (lam alpha : ℝ) (ha : 0 < alpha) (x : maxDomain lam alpha ha) :
    rep alpha (maxImage lam alpha ha x) = fockDiff lam (rep alpha x) :=
  Classical.choose_spec ((mem_maxDomain_iff lam alpha ha x).mp x.2)

/-- The action of `𝒟_λ^max` as a linear map on its domain. -/
def maxLinear (lam alpha : ℝ) (ha : 0 < alpha) : maxDomain lam alpha ha →ₗ[ℂ] Fock alpha where
  toFun := maxImage lam alpha ha
  map_add' := by
    intro x y
    apply rep_injective alpha
    rw [rep_add alpha ha, maxImage_spec, maxImage_spec, maxImage_spec,
      Submodule.coe_add, rep_add alpha ha,
      fockDiff_add lam (rep_differentiable alpha x) (rep_differentiable alpha y)]
  map_smul' := by
    intro c x
    apply rep_injective alpha
    rw [RingHom.id_apply, rep_smul alpha ha, maxImage_spec, maxImage_spec,
      Submodule.coe_smul, rep_smul alpha ha, fockDiff_smul]

/-- **The maximal Fock realization** `𝒟_λ^max` of Eq. (7.6), as an unbounded operator. -/
def fockDiffMax (lam alpha : ℝ) (ha : 0 < alpha) : Fock alpha →ₗ.[ℂ] Fock alpha where
  domain := maxDomain lam alpha ha
  toFun := maxLinear lam alpha ha

theorem fockDiffMax_domain (lam alpha : ℝ) (ha : 0 < alpha) (F : Fock alpha) :
    F ∈ (fockDiffMax lam alpha ha).domain ↔
      ∃ G : Fock alpha, rep alpha G = fockDiff lam (rep alpha F) :=
  Iff.rfl

theorem fockDiffMax_apply (lam alpha : ℝ) (ha : 0 < alpha)
    (x : (fockDiffMax lam alpha ha).domain) :
    rep alpha (fockDiffMax lam alpha ha x) = fockDiff lam (rep alpha x) :=
  maxImage_spec lam alpha ha x

/-- Concrete graph: `(F, G) ∈ graph 𝒟_λ^max ↔ rep G = 𝒟_λ (rep F)` on all of `ℂ`. -/
theorem mem_graph_iff (lam alpha : ℝ) (ha : 0 < alpha) (F G : Fock alpha) :
    (F, G) ∈ (fockDiffMax lam alpha ha).graph ↔ rep alpha G = fockDiff lam (rep alpha F) := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨y, hy, hyG⟩
    change (y : Fock alpha) = F at hy
    change fockDiffMax lam alpha ha y = G at hyG
    rw [← hyG, fockDiffMax_apply]
    change fockDiff lam (rep alpha (y : Fock alpha)) = fockDiff lam (rep alpha F)
    rw [hy]
  · intro h
    refine ⟨⟨F, ⟨G, h⟩⟩, rfl, ?_⟩
    apply rep_injective alpha
    rw [fockDiffMax_apply]
    exact h.symm

/-! ## Fock evaluation and Cauchy estimates -/

/-- A uniform evaluation constant on the disc `‖v‖ ≤ ‖z‖ + 2`. -/
def evalBound (alpha : ℝ) (z : ℂ) : ℝ := 1 + Real.exp (alpha * (‖z‖ + 2) ^ 2)

theorem rep_norm_le (alpha : ℝ) (ha : 0 < alpha) (F : Fock alpha) (v z : ℂ)
    (hv : ‖v‖ ≤ ‖z‖ + 2) : ‖rep alpha F v‖ ≤ evalBound alpha z * ‖F‖ := by
  have h1 := GaussianArea.entireRepresentative_norm_le_coherentEvaluation alpha ha v F
  have hK2 := GaussianArea.intrinsicEntireEvaluationContinuous_norm_sq alpha ha v
  set K := ‖GaussianArea.intrinsicEntireEvaluationContinuous alpha ha v‖ with hK_def
  have hsq : ‖v‖ ^ 2 ≤ (‖z‖ + 2) ^ 2 := by nlinarith [norm_nonneg v]
  have hexp : Real.exp (alpha * ‖v‖ ^ 2) ≤ Real.exp (alpha * (‖z‖ + 2) ^ 2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsq ha.le)
  have hK : K ≤ evalBound alpha z := by
    unfold evalBound
    nlinarith [sq_nonneg (2 * K - 1)]
  calc ‖rep alpha F v‖ ≤ K * ‖F‖ := h1
    _ ≤ evalBound alpha z * ‖F‖ := mul_le_mul_of_nonneg_right hK (norm_nonneg F)

/-- Cauchy's estimate on the unit circle around `c`. -/
theorem cauchy_deriv_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) {r B : ℝ}
    (hB : ∀ v : ℂ, ‖v‖ ≤ r → ‖f v‖ ≤ B) {c : ℂ} (hc : ‖c‖ + 1 ≤ r) : ‖deriv f c‖ ≤ B := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := c) (R := 1) (C := B)
    one_pos hf.diffContOnCl (fun v hv => hB v (by
      have hd : dist v c = 1 := hv
      rw [dist_eq_norm] at hd
      have := norm_le_insert' v c
      linarith))
  rw [div_one] at h
  exact h

theorem norm_four_complex : ‖(4 : ℂ)‖ = 4 := by
  have h : (4 : ℂ) = ((4 : ℝ) : ℂ) := by
    first
    | exact (Complex.ofReal_ofNat 4).symm
    | (push_cast; ring)
    | norm_num
  rw [h, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_pos (by norm_num)

/-- The constant in `|(𝒟_λ F)(z)| ≤ K_λ(z) ‖F‖`. -/
def fockDiffBound (lam alpha : ℝ) (z : ℂ) : ℝ :=
  (‖z‖ ^ 2 + |2 * lam + 1| * ‖z‖ + ‖z‖ ^ 2 / 4) * evalBound alpha z

theorem fockDiff_rep_norm_le (lam alpha : ℝ) (ha : 0 < alpha) (F : Fock alpha) (z : ℂ) :
    ‖fockDiff lam (rep alpha F) z‖ ≤ fockDiffBound lam alpha z * ‖F‖ := by
  set f := rep alpha F with hf_def
  have hf : Differentiable ℂ f := rep_differentiable alpha F
  set B := evalBound alpha z * ‖F‖ with hB_def
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have h0 : ‖f z‖ ≤ B := rep_norm_le alpha ha F z z (by linarith)
  have h1 : ‖deriv f z‖ ≤ B :=
    cauchy_deriv_le hf (r := ‖z‖ + 2) (fun v hv => rep_norm_le alpha ha F v z hv) (by linarith)
  have h2 : ‖deriv (deriv f) z‖ ≤ B :=
    cauchy_deriv_le (differentiable_deriv hf) (r := ‖z‖ + 1)
      (fun v hv => cauchy_deriv_le hf (r := ‖z‖ + 2)
        (fun w hw => rep_norm_le alpha ha F w z hw) (by linarith)) le_rfl
  have e2 : ‖z ^ 2 * deriv (deriv f) z‖ = ‖z‖ ^ 2 * ‖deriv (deriv f) z‖ := by
    rw [norm_mul, norm_pow]
  have e1 : ‖((2 * lam + 1 : ℝ) : ℂ) * z * deriv f z‖ = |2 * lam + 1| * ‖z‖ * ‖deriv f z‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have e0 : ‖z ^ 2 / 4 * f z‖ = ‖z‖ ^ 2 / 4 * ‖f z‖ := by
    rw [norm_mul, norm_div, norm_pow, norm_four_complex]
  have b2 : ‖z‖ ^ 2 * ‖deriv (deriv f) z‖ ≤ ‖z‖ ^ 2 * B :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have b1 : |2 * lam + 1| * ‖z‖ * ‖deriv f z‖ ≤ |2 * lam + 1| * ‖z‖ * B :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have b0 : ‖z‖ ^ 2 / 4 * ‖f z‖ ≤ ‖z‖ ^ 2 / 4 * B :=
    mul_le_mul_of_nonneg_left h0 (by positivity)
  have htot : fockDiffBound lam alpha z * ‖F‖ =
      ‖z‖ ^ 2 * B + |2 * lam + 1| * ‖z‖ * B + ‖z‖ ^ 2 / 4 * B := by
    rw [hB_def]
    unfold fockDiffBound
    ring
  unfold fockDiff
  rw [htot]
  calc ‖z ^ 2 * deriv (deriv f) z + ((2 * lam + 1 : ℝ) : ℂ) * z * deriv f z + z ^ 2 / 4 * f z‖
      ≤ ‖z ^ 2 * deriv (deriv f) z‖ + ‖((2 * lam + 1 : ℝ) : ℂ) * z * deriv f z‖ +
          ‖z ^ 2 / 4 * f z‖ := norm_add₃_le
    _ ≤ ‖z‖ ^ 2 * B + |2 * lam + 1| * ‖z‖ * B + ‖z‖ ^ 2 / 4 * B := by
      rw [e2, e1, e0]
      linarith

/-- `F ↦ (𝒟_λ F)(z)` is a continuous linear functional on the Fock space. -/
def fockDiffEval (lam alpha : ℝ) (ha : 0 < alpha) (z : ℂ) : Fock alpha →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun F => fockDiff lam (rep alpha F) z
      map_add' := by
        intro F G
        rw [rep_add alpha ha,
          fockDiff_add lam (rep_differentiable alpha F) (rep_differentiable alpha G)]
        rfl
      map_smul' := by
        intro c F
        rw [rep_smul alpha ha, fockDiff_smul, RingHom.id_apply]
        rfl }
    (fockDiffBound lam alpha z) (fun F => fockDiff_rep_norm_le lam alpha ha F z)

theorem fockDiffEval_apply (lam alpha : ℝ) (ha : 0 < alpha) (z : ℂ) (F : Fock alpha) :
    fockDiffEval lam alpha ha z F = fockDiff lam (rep alpha F) z := rfl

theorem evalCLM_apply (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) (F : Fock alpha) :
    GaussianArea.intrinsicEntireEvaluationContinuous alpha ha z F = rep alpha F z := rfl

/-! ## Theorem 7.3, closedness -/

/-- **Theorem 7.3 (closedness).** The graph of `𝒟_λ^max` is closed in `Fock × Fock`. -/
theorem theorem_7_3_closed (lam alpha : ℝ) (ha : 0 < alpha) :
    (fockDiffMax lam alpha ha).IsClosed := by
  have hgraph : ((fockDiffMax lam alpha ha).graph : Set (Fock alpha × Fock alpha)) =
      ⋂ z : ℂ, {p : Fock alpha × Fock alpha |
        GaussianArea.intrinsicEntireEvaluationContinuous alpha ha z p.2 =
          fockDiffEval lam alpha ha z p.1} := by
    ext p
    rw [Set.mem_iInter, SetLike.mem_coe]
    obtain ⟨F, G⟩ := p
    rw [mem_graph_iff]
    constructor
    · intro h z
      change rep alpha G z = fockDiff lam (rep alpha F) z
      rw [h]
    · intro h
      funext z
      exact h z
  unfold LinearPMap.IsClosed
  rw [hgraph]
  exact isClosed_iInter fun z =>
    isClosed_eq ((GaussianArea.intrinsicEntireEvaluationContinuous alpha ha z).continuous.comp
      continuous_snd) ((fockDiffEval lam alpha ha z).continuous.comp continuous_fst)

/-! ## Complexification of the real Sturm–Liouville operator -/

/-- Real-to-complex embedding `L²(ν_λ;ℝ) → L²(ν_λ;ℂ)`, `u ↦ (t ↦ (u t : ℂ))`. -/
def cxL (lam : ℝ) : Hr lam →L[ℝ] Hc lam :=
  Complex.ofRealCLM.compLpL 2 (Ultraspherical.measure lam)

/-- Real part `L²(ν_λ;ℂ) → L²(ν_λ;ℝ)`. -/
def reL (lam : ℝ) : Hc lam →L[ℝ] Hr lam :=
  Complex.reCLM.compLpL 2 (Ultraspherical.measure lam)

/-- Imaginary part `L²(ν_λ;ℂ) → L²(ν_λ;ℝ)`. -/
def imL (lam : ℝ) : Hc lam →L[ℝ] Hr lam :=
  Complex.imCLM.compLpL 2 (Ultraspherical.measure lam)

theorem cxL_ae (lam : ℝ) (u : Hr lam) :
    (cxL lam u : ℝ → ℂ) =ᵐ[Ultraspherical.measure lam] fun t => ((u t : ℝ) : ℂ) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := Ultraspherical.measure lam)
    Complex.ofRealCLM u] with t ht
  rw [← Complex.ofRealCLM_apply]
  exact ht

theorem reL_ae (lam : ℝ) (f : Hc lam) :
    (reL lam f : ℝ → ℝ) =ᵐ[Ultraspherical.measure lam] fun t => (f t).re := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := Ultraspherical.measure lam)
    Complex.reCLM f] with t ht
  rw [← Complex.reCLM_apply]
  exact ht

theorem imL_ae (lam : ℝ) (f : Hc lam) :
    (imL lam f : ℝ → ℝ) =ᵐ[Ultraspherical.measure lam] fun t => (f t).im := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := Ultraspherical.measure lam)
    Complex.imCLM f] with t ht
  rw [← Complex.imCLM_apply]
  exact ht

theorem reL_cxL (lam : ℝ) (u : Hr lam) : reL lam (cxL lam u) = u := by
  apply Lp.ext
  filter_upwards [reL_ae lam (cxL lam u), cxL_ae lam u] with t h1 h2
  rw [h1, h2, Complex.ofReal_re]

/-- Every `f ∈ H_λ` is `cx(Re f) + i cx(Im f)`. -/
theorem cxL_re_add_im (lam : ℝ) (f : Hc lam) :
    cxL lam (reL lam f) + Complex.I • cxL lam (imL lam f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (cxL lam (reL lam f)) (Complex.I • cxL lam (imL lam f)),
    Lp.coeFn_smul Complex.I (cxL lam (imL lam f)), cxL_ae lam (reL lam f),
    cxL_ae lam (imL lam f), reL_ae lam f, imL_ae lam f] with t h1 h2 h3 h4 h5 h6
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, h3, h4, h5, h6, mul_comm]
  exact Complex.re_add_im (f t)

theorem cxL_polynomial (lam : ℝ) (hlam : 0 < lam) (p : ℝ[X]) :
    cxL lam (Ultraspherical.sturmRealPolynomialLp lam hlam p) =
      polyLp lam hlam (p.map Complex.ofRealHom) := by
  apply Lp.ext
  filter_upwards [cxL_ae lam (Ultraspherical.sturmRealPolynomialLp lam hlam p),
    Ultraspherical.sturmRealPolynomialLp_ae_eval lam hlam p,
    polyLp_ae lam hlam (p.map Complex.ofRealHom)] with t h1 h2 h3
  rw [h1, h3, h2, Polynomial.eval_map]
  exact (Polynomial.eval₂_at_apply Complex.ofRealHom t).symm

theorem polyLp_neg (lam : ℝ) (hlam : 0 < lam) (q : ℂ[X]) :
    polyLp lam hlam (-q) = -polyLp lam hlam q := by
  apply Lp.ext
  filter_upwards [polyLp_ae lam hlam (-q), polyLp_ae lam hlam q,
    Lp.coeFn_neg (polyLp lam hlam q)] with t h1 h2 h3
  rw [h1, h3, Pi.neg_apply, h2, Polynomial.eval_neg]

/-- The complex Gegenbauer expression `D_λ` on real polynomials is `-L_λ`. -/
theorem gegenDiff_map (lam : ℝ) (p : ℝ[X]) :
    gegenDiff lam (p.map Complex.ofRealHom) =
      -((Ultraspherical.sturmPolynomial lam p).map Complex.ofRealHom) := by
  unfold gegenDiff Ultraspherical.sturmPolynomial
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, Polynomial.derivative_map, Complex.ofRealHom_eq_coe]
  ring

/-- The library's closed real Gegenbauer–Sturm operator `A = L_λ = -D_λ` on `L²(ν_λ;ℝ)`. -/
abbrev sturmClosed (lam : ℝ) (hlam : 0 < lam) : Hr lam →ₗ.[ℝ] Hr lam :=
  (Ultraspherical.sturmRealPartialOperator lam hlam).closure

/-- The domain used is exactly the diagonal weighted-ℓ² domain of Proposition 5.1
(library theorem, restated for the record). -/
theorem sturmClosed_domain_eq_diagonal (lam : ℝ) (hlam : 0 < lam) :
    ((sturmClosed lam hlam).domain : Set (Hr lam)) =
      Ultraspherical.sturmMonicHilbertUnshiftedDomain lam hlam :=
  (Ultraspherical.sturmRealClosed_eq_exact_monicGegenbauer_spectral_realization lam hlam).1

/-- The source-to-Fock map on graphs: `(a, b) ↦ (C (cx a), -C (cx b))`. -/
def graphMap (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Hr lam × Hr lam → Fock alpha × Fock alpha := fun q =>
  (GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha (cxL lam q.1),
    -GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha (cxL lam q.2))

theorem graphMap_continuous (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Continuous (graphMap lam alpha hlam ha) :=
  (((GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha).continuous.comp
      (cxL lam).continuous).comp continuous_fst).prodMk
    ((((GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha).continuous.comp
      (cxL lam).continuous).comp continuous_snd).neg)

/-- Theorem 7.2 transported to the graph: the polynomial Sturm graph is mapped into
`graph 𝒟_λ^max`. -/
theorem graphMap_polynomial_graph (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (q : Hr lam × Hr lam)
    (hq : q ∈ (Ultraspherical.sturmRealPartialOperator lam hlam).graph) :
    graphMap lam alpha hlam ha q ∈ (fockDiffMax lam alpha ha).graph := by
  rw [LinearPMap.mem_graph_iff] at hq
  obtain ⟨y, hy1, hy2⟩ := hq
  set p := Ultraspherical.sturmRealDomainRepresentative lam hlam y with hp_def
  have hp : Ultraspherical.sturmRealPolynomialLp lam hlam p = (y : Hr lam) :=
    Ultraspherical.sturmRealDomainRepresentative_spec lam hlam y
  have hTy : Ultraspherical.sturmRealPartialOperator lam hlam y =
      Ultraspherical.sturmRealPolynomialLp lam hlam (Ultraspherical.sturmPolynomial lam p) := rfl
  obtain ⟨a, b⟩ := q
  change (y : Hr lam) = a at hy1
  change Ultraspherical.sturmRealPartialOperator lam hlam y = b at hy2
  have ha' : a = Ultraspherical.sturmRealPolynomialLp lam hlam p := by rw [hp, hy1]
  have hb' : b = Ultraspherical.sturmRealPolynomialLp lam hlam
      (Ultraspherical.sturmPolynomial lam p) := by rw [← hy2, hTy]
  have hfst : (graphMap lam alpha hlam ha (a, b)).1 =
      GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha
        (polyLp lam hlam (p.map Complex.ofRealHom)) := by
    change GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha (cxL lam a) = _
    rw [ha', cxL_polynomial]
  have hsnd : (graphMap lam alpha hlam ha (a, b)).2 =
      GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha
        (polyLp lam hlam (gegenDiff lam (p.map Complex.ofRealHom))) := by
    change -GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha (cxL lam b) = _
    rw [hb', cxL_polynomial, gegenDiff_map, polyLp_neg, map_neg]
  have hpair : graphMap lam alpha hlam ha (a, b) =
      (GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha
        (polyLp lam hlam (p.map Complex.ofRealHom)),
       GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha
        (polyLp lam hlam (gegenDiff lam (p.map Complex.ofRealHom)))) :=
    Prod.ext hfst hsnd
  rw [hpair, mem_graph_iff]
  funext z
  exact (intertwining lam alpha hlam ha (p.map Complex.ofRealHom) z).symm

/-- Graph-core extension: the whole closed Sturm graph is mapped into `graph 𝒟_λ^max`. -/
theorem graphMap_closed_graph (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (q : Hr lam × Hr lam) (hq : q ∈ (sturmClosed lam hlam).graph) :
    graphMap lam alpha hlam ha q ∈ (fockDiffMax lam alpha ha).graph := by
  have hclosedD := theorem_7_3_closed lam alpha ha
  unfold LinearPMap.IsClosed at hclosedD
  have hpre : IsClosed (graphMap lam alpha hlam ha ⁻¹'
      ((fockDiffMax lam alpha ha).graph : Set (Fock alpha × Fock alpha))) :=
    hclosedD.preimage (graphMap_continuous lam alpha hlam ha)
  have hsub : ((Ultraspherical.sturmRealPartialOperator lam hlam).graph :
      Set (Hr lam × Hr lam)) ⊆ graphMap lam alpha hlam ha ⁻¹'
        ((fockDiffMax lam alpha ha).graph : Set (Fock alpha × Fock alpha)) :=
    fun q hq => graphMap_polynomial_graph lam alpha hlam ha q hq
  have hcl := closure_minimal hsub hpre
  have hq' : q ∈ closure ((Ultraspherical.sturmRealPartialOperator lam hlam).graph :
      Set (Hr lam × Hr lam)) := by
    rw [← Submodule.topologicalClosure_coe,
      ← Ultraspherical.sturmRealPartialOperator_closed_graph_eq lam hlam]
    exact hq
  exact hcl hq'

/-! ## Theorem 7.3, graph-domain intertwining -/

/-- Graph form of Eq. (7.7): for `f = u + i v ∈ Dom(D_λ)` (`u, v ∈ Dom A`),
`(C f, C D_λ f) ∈ graph 𝒟_λ^max`, where `D_λ f = -(A u + i A v)`. -/
theorem intertwining_graph (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (u v : (sturmClosed lam hlam).domain) :
    (GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha
        (cxL lam u + Complex.I • cxL lam v),
      GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha
        (-(cxL lam (sturmClosed lam hlam u) + Complex.I • cxL lam (sturmClosed lam hlam v)))) ∈
      (fockDiffMax lam alpha ha).graph := by
  set Cm := GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha
  have hu := graphMap_closed_graph lam alpha hlam ha ((u : Hr lam), sturmClosed lam hlam u)
    ((sturmClosed lam hlam).mem_graph u)
  have hv := graphMap_closed_graph lam alpha hlam ha ((v : Hr lam), sturmClosed lam hlam v)
    ((sturmClosed lam hlam).mem_graph v)
  have hsum := (fockDiffMax lam alpha ha).graph.add_mem hu
    ((fockDiffMax lam alpha ha).graph.smul_mem Complex.I hv)
  have heq : graphMap lam alpha hlam ha ((u : Hr lam), sturmClosed lam hlam u) +
      Complex.I • graphMap lam alpha hlam ha ((v : Hr lam), sturmClosed lam hlam v) =
      (Cm (cxL lam u + Complex.I • cxL lam v),
        Cm (-(cxL lam (sturmClosed lam hlam u) +
          Complex.I • cxL lam (sturmClosed lam hlam v)))) := by
    apply Prod.ext
    · change Cm (cxL lam u) + Complex.I • Cm (cxL lam v) =
        Cm (cxL lam u + Complex.I • cxL lam v)
      rw [map_add, map_smul]
    · change -Cm (cxL lam (sturmClosed lam hlam u)) +
          Complex.I • -Cm (cxL lam (sturmClosed lam hlam v)) =
        Cm (-(cxL lam (sturmClosed lam hlam u) + Complex.I • cxL lam (sturmClosed lam hlam v)))
      rw [map_neg, map_add, map_smul, smul_neg, neg_add]
  rw [← heq]
  exact hsum

/-- **Theorem 7.3 (graph-domain intertwining, Eq. (7.7)).** For every `f ∈ Dom(D_λ)`,
written `f = u + i v` with `u, v ∈ Dom A` (`A = -D_λ` the library's closed real operator),
`C f ∈ Dom(𝒟_λ^max)` and `𝒟_λ^max C f = C D_λ f` with `D_λ f = -(A u + i A v)`. -/
theorem theorem_7_3_intertwining (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (u v : (sturmClosed lam hlam).domain) :
    ∃ h : GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha
        (cxL lam u + Complex.I • cxL lam v) ∈ (fockDiffMax lam alpha ha).domain,
      fockDiffMax lam alpha ha ⟨_, h⟩ =
        GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha
          (-(cxL lam (sturmClosed lam hlam u) +
            Complex.I • cxL lam (sturmClosed lam hlam v))) := by
  have hg := intertwining_graph lam alpha hlam ha u v
  rw [mem_graph_iff] at hg
  refine ⟨⟨_, hg⟩, ?_⟩
  apply rep_injective alpha
  rw [fockDiffMax_apply]
  exact hg.symm

/-! ## Corollary 7.4 -/

/-- The normalized real Gegenbauer polynomial `P_n^{(λ)} ∈ L²(ν_λ;ℝ)` of the library. -/
abbrev gegenReal (lam : ℝ) (hlam : 0 < lam) (n : ℕ) : Hr lam :=
  Ultraspherical.sturmMonicEigenCandidate_realL2_normalized lam hlam n

/-- `P_n^{(λ)}` as a vector of `H_λ = L²(ν_λ;ℂ)`. -/
def gegenP (lam : ℝ) (hlam : 0 < lam) (n : ℕ) : Hc lam := cxL lam (gegenReal lam hlam n)

/-- `F_n = C_{λ,α} P_n^{(λ)}`. -/
def fockF (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (n : ℕ) : Fock alpha :=
  GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha (gegenP lam hlam n)

/-- `P_n ∈ Dom A` with `A P_n = -n(n+2λ) P_n` (library eigenmodes, normalized). -/
theorem gegenReal_eigen (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    ∃ y : (sturmClosed lam hlam).domain, (y : Hr lam) = gegenReal lam hlam n ∧
      sturmClosed lam hlam y = Ultraspherical.sturmEigenvalue lam n • (y : Hr lam) := by
  obtain ⟨x, hx, hAx⟩ := Ultraspherical.sturmMonicEigenCandidate_closed_domain_eigen lam hlam n
  refine ⟨(‖(x : Hr lam)‖)⁻¹ • x, ?_, ?_⟩
  · change (‖(x : Hr lam)‖)⁻¹ • (x : Hr lam) =
      (‖Ultraspherical.sturmRealPolynomialLp lam hlam
        (Ultraspherical.sturmMonicEigenCandidate lam n)‖)⁻¹ •
        Ultraspherical.sturmRealPolynomialLp lam hlam
          (Ultraspherical.sturmMonicEigenCandidate lam n)
    rw [hx]
  · rw [LinearPMap.map_smul, hAx, Submodule.coe_smul, smul_comm]

/-- `D_λ P_n = n(n+2λ) P_n` in `H_λ`, in the complexified form used by Theorem 7.3. -/
theorem gegenP_eigen_image (lam : ℝ) (hlam : 0 < lam) (n : ℕ)
    (y : (sturmClosed lam hlam).domain)
    (hAy : sturmClosed lam hlam y = Ultraspherical.sturmEigenvalue lam n • (y : Hr lam))
    (hy : (y : Hr lam) = gegenReal lam hlam n) :
    -(cxL lam (sturmClosed lam hlam y) +
        Complex.I • cxL lam (sturmClosed lam hlam (0 : (sturmClosed lam hlam).domain))) =
      ((n : ℂ) * ((n : ℂ) + 2 * (lam : ℂ))) • gegenP lam hlam n := by
  rw [LinearPMap.map_zero, map_zero, smul_zero, add_zero, hAy, map_smul, hy,
    RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal]
  unfold Ultraspherical.sturmEigenvalue gegenP
  rw [← neg_smul]
  congr 1
  first
  | (push_cast; ring)
  | (push_cast; done)
  | (rw [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_natCast]; push_cast; ring)

theorem gegenP_decomp (lam : ℝ) (hlam : 0 < lam) (n : ℕ)
    (y : (sturmClosed lam hlam).domain) (hy : (y : Hr lam) = gegenReal lam hlam n) :
    cxL lam y + Complex.I • cxL lam ((0 : (sturmClosed lam hlam).domain) : Hr lam) =
      gegenP lam hlam n := by
  rw [Submodule.coe_zero, map_zero, smul_zero, add_zero, hy]
  rfl

/-- **Corollary 7.4 (eigenrelation).** `F_n ∈ Dom(𝒟_λ^max)` and
`𝒟_λ^max F_n = n(n+2λ) F_n`. -/
theorem corollary_7_4_eigen (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (n : ℕ) :
    ∃ h : fockF lam alpha hlam ha n ∈ (fockDiffMax lam alpha ha).domain,
      fockDiffMax lam alpha ha ⟨_, h⟩ =
        ((n : ℂ) * ((n : ℂ) + 2 * (lam : ℂ))) • fockF lam alpha hlam ha n := by
  obtain ⟨y, hy, hAy⟩ := gegenReal_eigen lam hlam n
  have hg := intertwining_graph lam alpha hlam ha y 0
  rw [gegenP_decomp lam hlam n y hy, gegenP_eigen_image lam hlam n y hAy hy, map_smul] at hg
  rw [mem_graph_iff] at hg
  refine ⟨⟨_, hg⟩, ?_⟩
  apply rep_injective alpha
  rw [fockDiffMax_apply]
  exact hg.symm

/-- **Corollary 7.4 (nonvanishing).** `F_n ≠ 0`, by injectivity of `C_{λ,α}`
(Proposition 6.6, library `C_intrinsicEntire_injective`). -/
theorem corollary_7_4_ne_zero (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (n : ℕ) :
    fockF lam alpha hlam ha n ≠ 0 := by
  intro h0
  have hP : gegenP lam hlam n = 0 := by
    apply GeneralUltrasphericalFock.C_intrinsicEntire_injective lam alpha hlam ha
    rw [map_zero]
    exact h0
  have he : gegenReal lam hlam n = 0 := by
    rw [← reL_cxL lam (gegenReal lam hlam n)]
    change reL lam (gegenP lam hlam n) = 0
    rw [hP, map_zero]
  have hn := Ultraspherical.sturmMonicEigenCandidate_realL2_normalized_norm lam hlam n
  change ‖gegenReal lam hlam n‖ = 1 at hn
  rw [he, norm_zero] at hn
  exact zero_ne_one hn

/-- Dense range of `C_{λ,α}` in the Fock space (from the library's Proposition 6.6). -/
theorem C_intrinsicEntire_denseRange (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    DenseRange (GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha) := by
  have hC : DenseRange (GeneralUltrasphericalFock.C lam alpha hlam ha) := by
    have h := GeneralUltrasphericalFock.C_dense_range_unconditional lam alpha hlam ha
    rw [← Submodule.dense_iff_topologicalClosure_eq_top, LinearMap.coe_range] at h
    exact h
  have hE : DenseRange (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha) :=
    (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).surjective.denseRange
  exact hE.comp hC (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).continuous

/-- **Corollary 7.4 (completeness).** The closed span of `{F_n : n ≥ 0}` is the Fock space. -/
theorem corollary_7_4_complete (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (Submodule.span ℂ (Set.range (fockF lam alpha hlam ha))).topologicalClosure = ⊤ := by
  set Cm := GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha
  set S := (Submodule.span ℂ (Set.range (fockF lam alpha hlam ha))).topologicalClosure
  have hS : IsClosed (S : Set (Fock alpha)) := Submodule.isClosed_topologicalClosure _
  -- real vectors: the set `{u | C (cx u) ∈ S}` is a closed real subspace containing every `P_n`
  let T : Submodule ℝ (Hr lam) :=
    { carrier := {u | Cm (cxL lam u) ∈ S}
      zero_mem' := by
        change Cm (cxL lam 0) ∈ S
        rw [map_zero, map_zero]
        exact S.zero_mem
      add_mem' := by
        intro a b ha' hb'
        change Cm (cxL lam (a + b)) ∈ S
        rw [map_add, map_add]
        exact S.add_mem ha' hb'
      smul_mem' := by
        intro r a ha'
        change Cm (cxL lam (r • a)) ∈ S
        rw [map_smul, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
        exact S.smul_mem _ ha' }
  have hTclosed : IsClosed (T : Set (Hr lam)) :=
    hS.preimage (Cm.continuous.comp (cxL lam).continuous)
  have hspan : Submodule.span ℝ (Set.range (gegenReal lam hlam)) ≤ T := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    change fockF lam alpha hlam ha n ∈ S
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self n))
  have hdense : (Submodule.span ℝ (Set.range (gegenReal lam hlam))).topologicalClosure = ⊤ := by
    have h := (Ultraspherical.sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).dense_span
    rw [Ultraspherical.sturmMonicEigenCandidate_realL2_hilbertBasis,
      HilbertBasis.coe_mkOfOrthogonalEqBot] at h
    exact h
  have hT : ∀ u : Hr lam, Cm (cxL lam u) ∈ S := by
    intro u
    have hle : (Submodule.span ℝ (Set.range (gegenReal lam hlam))).topologicalClosure ≤ T :=
      Submodule.topologicalClosure_minimal _ hspan hTclosed
    rw [hdense] at hle
    exact hle Submodule.mem_top
  -- complex vectors: `f = cx(Re f) + i cx(Im f)`
  have hrange : Set.range Cm ⊆ (S : Set (Fock alpha)) := by
    rintro _ ⟨f, rfl⟩
    rw [← cxL_re_add_im lam f, map_add, map_smul]
    exact S.add_mem (hT _) (S.smul_mem _ (hT _))
  have hall : closure (Set.range Cm) ⊆ (S : Set (Fock alpha)) := closure_minimal hrange hS
  rw [(C_intrinsicEntire_denseRange lam alpha hlam ha).closure_range] at hall
  exact Submodule.eq_top_iff'.mpr fun F => hall (Set.mem_univ F)

/-! ## Theorem 7.3, density -/

/-- **Theorem 7.3 (dense domain).** `Dom(𝒟_λ^max)` is dense in the Fock space. -/
theorem theorem_7_3_dense (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (fockDiffMax lam alpha ha).domain.topologicalClosure = ⊤ := by
  have hle : Submodule.span ℂ (Set.range (fockF lam alpha hlam ha)) ≤
      (fockDiffMax lam alpha ha).domain := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    obtain ⟨h, _⟩ := corollary_7_4_eigen lam alpha hlam ha n
    exact h
  have hmono := Submodule.topologicalClosure_mono hle
  rw [corollary_7_4_complete lam alpha hlam ha] at hmono
  exact top_unique hmono

#print axioms GegenbauerFock.Section7Closed.theorem_7_3_closed
#print axioms GegenbauerFock.Section7Closed.theorem_7_3_dense
#print axioms GegenbauerFock.Section7Closed.theorem_7_3_intertwining
#print axioms GegenbauerFock.Section7Closed.corollary_7_4_ne_zero
#print axioms GegenbauerFock.Section7Closed.corollary_7_4_eigen
#print axioms GegenbauerFock.Section7Closed.corollary_7_4_complete

end GegenbauerFock.Section7Closed
