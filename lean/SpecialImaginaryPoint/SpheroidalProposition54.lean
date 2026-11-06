import Mathlib
import SpecialImaginaryPoint.GramCommutationTheorem52
import GegenbauerFock.GramSpectralKernel
import GegenbauerFock.GramKernelSeries
import GegenbauerFock.UltrasphericalComplexWeierstrass
import GegenbauerFock.DualGramEigenbasisTrace

/-!
# Manuscript 14, Proposition 5.4 (simple spectrum and spheroidal diagonalisation)

This module proves, in Lean 4, the operator-theoretic content of Proposition 5.4 for the closed
operator `𝒜_c = D̄ - c² M_{u²}` of the Theorem 5.2 certificate (`Theorem52.AClosed c`) and the
Gram operator `S_{1/2,c}` (`Theorem52.S c hc`), for every `c > 0`:

* `Par_AClosed`, `Par_S`: the parity operator `Π f (u) = f(-u)` (`Par`, a linear isometry of
  `H = L²(ν_{1/2}; ℂ)`, `Par_Par`) preserves `Dom(𝒜_c)` and commutes with `𝒜_c` and with
  `S_{1/2,c}`;
* `eigen_simple_parity`: on each parity subspace the eigenvalues of `𝒜_c` are simple: two
  eigenvectors of the same eigenvalue and the same parity are proportional;
* `parity_eigen_S_eigen`: every eigenvector of `𝒜_c` of definite parity is an eigenvector of
  `S_{1/2,c}` with a strictly positive eigenvalue;
* `spheroidal_joint_eigenbasis`: `H` has a Hilbert basis `{ψ_i}` of common eigenvectors,
  `𝒜_c ψ_i = χ_i ψ_i`, `S_{1/2,c} ψ_i = σ_i ψ_i`, `σ_i > 0`, `Π ψ_i = ±ψ_i`, and
  `∑ σ_i = ₁F₁(1/2; 3/2; c)` (the certified Kummer value of the GegenbauerFock library).

Method.  Simplicity does not use the Legendre basis: for an eigenvector `f` the moments
`m_k = ⟪f, u^k⟫` satisfy `c² m_{k+2} ∈ span(m_0, …, m_{k+1})` (`eigen_mom_vanish`), because
`⟪𝒜_c f, q⟫ = ⟪f, 𝒜_c q⟫` on polynomials (`AClosed_inner_polyLp`) and `𝒜_c` raises the degree
by two with leading coefficient `-c²`; parity kills one of `m_0, m_1`, and the density of the
polynomials (`polyCore_dense`) gives injectivity of `f ↦ m_j`.  The Hilbert basis is built from
the compact symmetric `S_{1/2,c}` (Mathlib's compact spectral theorem): each nonzero eigenspace
of `S_{1/2,c}` is finite-dimensional, lies in `Dom(𝒜_c)` by Theorem 5.2, and splits into its
two parity parts, on which `𝒜_c` is symmetric and is diagonalised by the finite-dimensional
spectral theorem.

Not formalised here: the compactness of the resolvent of `𝒜_c` (the basis is obtained from the
compactness of `S_{1/2,c}` instead), the identification of `D̄` with the spectral realisation (9)
of the manuscript (as for Theorem 5.2), and the identification of the eigenvectors with the
angular spheroidal wave functions of DLMF §30, which has no Mathlib counterpart.
-/

noncomputable section

open MeasureTheory Polynomial Module End
open scoped InnerProductSpace ENNReal

namespace Manuscript14Gram.Prop54

open Manuscript14Gram.Theorem52


/-! ## The reflection `u ↦ -u` and the parity operator -/

theorem eud_neg (u : ℝ) :
    GegenbauerFock.Ultraspherical.eulerianUniformDensity (-u) =
      GegenbauerFock.Ultraspherical.eulerianUniformDensity u := by
  unfold GegenbauerFock.Ultraspherical.eulerianUniformDensity
  by_cases h : -1 < u ∧ u < 1
  · have h' : -1 < -u ∧ -u < 1 := ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [if_pos h, if_pos h']
  · have h' : ¬ (-1 < -u ∧ -u < 1) := by
      rintro ⟨h1, h2⟩
      exact h ⟨by linarith, by linarith⟩
    rw [if_neg h, if_neg h']

/-- `ν_{1/2}` is invariant under `u ↦ -u`. -/
theorem nu_neg : MeasurePreserving (Neg.neg : ℝ → ℝ) ν ν := by
  refine ⟨measurable_neg, ?_⟩
  ext s hs
  rw [Measure.map_apply measurable_neg hs]
  change GegenbauerFock.Ultraspherical.measure (1 / 2 : ℝ) _ =
    GegenbauerFock.Ultraspherical.measure (1 / 2 : ℝ) s
  rw [GegenbauerFock.Ultraspherical.measure_half_eq_uniformDensity,
    withDensity_apply _ (measurable_neg hs), withDensity_apply _ hs]
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
    measurableEmbedding_neg
    (fun u : ℝ => ENNReal.ofReal (GegenbauerFock.Ultraspherical.eulerianUniformDensity u)) s
  simp only [eud_neg] at h
  exact h

/-- The parity operator `Π f = f ∘ (-·)` as a linear isometry of `H`. -/
def ParL : H →ₗᵢ[ℂ] H := Lp.compMeasurePreservingₗᵢ ℂ (Neg.neg : ℝ → ℝ) nu_neg

/-- The parity operator `Π` as a bounded operator. -/
def Par : H →L[ℂ] H := ParL.toContinuousLinearMap

theorem Par_apply_ae (f : H) : (Par f : ℝ → ℂ) =ᵐ[ν] fun u => f (-u) := by
  change ((Lp.compMeasurePreserving (Neg.neg : ℝ → ℝ) nu_neg f : H) : ℝ → ℂ) =ᵐ[ν] _
  exact Lp.coeFn_compMeasurePreserving f nu_neg

theorem Par_inner (f g : H) : ⟪Par f, Par g⟫_ℂ = ⟪f, g⟫_ℂ :=
  ParL.inner_map_map f g

theorem Par_Par (f : H) : Par (Par f) = f := by
  apply Lp.ext
  have h2 : (fun u => (Par f : ℝ → ℂ) (-u)) =ᵐ[ν] fun u => f (-(-u)) :=
    nu_neg.quasiMeasurePreserving.ae_eq_comp (Par_apply_ae f)
  filter_upwards [Par_apply_ae (Par f), h2] with u hu1 hu2
  rw [hu1, hu2, neg_neg]

/-- The sign attached to a parity label: `true` ↦ `+1` (even), `false` ↦ `-1` (odd). -/
def sgn (e : Bool) : ℂ := if e then 1 else -1

theorem sgn_true : sgn true = 1 := rfl

theorem sgn_false : sgn false = -1 := rfl

theorem sgn_conj (e : Bool) : (starRingEnd ℂ) (sgn e) = sgn e := by
  cases e
  · rw [sgn_false, map_neg, map_one]
  · rw [sgn_true, map_one]

theorem sgn_mul_of_ne {e e' : Bool} (h : e ≠ e') : sgn e * sgn e' = -1 := by
  cases e <;> cases e'
  · exact absurd rfl h
  · rw [sgn_false, sgn_true]; ring
  · rw [sgn_true, sgn_false]; ring
  · exact absurd rfl h

/-! ## Parity on polynomials and on the operators -/

theorem Par_polyLp (p : ℂ[X]) : Par (polyLp p) = polyLp (p.comp (-X)) := by
  apply Lp.ext
  have h2 : (fun u => (polyLp p : ℝ → ℂ) (-u)) =ᵐ[ν] fun u => polyFun p (-u) :=
    nu_neg.quasiMeasurePreserving.ae_eq_comp (polyLp_ae_eq p)
  filter_upwards [Par_apply_ae (polyLp p), h2, polyLp_ae_eq (p.comp (-X))] with u h1 hu h3
  rw [h1, h3, hu]
  simp [polyFun, eval_comp]

theorem DPoly_comp_neg (p : ℂ[X]) : DPoly (p.comp (-X)) = (DPoly p).comp (-X) := by
  have h1 : derivative (p.comp (-X)) = -(derivative p).comp (-X) := by
    rw [derivative_comp]
    simp
  have h2 : derivative (derivative (p.comp (-X))) = (derivative (derivative p)).comp (-X) := by
    rw [h1, derivative_neg, derivative_comp]
    simp
  rw [DPoly_apply, DPoly_apply, h2, h1]
  simp only [neg_comp, sub_comp, mul_comp, one_comp, pow_comp, X_comp, C_comp]
  ring

/-- The graph of the polynomial Legendre operator is invariant under `Π × Π`. -/
theorem Par_DPMap_graph (x : H × H) (hx : x ∈ DPMap.graph) :
    (Par x.1, Par x.2) ∈ DPMap.graph := by
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff DPMap).mp hx
  obtain ⟨p, hp⟩ := LinearMap.mem_range.mp y.2
  have hyp : y = ⟨polyLp p, polyLp_mem p⟩ := Subtype.ext hp.symm
  subst hyp
  have hx1 : x.1 = polyLp p := hy1.symm
  have hx2 : x.2 = polyLp (DPoly p) := by rw [← hy2, DPMap_apply]
  refine (LinearPMap.mem_graph_iff DPMap).mpr ⟨⟨polyLp (p.comp (-X)), polyLp_mem _⟩, ?_, ?_⟩
  · show polyLp (p.comp (-X)) = Par x.1
    rw [hx1, Par_polyLp]
  · show DPMap ⟨polyLp (p.comp (-X)), polyLp_mem _⟩ = Par x.2
    rw [DPMap_apply, hx2, DPoly_comp_neg, Par_polyLp]

theorem DClosed_graph_eq :
    (DClosed.graph : Set (H × H)) = closure (DPMap.graph : Set (H × H)) := by
  show (DPMap.closure.graph : Set (H × H)) = _
  rw [← DPMap_isClosable.graph_closure_eq_closure_graph, Submodule.topologicalClosure_coe]

/-- `Π` preserves `Dom(D̄)` and commutes with `D̄`. -/
theorem Par_DClosed (f : H) (hf : f ∈ DClosed.domain) :
    ∃ hP : Par f ∈ DClosed.domain, DClosed ⟨Par f, hP⟩ = Par (DClosed ⟨f, hf⟩) := by
  let Φ : H × H →L[ℂ] H × H := Par.prodMap Par
  have hmaps : Set.MapsTo Φ (DPMap.graph : Set (H × H)) (DPMap.graph : Set (H × H)) := by
    intro x hx
    exact Par_DPMap_graph x hx
  have hmapsCl := hmaps.closure Φ.continuous
  have hgraph : (f, DClosed ⟨f, hf⟩) ∈ (DClosed.graph : Set (H × H)) :=
    LinearPMap.mem_graph DClosed ⟨f, hf⟩
  rw [DClosed_graph_eq] at hgraph
  have h1 : Φ (f, DClosed ⟨f, hf⟩) ∈ (DClosed.graph : Set (H × H)) := by
    rw [DClosed_graph_eq]
    exact hmapsCl hgraph
  have h1' : (Par f, Par (DClosed ⟨f, hf⟩)) ∈ DClosed.graph := h1
  obtain ⟨⟨y, hyD⟩, hy1, hy2⟩ := (LinearPMap.mem_graph_iff DClosed).mp h1'
  have hy1' : y = Par f := hy1
  subst hy1'
  exact ⟨hyD, hy2⟩

theorem Par_M (f : H) : Par (M f) = M (Par f) := by
  apply Lp.ext
  have h2 : (fun u => (M f : ℝ → ℂ) (-u)) =ᵐ[ν] fun u => (((-u) ^ 2 : ℝ) : ℂ) * f (-u) :=
    nu_neg.quasiMeasurePreserving.ae_eq_comp (M_apply_ae f)
  filter_upwards [Par_apply_ae (M f), h2, M_apply_ae (Par f), Par_apply_ae f]
    with u h1 hu h3 h4
  rw [h1, h3, h4, hu, neg_sq]

/-- **Proposition 5.4, parity and `𝒜_c`:** `Π` preserves `Dom(𝒜_c)` and commutes with `𝒜_c`. -/
theorem Par_AClosed (c : ℝ) (x : (AClosed c).domain) :
    ∃ hP : Par x ∈ (AClosed c).domain, AClosed c ⟨Par x, hP⟩ = Par (AClosed c x) := by
  obtain ⟨hP, hD⟩ := Par_DClosed x x.2
  refine ⟨hP, ?_⟩
  have e1 : AClosed c ⟨Par x, hP⟩ = DClosed ⟨Par x, hP⟩ - ((c : ℂ) ^ 2) • M (Par x) := rfl
  have e2 : AClosed c x = DClosed ⟨x, x.2⟩ - ((c : ℂ) ^ 2) • M x := rfl
  rw [e1, e2, hD, map_sub, map_smul, Par_M]

theorem integral_nu_neg (g : ℝ → ℂ) : ∫ v, g (-v) ∂ν = ∫ v, g v ∂ν := by
  rw [integral_nu, integral_nu, intervalIntegral.integral_comp_neg g]
  norm_num

theorem SFun_Par (c : ℝ) (f : H) (u : ℝ) :
    SFun c (Par f : ℝ → ℂ) u = SFun c (f : ℝ → ℂ) (-u) := by
  unfold SFun
  calc ∫ v, (Real.exp (c * u * v) : ℂ) * (Par f : ℝ → ℂ) v ∂ν
      = ∫ v, (Real.exp (c * u * v) : ℂ) * f (-v) ∂ν := by
        apply integral_congr_ae
        filter_upwards [Par_apply_ae f] with v hv
        rw [hv]
    _ = ∫ v, (Real.exp (c * (-u) * (-v)) : ℂ) * f (-v) ∂ν := by
        congr 1
        funext v
        rw [show c * (-u) * (-v) = c * u * v by ring]
    _ = ∫ v, (Real.exp (c * (-u) * v) : ℂ) * f v ∂ν :=
        integral_nu_neg (fun v => (Real.exp (c * (-u) * v) : ℂ) * f v)

/-- **Proposition 5.4, parity and `S_{1/2,c}`:** `Π S = S Π`. -/
theorem Par_S (c : ℝ) (hc : 0 < c) (f : H) : Par (S c hc f) = S c hc (Par f) := by
  apply Lp.ext
  have h2 : (fun u => (S c hc f : ℝ → ℂ) (-u)) =ᵐ[ν] fun u => SFun c (f : ℝ → ℂ) (-u) :=
    nu_neg.quasiMeasurePreserving.ae_eq_comp (S_apply_ae c hc f)
  filter_upwards [Par_apply_ae (S c hc f), h2, S_apply_ae c hc (Par f)] with u h1 hu h3
  rw [h1, h3, SFun_Par]
  exact hu

/-! ## Symmetry of `D̄` and `𝒜_c` -/

theorem DClosed_le_adjoint : DClosed ≤ DPMap.adjoint := by
  have hdense := DPMap_domain_dense
  have hle : DPMap ≤ DPMap.adjoint := DPMap_formalSymmetric.le_adjoint hdense
  have hclosed : DPMap.adjoint.IsClosed := LinearPMap.adjoint_isClosed hdense
  refine LinearPMap.le_of_le_graph ?_
  show DPMap.closure.graph ≤ _
  rw [← DPMap_isClosable.graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le hle) hclosed

theorem DClosed_inner_core (f : DClosed.domain) (p : DPMap.domain) :
    ⟪DClosed f, (p : H)⟫_ℂ = ⟪(f : H), DPMap p⟫_ℂ := by
  have h := DClosed_le_adjoint
  have hf : (f : H) ∈ DPMap.adjoint.domain := h.1 f.2
  have heq : DClosed f = DPMap.adjoint ⟨f, hf⟩ := h.2 (x := f) (y := ⟨f, hf⟩) rfl
  rw [heq]
  exact LinearPMap.adjoint_isFormalAdjoint DPMap_domain_dense ⟨f, hf⟩ p

/-- `D̄` is symmetric on its domain. -/
theorem DClosed_symm (f g : DClosed.domain) :
    ⟪DClosed f, (g : H)⟫_ℂ = ⟪(f : H), DClosed g⟫_ℂ := by
  let G : Set (H × H) := {z | ⟪DClosed f, z.1⟫_ℂ = ⟪(f : H), z.2⟫_ℂ}
  have hGc : IsClosed G :=
    isClosed_eq (continuous_const.inner continuous_fst) (continuous_const.inner continuous_snd)
  have hsub : (DPMap.graph : Set (H × H)) ⊆ G := by
    rintro ⟨a, b⟩ hab
    obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff DPMap).mp hab
    show ⟪DClosed f, a⟫_ℂ = ⟪(f : H), b⟫_ℂ
    have ha : (y : H) = a := hy1
    have hb : DPMap y = b := hy2
    rw [← ha, ← hb]
    exact DClosed_inner_core f y
  have hcl : (DClosed.graph : Set (H × H)) ⊆ G := by
    rw [DClosed_graph_eq]
    exact closure_minimal hsub hGc
  exact hcl (LinearPMap.mem_graph DClosed g)

theorem M_symm (f g : H) : ⟪M f, g⟫_ℂ = ⟪f, M g⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [M_apply_ae f, M_apply_ae g] with u hf hg
  rw [hf, hg, RCLike.inner_apply', RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

/-- `𝒜_c` is symmetric on its domain. -/
theorem AClosed_symm (c : ℝ) (f g : (AClosed c).domain) :
    ⟪AClosed c f, (g : H)⟫_ℂ = ⟪(f : H), AClosed c g⟫_ℂ := by
  rw [AClosed_apply c f, AClosed_apply c g, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, DClosed_symm f g, M_symm]
  have hc2 : (starRingEnd ℂ) ((c : ℂ) ^ 2) = (c : ℂ) ^ 2 := by
    rw [map_pow, Complex.conj_ofReal]
  rw [hc2] <;> rfl

theorem AClosed_inner_polyLp (c : ℝ) (f : (AClosed c).domain) (q : ℂ[X]) :
    ⟪AClosed c f, polyLp q⟫_ℂ = ⟪(f : H), polyLp (APoly c q)⟫_ℂ := by
  have hq : polyLp q ∈ DClosed.domain := DPMap_le_DClosed.1 (polyLp_mem q)
  have h := AClosed_symm c f ⟨polyLp q, hq⟩
  rw [AClosed_polyLp c q hq] at h
  exact h

/-! ## Moments, and simplicity on the parity subspaces -/

/-- The moments `m_k(f) = ⟪f, u^k⟫`. -/
def mom (f : H) (k : ℕ) : ℂ := ⟪f, polyLp (X ^ k)⟫_ℂ

theorem inner_polyLp_eq_sum (f : H) (p : ℂ[X]) :
    ⟪f, polyLp p⟫_ℂ = ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * mom f j := by
  change ⟪f, polyLinear p⟫_ℂ = _
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
  rw [map_sum, inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← smul_eq_C_mul, map_smul, inner_smul_right]
  rfl

theorem mom_smul (a : ℂ) (f : H) (k : ℕ) : mom (a • f) k = (starRingEnd ℂ) a * mom f k := by
  unfold mom
  rw [inner_smul_left]

theorem mom_sub (f g : H) (k : ℕ) : mom (f - g) k = mom f k - mom g k := by
  unfold mom
  rw [inner_sub_left]

/-- For an eigenvector of `𝒜_c`, `m_0 = m_1 = 0` forces all moments to vanish
(`c² m_{k+2}` is a combination of `m_0, …, m_{k+1}`). -/
theorem eigen_mom_vanish (c : ℝ) (hc : 0 < c) (χ : ℂ) (f : (AClosed c).domain)
    (hf : AClosed c f = χ • (f : H)) (h0 : mom f 0 = 0) (h1 : mom f 1 = 0) :
    ∀ k, mom f k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · exact h0
    · exact h1
    · have key : mom f (k + 2) = 0 := by
        have hrel := AClosed_inner_polyLp c f (X ^ k)
        rw [hf, inner_smul_left, polyLp_APoly] at hrel
        have hk : mom f k = 0 := ih k (by omega)
        have hD : ⟪(f : H), polyLp (DPoly (X ^ k))⟫_ℂ = 0 := by
          rw [inner_polyLp_eq_sum]
          apply Finset.sum_eq_zero
          intro j hj
          have hdeg : (DPoly (X ^ k)).natDegree ≤ k :=
            (natDegree_DPoly_le _).trans (natDegree_X_pow k).le
          have hjr := Finset.mem_range.mp hj
          rw [ih j (by omega), mul_zero]
        have hX : (X : ℂ[X]) ^ 2 * X ^ k = X ^ (k + 2) := by ring
        rw [inner_sub_right, inner_smul_right, hD, hX] at hrel
        change (starRingEnd ℂ) χ * mom f k = 0 - (c : ℂ) ^ 2 * mom f (k + 2) at hrel
        rw [hk, mul_zero, zero_sub, zero_eq_neg] at hrel
        have hc2 : (c : ℂ) ^ 2 ≠ 0 := by
          have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
          exact pow_ne_zero 2 this
        exact (mul_eq_zero.mp hrel).resolve_left hc2
      exact key

/-- An eigenvector of `𝒜_c` with `m_0 = m_1 = 0` is zero (density of the polynomials). -/
theorem eigen_zero_of_mom (c : ℝ) (hc : 0 < c) (χ : ℂ) (f : (AClosed c).domain)
    (hf : AClosed c f = χ • (f : H)) (h0 : mom f 0 = 0) (h1 : mom f 1 = 0) :
    (f : H) = 0 := by
  have hall := eigen_mom_vanish c hc χ f hf h0 h1
  apply Dense.eq_zero_of_inner_left (𝕜 := ℂ) polyCore_dense
  intro v hv
  obtain ⟨p, rfl⟩ := LinearMap.mem_range.mp hv
  change ⟪(f : H), polyLp p⟫_ℂ = 0
  rw [inner_polyLp_eq_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [hall j, mul_zero]

theorem mom_parity (f : H) (e : Bool) (hf : Par f = sgn e • f) (k : ℕ) :
    mom f k = sgn e * (-1) ^ k * mom f k := by
  have h := Par_inner f (polyLp (X ^ k))
  have hcomp : (X ^ k : ℂ[X]).comp (-X) = ((-1 : ℂ) ^ k) • X ^ k := by
    rw [X_pow_comp, neg_pow (X : ℂ[X]) k, smul_eq_C_mul, C_pow, C_neg, C_1]
  rw [hf, Par_polyLp, hcomp, polyLp_smul, inner_smul_left, inner_smul_right, sgn_conj] at h
  unfold mom
  rw [mul_assoc]
  exact h.symm

/-- An odd vector has `m_0 = 0`. -/
theorem mom0_vanish_odd (f : H) (hf : Par f = sgn false • f) : mom f 0 = 0 := by
  have h := mom_parity f false hf 0
  rw [sgn_false, pow_zero, mul_one] at h
  linear_combination h / 2

/-- An even vector has `m_1 = 0`. -/
theorem mom1_vanish_even (f : H) (hf : Par f = sgn true • f) : mom f 1 = 0 := by
  have h := mom_parity f true hf 1
  rw [sgn_true, pow_one, one_mul] at h
  linear_combination h / 2

/-- The moment that parity does not kill: `m_0` for even, `m_1` for odd vectors. -/
def jdx (e : Bool) : ℕ := if e then 0 else 1

theorem eigen_zero_of_parity (c : ℝ) (hc : 0 < c) (χ : ℂ) (e : Bool)
    (x : (AClosed c).domain) (hx : AClosed c x = χ • (x : H))
    (hxe : Par x = sgn e • (x : H)) (hxj : mom x (jdx e) = 0) : (x : H) = 0 := by
  cases e
  · exact eigen_zero_of_mom c hc χ x hx (mom0_vanish_odd x hxe) hxj
  · exact eigen_zero_of_mom c hc χ x hx hxj (mom1_vanish_even x hxe)

theorem combo_eigen (c : ℝ) (χ : ℂ) (e : Bool) (f g : (AClosed c).domain)
    (hf : AClosed c f = χ • (f : H)) (hg : AClosed c g = χ • (g : H))
    (hfe : Par f = sgn e • (f : H)) (hge : Par g = sgn e • (g : H)) (α β : ℂ) :
    AClosed c (β • f - α • g) = χ • ((β • f - α • g : (AClosed c).domain) : H) ∧
      Par ((β • f - α • g : (AClosed c).domain) : H) =
        sgn e • ((β • f - α • g : (AClosed c).domain) : H) := by
  constructor
  · rw [LinearPMap.map_sub, LinearPMap.map_smul, LinearPMap.map_smul, hf, hg,
      Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul, smul_sub,
      smul_comm χ β (f : H), smul_comm χ α (g : H)]
  · rw [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul, map_sub, map_smul, map_smul,
      hfe, hge, smul_sub, smul_comm (sgn e) β (f : H), smul_comm (sgn e) α (g : H)]

/-- **Proposition 5.4, simplicity:** two eigenvectors of `𝒜_c` with the same eigenvalue and the
same parity are proportional. -/
theorem eigen_simple_parity (c : ℝ) (hc : 0 < c) (χ : ℂ) (e : Bool)
    (f g : (AClosed c).domain)
    (hf : AClosed c f = χ • (f : H)) (hg : AClosed c g = χ • (g : H))
    (hfe : Par f = sgn e • (f : H)) (hge : Par g = sgn e • (g : H)) (hf0 : (f : H) ≠ 0) :
    ∃ t : ℂ, (g : H) = t • (f : H) := by
  have ha0 : mom (f : H) (jdx e) ≠ 0 := fun h => hf0 (eigen_zero_of_parity c hc χ e f hf hfe h)
  obtain ⟨hw, hwe⟩ := combo_eigen c χ e f g hf hg hfe hge
    ((starRingEnd ℂ) (mom (f : H) (jdx e))) ((starRingEnd ℂ) (mom (g : H) (jdx e)))
  have hwj : mom (((starRingEnd ℂ) (mom (g : H) (jdx e)) • f -
      (starRingEnd ℂ) (mom (f : H) (jdx e)) • g : (AClosed c).domain) : H) (jdx e) = 0 := by
    rw [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul, mom_sub, mom_smul, mom_smul,
      Complex.conj_conj, Complex.conj_conj]
    ring
  have h0 := eigen_zero_of_parity c hc χ e _ hw hwe hwj
  rw [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul, sub_eq_zero] at h0
  refine ⟨(starRingEnd ℂ) (mom (g : H) (jdx e)) / (starRingEnd ℂ) (mom (f : H) (jdx e)), ?_⟩
  have ha0' : (starRingEnd ℂ) (mom (f : H) (jdx e)) ≠ 0 :=
    (_root_.map_ne_zero (starRingEnd ℂ)).mpr ha0
  rw [div_eq_mul_inv, mul_comm, ← smul_smul, h0, smul_smul, inv_mul_cancel₀ ha0', one_smul]

/-! ## Eigenvectors of definite parity are eigenvectors of `S_{1/2,c}` -/

theorem S_injective (c : ℝ) (hc : 0 < c) : Function.Injective (S c hc) := by
  intro f g hfg
  have h : S c hc (f - g) = 0 := by rw [map_sub, hfg, sub_self]
  have hC := (GegenbauerFock.GeneralUltrasphericalFock.gram_apply_eq_zero_iff_C_eq_zero
    (1 / 2) (1 / (4 * c)) hhalf (by positivity) (f - g)).mp h
  have h2 := GegenbauerFock.GeneralUltrasphericalFock.C_injective (1 / 2) (1 / (4 * c)) hhalf
    (by positivity) (hC.trans (map_zero _).symm)
  exact sub_eq_zero.mp h2

theorem S_symm (c : ℝ) (hc : 0 < c) (x y : H) : ⟪S c hc x, y⟫_ℂ = ⟪x, S c hc y⟫_ℂ := by
  have h3 : (S c hc).adjoint = S c hc :=
    GegenbauerFock.GeneralUltrasphericalFock.gram_selfadjoint (1 / 2) (1 / (4 * c)) hhalf
      (by positivity)
  have h2 := ContinuousLinearMap.adjoint_inner_right (S c hc) x y
  rw [h3] at h2
  exact h2.symm

/-- **Proposition 5.4, joint eigenvectors:** an eigenvector of `𝒜_c` of definite parity is an
eigenvector of `S_{1/2,c}` with a strictly positive eigenvalue. -/
theorem parity_eigen_S_eigen (c : ℝ) (hc : 0 < c) (χ : ℂ) (e : Bool)
    (x : (AClosed c).domain) (hx : AClosed c x = χ • (x : H))
    (hxe : Par x = sgn e • (x : H)) (hx0 : (x : H) ≠ 0) :
    ∃ σ : ℝ, 0 < σ ∧ S c hc x = (σ : ℂ) • (x : H) := by
  have hy : AClosed c ⟨S c hc x, S_range_subset_domain c hc x⟩ = χ • S c hc x := by
    rw [gram_commutes_with_perturbed_legendre c hc x, hx, map_smul]
  have hye : Par (S c hc x) = sgn e • S c hc x := by
    rw [Par_S, hxe, map_smul]
  obtain ⟨t, ht⟩ := eigen_simple_parity c hc χ e x ⟨S c hc x, S_range_subset_domain c hc x⟩
    hx hy hxe hye hx0
  have ht' : S c hc x = t • (x : H) := ht
  have hn : ⟪(x : H), (x : H)⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hx0
  have h1 : ⟪(x : H), S c hc x⟫_ℂ = t * ⟪(x : H), (x : H)⟫_ℂ := by
    rw [ht', inner_smul_right]
  have h2 : ⟪S c hc x, (x : H)⟫_ℂ = (starRingEnd ℂ) t * ⟪(x : H), (x : H)⟫_ℂ := by
    rw [ht', inner_smul_left]
  have hsym := S_symm c hc x x
  rw [h1, h2] at hsym
  have hconj : (starRingEnd ℂ) t = t := mul_right_cancel₀ hn hsym
  have hreal : ((t.re : ℝ) : ℂ) = t := Complex.conj_eq_iff_re.mp hconj
  have ht0 : t ≠ 0 := by
    intro h
    apply hx0
    apply S_injective c hc
    rw [ht', h, zero_smul, map_zero]
  have htre0 : t.re ≠ 0 := by
    intro h
    apply ht0
    rw [← hreal, h, Complex.ofReal_zero]
  have hpos := GegenbauerFock.GeneralUltrasphericalFock.gram_positive (1 / 2) (1 / (4 * c))
    hhalf (by positivity) x
  have hpos' : 0 ≤ RCLike.re ⟪S c hc x, (x : H)⟫_ℂ := hpos
  have hnn : (⟪(x : H), (x : H)⟫_ℂ).re = ‖(x : H)‖ ^ 2 := by
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) (x : H)
    rwa [RCLike.re_to_complex] at h
  rw [h2, hconj, RCLike.re_to_complex, ← hreal, Complex.re_ofReal_mul, hnn] at hpos'
  have hsq : 0 < ‖(x : H)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
  have htre : 0 ≤ t.re := by
    by_contra hneg
    have : t.re * ‖(x : H)‖ ^ 2 < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) hsq
    linarith
  refine ⟨t.re, lt_of_le_of_ne htre (Ne.symm htre0), ?_⟩
  rw [hreal]
  exact ht'

/-! ## The joint Hilbert eigenbasis -/

section Basis

variable (c : ℝ) (hc : 0 < c)

theorem S_isSymmetric : ((S c hc : H →L[ℂ] H) : H →ₗ[ℂ] H).IsSymmetric :=
  fun x y => S_symm c hc x y

theorem S_compact : IsCompactOperator (S c hc) :=
  GegenbauerFock.GeneralUltrasphericalFock.gram_compact_concrete (1 / 2) (1 / (4 * c)) hhalf
    (by positivity)

/-- The joint eigenspace of `S_{1/2,c}` (eigenvalue `μ`) and `Π` (sign `sgn e`). -/
def Fsp (μ : ℂ) (e : Bool) : Submodule ℂ H :=
  eigenspace (S c hc).toLinearMap μ ⊓ eigenspace (Par : H →L[ℂ] H).toLinearMap (sgn e)

theorem mem_Fsp {μ : ℂ} {e : Bool} {x : H} :
    x ∈ Fsp c hc μ e ↔ S c hc x = μ • x ∧ Par x = sgn e • x := by
  unfold Fsp
  rw [Submodule.mem_inf, mem_eigenspace_iff, mem_eigenspace_iff]
  rfl

theorem Fsp_le_domain (μ : ℂ) (e : Bool) : Fsp c hc μ e ≤ (AClosed c).domain := by
  intro x hx
  have hS := ((mem_Fsp c hc).mp hx).1
  by_cases hμ : μ = 0
  · rw [hμ, zero_smul] at hS
    have : x = 0 := S_injective c hc (hS.trans (map_zero _).symm)
    rw [this]
    exact Submodule.zero_mem _
  · have hx' : x = μ⁻¹ • S c hc x := by
      rw [hS, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (S_range_subset_domain c hc x)

theorem Fsp_A_mem (μ : ℂ) (e : Bool) (x : Fsp c hc μ e) :
    AClosed c (Submodule.inclusion (Fsp_le_domain c hc μ e) x) ∈ Fsp c hc μ e := by
  obtain ⟨hS, hP⟩ := (mem_Fsp c hc).mp x.2
  rw [mem_Fsp]
  constructor
  · have h := gram_commutes_with_perturbed_legendre c hc
      (Submodule.inclusion (Fsp_le_domain c hc μ e) x)
    have hyz : (⟨S c hc (Submodule.inclusion (Fsp_le_domain c hc μ e) x),
        S_range_subset_domain c hc (Submodule.inclusion (Fsp_le_domain c hc μ e) x)⟩ :
          (AClosed c).domain) = μ • Submodule.inclusion (Fsp_le_domain c hc μ e) x := by
      apply Subtype.ext
      exact hS
    rw [hyz, LinearPMap.map_smul] at h
    exact h.symm
  · obtain ⟨hPd, hPA⟩ := Par_AClosed c (Submodule.inclusion (Fsp_le_domain c hc μ e) x)
    have hpz : (⟨Par (Submodule.inclusion (Fsp_le_domain c hc μ e) x), hPd⟩ :
        (AClosed c).domain) = sgn e • Submodule.inclusion (Fsp_le_domain c hc μ e) x := by
      apply Subtype.ext
      exact hP
    rw [hpz, LinearPMap.map_smul] at hPA
    exact hPA.symm

theorem Fsp_fd (μ : ℂ) (e : Bool) : FiniteDimensional ℂ (Fsp c hc μ e) := by
  by_cases hμ : μ = 0
  · have hbot : Fsp c hc μ e = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hS := ((mem_Fsp c hc).mp hx).1
      rw [hμ, zero_smul] at hS
      rw [Submodule.mem_bot]
      exact S_injective c hc (hS.trans (map_zero _).symm)
    rw [hbot]
    infer_instance
  · have : FiniteDimensional ℂ (eigenspace (S c hc).toLinearMap μ) :=
      ContinuousLinearMap.finite_dimensional_eigenspace (S_compact c hc) μ hμ
    exact Submodule.finiteDimensional_of_le (S₂ := eigenspace (S c hc).toLinearMap μ) inf_le_left

instance instFdFsp (μ : ℂ) (e : Bool) : FiniteDimensional ℂ (Fsp c hc μ e) := Fsp_fd c hc μ e

/-- `𝒜_c` restricted to the joint eigenspace `Fsp μ e`. -/
def AF (μ : ℂ) (e : Bool) : Fsp c hc μ e →ₗ[ℂ] Fsp c hc μ e :=
  LinearMap.codRestrict (Fsp c hc μ e)
    ((AClosed c).toFun ∘ₗ Submodule.inclusion (Fsp_le_domain c hc μ e))
    (fun x => Fsp_A_mem c hc μ e x)

theorem AF_coe (μ : ℂ) (e : Bool) (x : Fsp c hc μ e) :
    ((AF c hc μ e x : Fsp c hc μ e) : H) =
      AClosed c (Submodule.inclusion (Fsp_le_domain c hc μ e) x) := rfl

theorem AF_symm (μ : ℂ) (e : Bool) : (AF c hc μ e).IsSymmetric := by
  intro x y
  rw [Submodule.coe_inner, Submodule.coe_inner, AF_coe, AF_coe]
  exact AClosed_symm c (Submodule.inclusion (Fsp_le_domain c hc μ e) x)
    (Submodule.inclusion (Fsp_le_domain c hc μ e) y)

/-- The orthonormal eigenbasis of `𝒜_c` on `Fsp μ e` (finite-dimensional spectral theorem). -/
def Bas (q : ℂ × Bool) :
    OrthonormalBasis (Fin (finrank ℂ (Fsp c hc q.1 q.2))) ℂ (Fsp c hc q.1 q.2) :=
  (AF_symm c hc q.1 q.2).eigenvectorBasis rfl

/-- The corresponding real eigenvalues of `𝒜_c`. -/
def eigA (q : ℂ × Bool) (i : Fin (finrank ℂ (Fsp c hc q.1 q.2))) : ℝ :=
  (AF_symm c hc q.1 q.2).eigenvalues rfl i

theorem AF_Bas (q : ℂ × Bool) (i : Fin (finrank ℂ (Fsp c hc q.1 q.2))) :
    AF c hc q.1 q.2 (Bas c hc q i) = (eigA c hc q i : ℂ) • Bas c hc q i :=
  (AF_symm c hc q.1 q.2).apply_eigenvectorBasis rfl i

/-- The index type of the joint basis. -/
abbrev JIdx : Type := Σ q : ℂ × Bool, Fin (finrank ℂ (Fsp c hc q.1 q.2))

/-- The joint eigenvectors, as vectors of `H`. -/
def vec (a : JIdx c hc) : H := (Fsp c hc a.1.1 a.1.2).subtypeₗᵢ (Bas c hc a.1 a.2)

theorem vec_coe (a : JIdx c hc) :
    vec c hc a = ((Bas c hc a.1 a.2 : Fsp c hc a.1.1 a.1.2) : H) := by
  rw [vec, Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype]

theorem vec_mem (a : JIdx c hc) : vec c hc a ∈ Fsp c hc a.1.1 a.1.2 := by
  rw [vec_coe]
  exact (Bas c hc a.1 a.2).2

theorem Fsp_orthogonal : OrthogonalFamily ℂ (fun q : ℂ × Bool => Fsp c hc q.1 q.2)
    (fun q => (Fsp c hc q.1 q.2).subtypeₗᵢ) := by
  intro q q' hqq' x y
  change ⟪(x : H), (y : H)⟫_ℂ = 0
  obtain ⟨hxS, hxP⟩ := (mem_Fsp c hc).mp x.2
  obtain ⟨hyS, hyP⟩ := (mem_Fsp c hc).mp y.2
  by_cases hμ : q.1 = q'.1
  · have he : q.2 ≠ q'.2 := by
      intro h
      exact hqq' (Prod.ext hμ h)
    have h := Par_inner (x : H) (y : H)
    rw [hxP, hyP, inner_smul_left, inner_smul_right, sgn_conj] at h
    have h' : sgn q.2 * (sgn q'.2 * ⟪(x : H), (y : H)⟫_ℂ) = -⟪(x : H), (y : H)⟫_ℂ := by
      rw [← mul_assoc, sgn_mul_of_ne he, neg_one_mul]
    rw [h'] at h
    linear_combination -h / 2
  · have hfam := (S_isSymmetric c hc).orthogonalFamily_eigenspaces
    have hx' : (x : H) ∈ eigenspace (S c hc).toLinearMap q.1 := mem_eigenspace_iff.mpr hxS
    have hy' : (y : H) ∈ eigenspace (S c hc).toLinearMap q'.1 := mem_eigenspace_iff.mpr hyS
    exact hfam hμ ⟨(x : H), hx'⟩ ⟨(y : H), hy'⟩

theorem vec_orthonormal : Orthonormal ℂ (vec c hc) :=
  (Fsp_orthogonal c hc).orthonormal_sigma_orthonormal (fun q => (Bas c hc q).orthonormal)

theorem Fsp_le_span (q : ℂ × Bool) :
    Fsp c hc q.1 q.2 ≤ Submodule.span ℂ (Set.range (vec c hc)) := by
  intro x hx
  have hsum := (Bas c hc q).sum_repr ⟨x, hx⟩
  have hx' : x = ∑ i, (Bas c hc q).repr ⟨x, hx⟩ i • ((Bas c hc q i : Fsp c hc q.1 q.2) : H) := by
    have := congrArg (fun z : Fsp c hc q.1 q.2 => (z : H)) hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  rw [hx']
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨⟨q, i⟩, vec_coe c hc ⟨q, i⟩⟩

theorem eigenspace_le_span (μ : ℂ) :
    eigenspace (S c hc).toLinearMap μ ≤ Submodule.span ℂ (Set.range (vec c hc)) := by
  intro x hx
  have hS : S c hc x = μ • x := mem_eigenspace_iff.mp hx
  have hSP : S c hc (Par x) = μ • Par x := by rw [← Par_S, hS, map_smul]
  have hxE : x ∈ eigenspace (S c hc).toLinearMap μ := hx
  have hPE : Par x ∈ eigenspace (S c hc).toLinearMap μ := mem_eigenspace_iff.mpr hSP
  have hx2 : x = (1 / 2 : ℂ) • (x + Par x) + (1 / 2 : ℂ) • (x - Par x) := by
    rw [← smul_add, show x + Par x + (x - Par x) = (2 : ℂ) • x by rw [two_smul]; abel,
      smul_smul]
    norm_num
  have hp : (1 / 2 : ℂ) • (x + Par x) ∈ Fsp c hc μ true := by
    refine (mem_Fsp c hc).mpr
      ⟨mem_eigenspace_iff.mp (Submodule.smul_mem _ _ (Submodule.add_mem _ hxE hPE)), ?_⟩
    rw [map_smul, map_add, Par_Par, sgn_true, one_smul, add_comm]
  have hm : (1 / 2 : ℂ) • (x - Par x) ∈ Fsp c hc μ false := by
    refine (mem_Fsp c hc).mpr
      ⟨mem_eigenspace_iff.mp (Submodule.smul_mem _ _ (Submodule.sub_mem _ hxE hPE)), ?_⟩
    rw [map_smul, map_sub, Par_Par, sgn_false, neg_one_smul, ← smul_neg, neg_sub]
  rw [hx2]
  exact Submodule.add_mem _ (Fsp_le_span c hc (μ, true) hp) (Fsp_le_span c hc (μ, false) hm)

theorem span_orthogonal_eq_bot :
    (Submodule.span ℂ (Set.range (vec c hc)))ᗮ = (⊥ : Submodule ℂ H) := by
  have hspec : (⨆ μ : ℂ, eigenspace (S c hc).toLinearMap μ)ᗮ = (⊥ : Submodule ℂ H) :=
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot (S_compact c hc)
      (S_isSymmetric c hc)
  have hi : (⨆ μ : ℂ, eigenspace (S c hc).toLinearMap μ) ≤
      (Submodule.span ℂ (Set.range (vec c hc))).topologicalClosure :=
    iSup_le fun μ => (eigenspace_le_span c hc μ).trans (Submodule.le_topologicalClosure _)
  have hle := Submodule.orthogonal_le hi
  rw [Submodule.orthogonal_closure, hspec] at hle
  exact eq_bot_iff.mpr hle

/-- The joint Hilbert basis. -/
def jointBasis : HilbertBasis (JIdx c hc) ℂ H :=
  HilbertBasis.mkOfOrthogonalEqBot (vec_orthonormal c hc) (span_orthogonal_eq_bot c hc)

theorem jointBasis_apply (a : JIdx c hc) : jointBasis c hc a = vec c hc a := by
  simp only [jointBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

theorem vec_ne_zero (a : JIdx c hc) : vec c hc a ≠ 0 := (vec_orthonormal c hc).ne_zero a

theorem vec_domain (a : JIdx c hc) : vec c hc a ∈ (AClosed c).domain :=
  Fsp_le_domain c hc a.1.1 a.1.2 (vec_mem c hc a)

theorem vec_A (a : JIdx c hc) :
    AClosed c ⟨vec c hc a, vec_domain c hc a⟩ = (eigA c hc a.1 a.2 : ℂ) • vec c hc a := by
  have h := congrArg (fun z : Fsp c hc a.1.1 a.1.2 => (z : H)) (AF_Bas c hc a.1 a.2)
  simp only [AF_coe, Submodule.coe_smul] at h
  have hv : (⟨vec c hc a, vec_domain c hc a⟩ : (AClosed c).domain) =
      Submodule.inclusion (Fsp_le_domain c hc a.1.1 a.1.2) (Bas c hc a.1 a.2) :=
    Subtype.ext (vec_coe c hc a)
  rw [hv, h, vec_coe]

theorem vec_Par (a : JIdx c hc) : Par (vec c hc a) = sgn a.1.2 • vec c hc a :=
  ((mem_Fsp c hc).mp (vec_mem c hc a)).2

end Basis

/-- **Proposition 5.4, joint eigenbasis and trace:** `H` has a Hilbert basis of common
eigenvectors of `𝒜_c`, `S_{1/2,c}` and `Π`, with real `𝒜_c`-eigenvalues `χ_i`, strictly
positive `S_{1/2,c}`-eigenvalues `σ_i`, and `∑ σ_i = ₁F₁(1/2; 3/2; c)` (`kummerSeries (1/2) c`). -/
theorem spheroidal_joint_eigenbasis (c : ℝ) (hc : 0 < c) :
    ∃ (κ : Type) (b : HilbertBasis κ ℂ H) (χ σ : κ → ℝ) (e : κ → Bool)
      (hdom : ∀ i, (b i : H) ∈ (AClosed c).domain),
      (∀ i, AClosed c ⟨b i, hdom i⟩ = (χ i : ℂ) • b i) ∧
      (∀ i, S c hc (b i) = (σ i : ℂ) • b i) ∧ (∀ i, 0 < σ i) ∧
      (∀ i, Par (b i) = sgn (e i) • b i) ∧
      HasSum σ (GegenbauerFock.KummerCoefficients.kummerSeries (1 / 2) c) := by
  have hdom : ∀ a, (jointBasis c hc a : H) ∈ (AClosed c).domain := by
    intro a
    rw [jointBasis_apply]
    exact vec_domain c hc a
  have hS : ∀ a, ∃ σ : ℝ, 0 < σ ∧
      S c hc (jointBasis c hc a) = (σ : ℂ) • jointBasis c hc a := by
    intro a
    obtain ⟨σ, hσ, hSσ⟩ := parity_eigen_S_eigen c hc (eigA c hc a.1 a.2 : ℂ) a.1.2
      ⟨vec c hc a, vec_domain c hc a⟩ (vec_A c hc a) (vec_Par c hc a) (vec_ne_zero c hc a)
    refine ⟨σ, hσ, ?_⟩
    rw [jointBasis_apply]
    exact hSσ
  choose σ hσpos hσ using hS
  refine ⟨JIdx c hc, jointBasis c hc, fun a => eigA c hc a.1 a.2, σ, fun a => a.1.2, hdom,
    ?_, hσ, hσpos, ?_, ?_⟩
  · intro a
    have hv : (⟨jointBasis c hc a, hdom a⟩ : (AClosed c).domain) =
        ⟨vec c hc a, vec_domain c hc a⟩ := Subtype.ext (jointBasis_apply c hc a)
    rw [hv, vec_A c hc a, jointBasis_apply]
  · intro a
    rw [jointBasis_apply]
    exact vec_Par c hc a
  · have heig : ∀ a, GegenbauerFock.GeneralUltrasphericalFock.gram (1 / 2) (1 / (4 * c)) hhalf
        (by positivity) (jointBasis c hc a) = (σ a : ℂ) • jointBasis c hc a := fun a => hσ a
    have hsum := GegenbauerFock.GeneralUltrasphericalFock.sourceGram_realEigenvalues_summable
      (1 / 2) (1 / (4 * c)) hhalf (by positivity) (jointBasis c hc) σ heig
    have htsum :=
      GegenbauerFock.GeneralUltrasphericalFock.sourceGram_realEigenvalues_tsum_eq_kummer
        (1 / 2) (1 / (4 * c)) hhalf (by positivity) (jointBasis c hc) σ heig
    have harg : (1 : ℝ) / (4 * (1 / (4 * c))) = c := by
      rw [mul_one_div, one_div_div, mul_div_cancel_left₀ c (by norm_num : (4 : ℝ) ≠ 0)]
    rw [harg] at htsum
    exact hsum.hasSum_iff.mpr htsum

#print axioms Manuscript14Gram.Prop54.Par_AClosed
#print axioms Manuscript14Gram.Prop54.Par_S
#print axioms Manuscript14Gram.Prop54.eigen_simple_parity
#print axioms Manuscript14Gram.Prop54.parity_eigen_S_eigen
#print axioms Manuscript14Gram.Prop54.spheroidal_joint_eigenbasis

end Manuscript14Gram.Prop54

end
