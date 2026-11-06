import Mathlib
import SpecialImaginaryPoint.SpheroidalProposition54
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2HilbertBasis
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicEigenPolynomial
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicDegree
import GegenbauerFock.UltrasphericalSturmLiouvilleRealPolynomialL2

/-!
# Manuscript 14: the spectral realisation (8)–(9) and the compact resolvent of `𝒜_c`

This module identifies the closed operator `D̄` of the Theorem 5.2 certificate (the graph closure of
the Legendre operator `D⁰ p = -[(1-u²)p']'` on the complex polynomials of `H = L²(ν_{1/2}; ℂ)`)
with the spectral realisation (8)–(9) of manuscript 14, and proves that `𝒜_c = D̄ - c² M_{u²}`
has compact resolvent, for every real `c`.

* `eB`: a Hilbert basis of `H` by polynomials (`eB_polynomial`): `eB n = q_n` with `deg q_n = n`,
  positive leading coefficient and `D⁰ q_n = n(n+1) q_n`; these properties characterise the
  orthonormal Gegenbauer basis `P_n^{(1/2)}` of the manuscript.  It is the complexification of the
  certified real Hilbert basis `sturmMonicEigenCandidate_realL2_hilbertBasis` of the GegenbauerFock
  library.
* `DClosed_domain_iff`, `DClosed_hasSum`: `f ∈ Dom(D̄)` iff `∑ n²(n+1)² |⟨P_n, f⟩|² < ∞`, and then
  `D̄ f = ∑ n(n+1) ⟨P_n, f⟩ P_n`: this is (8)–(9).
* `DClosed_isSelfAdjoint`: `D̄` is selfadjoint.
* `Rt_compact`, `DClosed_Rt`, `Rt_DClosed`: for `t > 0`, `(D̄ + t)⁻¹` is the compact diagonal
  operator with multipliers `(t + n(n+1))⁻¹`.
* `AClosed_compact_resolvent`: `(𝒜_c + (c²+1))⁻¹` exists as a compact bounded operator, a two-sided
  inverse on `Dom(𝒜_c)` (Neumann series for `c² M_{u²} (D̄ + c² + 1)⁻¹`, of norm `< 1`).
-/

noncomputable section

open MeasureTheory Polynomial Filter Topology
open scoped InnerProductSpace ENNReal

namespace Manuscript14Gram.Spectral

open Manuscript14Gram.Theorem52 Manuscript14Gram.Prop54

/-! ## Real and complex `L²` -/

/-- The real `L²` space of `ν = ν_{1/2}`. -/
abbrev HRe : Type := Lp ℝ 2 ν

/-- The real-linear embedding of real `L²` into complex `L²`. -/
def J : HRe →L[ℝ] H := Complex.ofRealCLM.compLpL 2 ν

/-- Real part. -/
def ReL : H →L[ℝ] HRe := Complex.reCLM.compLpL 2 ν

/-- Imaginary part. -/
def ImL : H →L[ℝ] HRe := Complex.imCLM.compLpL 2 ν

theorem J_ae (f : HRe) : (J f : ℝ → ℂ) =ᵐ[ν] fun u => ((f u : ℝ) : ℂ) :=
  ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := ν) Complex.ofRealCLM f

theorem ReL_ae (f : H) : (ReL f : ℝ → ℝ) =ᵐ[ν] fun u => (f u).re :=
  ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := ν) Complex.reCLM f

theorem ImL_ae (f : H) : (ImL f : ℝ → ℝ) =ᵐ[ν] fun u => (f u).im :=
  ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := ν) Complex.imCLM f

theorem J_inner (f g : HRe) : ⟪J f, J g⟫_ℂ = ((⟪f, g⟫_ℝ : ℝ) : ℂ) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [J_ae f, J_ae g] with u hf hg
  rw [hf, hg, RCLike.inner_apply', Complex.conj_ofReal, Real.inner_apply, Complex.ofReal_mul]

theorem decomp (f : H) : J (ReL f) + Complex.I • J (ImL f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (J (ReL f)) (Complex.I • J (ImL f)),
    Lp.coeFn_smul Complex.I (J (ImL f)), J_ae (ReL f), J_ae (ImL f), ReL_ae f, ImL_ae f]
    with u h1 h2 h3 h4 h5 h6
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, h5, h6, smul_eq_mul, mul_comm]
  exact Complex.re_add_im (f u)

/-! ## The Hilbert basis of Gegenbauer polynomials -/

/-- The certified real Hilbert basis of normalised monic Gegenbauer polynomials at `λ = 1/2`. -/
abbrev bR : HilbertBasis ℕ ℝ HRe :=
  GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_hilbertBasis (1 / 2) hhalf

/-- The monic Gegenbauer (Legendre) polynomial of degree `n`. -/
def G (n : ℕ) : ℝ[X] := GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate (1 / 2) n

/-- Its real `L²` class. -/
def PR (n : ℕ) : HRe := GegenbauerFock.Ultraspherical.sturmRealPolynomialLp (1 / 2) hhalf (G n)

theorem bR_apply (n : ℕ) : bR n = (‖PR n‖⁻¹) • PR n := by
  simp only [bR, GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_hilbertBasis,
    HilbertBasis.coe_mkOfOrthogonalEqBot]
  rfl

theorem bR_eq_zero {r : HRe} (h : ∀ n, ⟪bR n, r⟫_ℝ = 0) : r = 0 := by
  have hz : bR.repr r = 0 := by
    ext n
    simp [HilbertBasis.repr_apply_apply, h n]
  exact bR.repr.injective (hz.trans (map_zero _).symm)

/-- The complexified basis vectors. -/
def e (n : ℕ) : H := J (bR n)

theorem e_orthonormal : Orthonormal ℂ e := by
  classical
  rw [orthonormal_iff_ite]
  intro m n
  have h := orthonormal_iff_ite.mp bR.orthonormal m n
  show ⟪J (bR m), J (bR n)⟫_ℂ = _
  rw [J_inner, h]
  split_ifs <;> simp

theorem e_total : (Submodule.span ℂ (Set.range e))ᗮ = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  have hz : ∀ n, ⟪e n, f⟫_ℂ = 0 := fun n => hf (e n) (Submodule.subset_span ⟨n, rfl⟩)
  have hre : ∀ n, ⟪bR n, ReL f⟫_ℝ = 0 ∧ ⟪bR n, ImL f⟫_ℝ = 0 := by
    intro n
    have h := hz n
    rw [← decomp f, inner_add_right, inner_smul_right] at h
    change ⟪J (bR n), J (ReL f)⟫_ℂ + Complex.I * ⟪J (bR n), J (ImL f)⟫_ℂ = 0 at h
    rw [J_inner, J_inner] at h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    exact ⟨h1, h2⟩
  have hr : ReL f = 0 := bR_eq_zero (fun n => (hre n).1)
  have hi : ImL f = 0 := bR_eq_zero (fun n => (hre n).2)
  rw [← decomp f, hr, hi, map_zero, smul_zero, add_zero]

/-- The Hilbert basis `P_n^{(1/2)}` of `H`. -/
def eB : HilbertBasis ℕ ℂ H := HilbertBasis.mkOfOrthogonalEqBot e_orthonormal e_total

theorem eB_apply (n : ℕ) : eB n = e n := by
  simp only [eB, HilbertBasis.coe_mkOfOrthogonalEqBot]

theorem eB_ext {x y : H} (h : ∀ n, ⟪eB n, x⟫_ℂ = ⟪eB n, y⟫_ℂ) : x = y := by
  apply eB.repr.injective
  ext n
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, h n]

/-! ## The basis vectors are eigenpolynomials -/

/-- The complexified monic polynomial. -/
def Q (n : ℕ) : ℂ[X] := (G n).map Complex.ofRealHom

/-- The normalisation constant. -/
def nrm (n : ℕ) : ℝ := ‖PR n‖⁻¹

/-- The normalised complex polynomial `P_n^{(1/2)}`. -/
def q (n : ℕ) : ℂ[X] := ((nrm n : ℝ) : ℂ) • Q n

theorem J_polyR (p : ℝ[X]) :
    J (GegenbauerFock.Ultraspherical.sturmRealPolynomialLp (1 / 2) hhalf p) =
      polyLp (p.map Complex.ofRealHom) := by
  apply Lp.ext
  filter_upwards [J_ae (GegenbauerFock.Ultraspherical.sturmRealPolynomialLp (1 / 2) hhalf p),
    GegenbauerFock.Ultraspherical.sturmRealPolynomialLp_ae_eval (1 / 2) hhalf p,
    polyLp_ae_eq (p.map Complex.ofRealHom)] with u h1 h2 h3
  rw [h1, h2, h3]
  simp only [polyFun]
  rw [eval_map, ← Complex.ofRealHom_eq_coe u, eval₂_at_apply, Complex.ofRealHom_eq_coe]

theorem e_eq_polyLp (n : ℕ) : e n = polyLp (q n) := by
  rw [e, bR_apply, map_smul]
  show ‖PR n‖⁻¹ • J (GegenbauerFock.Ultraspherical.sturmRealPolynomialLp (1 / 2) hhalf (G n)) = _
  rw [J_polyR, q, polyLp_smul, Complex.coe_smul]
  rfl

theorem nrm_pos (n : ℕ) : 0 < nrm n := by
  have h1 : ‖bR n‖ = 1 := bR.orthonormal.1 n
  have hP : ‖PR n‖ ≠ 0 := by
    intro h0
    rw [bR_apply, h0, inv_zero, zero_smul, norm_zero] at h1
    exact zero_ne_one h1
  exact inv_pos.mpr (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hP))

/-- The eigenvalues `n(n+1)`. -/
def eig (n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) + 1)

theorem eig_nonneg (n : ℕ) : 0 ≤ eig n := by
  unfold eig
  positivity

theorem eig_mono {m n : ℕ} (h : m ≤ n) : eig m ≤ eig n := by
  unfold eig
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast h
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  exact mul_le_mul hmn (by linarith) (by linarith) (by linarith)

theorem le_eig (n : ℕ) : (n : ℝ) ≤ eig n := by
  unfold eig
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem DPoly_map (p : ℝ[X]) :
    DPoly (p.map Complex.ofRealHom) =
      -((GegenbauerFock.Ultraspherical.sturmPolynomial (1 / 2) p).map Complex.ofRealHom) := by
  have hC : Complex.ofRealHom (2 * (1 / 2 : ℝ) + 1) = 2 := by norm_num
  rw [DPoly_apply, GegenbauerFock.Ultraspherical.sturmPolynomial]
  simp only [Polynomial.derivative_map, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, Polynomial.map_C, hC]

theorem DPoly_Q (n : ℕ) : DPoly (Q n) = ((eig n : ℝ) : ℂ) • Q n := by
  rw [Q, DPoly_map, G,
    GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_eigen (1 / 2) hhalf n,
    Polynomial.map_smul, ← neg_smul]
  congr 1
  rw [GegenbauerFock.Ultraspherical.sturmEigenvalue, eig]
  simp only [Complex.ofRealHom_eq_coe]
  push_cast
  ring

theorem DPoly_q (n : ℕ) : DPoly (q n) = ((eig n : ℝ) : ℂ) • q n := by
  rw [q, map_smul, DPoly_Q, smul_comm ((nrm n : ℝ) : ℂ) ((eig n : ℝ) : ℂ) (Q n)]

theorem e_mem (n : ℕ) : e n ∈ DClosed.domain := by
  rw [e_eq_polyLp]
  exact DPMap_le_DClosed.1 (polyLp_mem _)

theorem DClosed_e (n : ℕ) : DClosed ⟨e n, e_mem n⟩ = ((eig n : ℝ) : ℂ) • e n := by
  have hq : polyLp (q n) ∈ DClosed.domain := DPMap_le_DClosed.1 (polyLp_mem _)
  have h := DClosed_polyLp (q n) hq
  have hv : (⟨e n, e_mem n⟩ : DClosed.domain) = ⟨polyLp (q n), hq⟩ :=
    Subtype.ext (e_eq_polyLp n)
  rw [hv, h, DPoly_q, polyLp_smul, e_eq_polyLp]

/-- **Identification of the basis with `P_n^{(1/2)}`:** `eB n` is the class of a polynomial of
degree `n` with positive leading coefficient, eigenpolynomial of `D⁰` for `n(n+1)`. -/
theorem eB_polynomial (n : ℕ) :
    eB n = polyLp (q n) ∧ (q n).natDegree = n ∧
      (∃ r : ℝ, 0 < r ∧ (q n).leadingCoeff = (r : ℂ)) ∧
      DPoly (q n) = ((eig n : ℝ) : ℂ) • q n := by
  have hc : ((nrm n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nrm_pos n).ne'
  have hreg : IsSMulRegular ℂ ((nrm n : ℝ) : ℂ) :=
    (isUnit_iff_ne_zero.mpr hc).isSMulRegular ℂ
  have hmonic : (Q n).Monic :=
    (GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_monic (1 / 2) n).map
      Complex.ofRealHom
  refine ⟨by rw [eB_apply, e_eq_polyLp], ?_, ⟨nrm n, nrm_pos n, ?_⟩, DPoly_q n⟩
  · rw [q]
    first
      | rw [natDegree_smul_of_smul_regular _ hreg]
      | rw [smul_eq_C_mul, natDegree_C_mul hc]
    rw [Q, natDegree_map_eq_of_injective Complex.ofRealHom.injective, G,
      GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_natDegree]
  · rw [q]
    first
      | rw [leadingCoeff_smul_of_smul_regular _ hreg, hmonic.leadingCoeff, smul_eq_mul, mul_one]
      | rw [smul_eq_C_mul, leadingCoeff_mul, leadingCoeff_C, hmonic.leadingCoeff, mul_one]

/-! ## The spectral realisation (8)–(9) -/

/-- The coefficients of `D̄ x` are `n(n+1)` times those of `x`. -/
theorem coeff_DClosed (x : DClosed.domain) (n : ℕ) :
    ⟪eB n, DClosed x⟫_ℂ = ((eig n : ℝ) : ℂ) * ⟪eB n, (x : H)⟫_ℂ := by
  rw [eB_apply]
  have h := DClosed_symm ⟨e n, e_mem n⟩ x
  rw [DClosed_e, inner_smul_left, Complex.conj_ofReal] at h
  exact h.symm

theorem memℓp_of_sq {a : ℕ → ℂ} (h : Summable fun n => ‖a n‖ ^ 2) : Memℓp a 2 :=
  memℓp_gen (h.congr fun n => by rw [ENNReal.toReal_ofNat, Real.rpow_two])

theorem summable_sq (v : H) : Summable fun n => ‖⟪eB n, v⟫_ℂ‖ ^ 2 := by
  have h := (lp.memℓp (eB.repr v)).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  refine h.congr fun n => ?_
  rw [HilbertBasis.repr_apply_apply, ENNReal.toReal_ofNat, Real.rpow_two]

theorem DClosed_graph_isClosed : IsClosed (DClosed.graph : Set (H × H)) := by
  rw [DClosed_graph_eq]
  exact isClosed_closure

/-- **(8)–(9), the domain:** `f ∈ Dom(D̄)` iff `∑ n²(n+1)² |⟨P_n, f⟩|² < ∞`. -/
theorem DClosed_domain_iff (f : H) :
    f ∈ DClosed.domain ↔ Summable fun n => eig n ^ 2 * ‖⟪eB n, f⟫_ℂ‖ ^ 2 := by
  constructor
  · intro hf
    refine (summable_sq (DClosed ⟨f, hf⟩)).congr fun n => ?_
    rw [coeff_DClosed ⟨f, hf⟩ n, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  · intro hs
    let a : ℕ → ℂ := fun n => ((eig n : ℝ) : ℂ) * ⟪eB n, f⟫_ℂ
    have hEq : ∀ n, ‖a n‖ ^ 2 = eig n ^ 2 * ‖⟪eB n, f⟫_ℂ‖ ^ 2 := by
      intro n
      simp only [a]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    have ha : Memℓp a 2 := memℓp_of_sq (hs.congr fun n => (hEq n).symm)
    let g : H := eB.repr.symm ⟨a, ha⟩
    have hg : ∀ n, ⟪eB n, g⟫_ℂ = a n := by
      intro n
      rw [← HilbertBasis.repr_apply_apply]
      simp only [g, LinearIsometryEquiv.apply_symm_apply]
    let s : ℕ → H := fun N => ∑ n ∈ Finset.range N, ⟪eB n, f⟫_ℂ • eB n
    let t : ℕ → H := fun N => ∑ n ∈ Finset.range N, a n • eB n
    have hgraph : ∀ N, (s N, t N) ∈ (DClosed.graph : Set (H × H)) := by
      intro N
      let y : DClosed.domain :=
        ∑ n ∈ Finset.range N, ⟪eB n, f⟫_ℂ • (⟨e n, e_mem n⟩ : DClosed.domain)
      have hy1 : (y : H) = s N := by
        simp only [y, s, Submodule.coe_sum, Submodule.coe_smul, eB_apply]
      have hy2 : DClosed y = t N := by
        simp only [y, t]
        change DClosed.toFun (∑ n ∈ Finset.range N,
          ⟪eB n, f⟫_ℂ • (⟨e n, e_mem n⟩ : DClosed.domain)) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro n _
        rw [map_smul]
        change ⟪eB n, f⟫_ℂ • DClosed ⟨e n, e_mem n⟩ = a n • eB n
        rw [DClosed_e, smul_smul, mul_comm]
        simp only [a, eB_apply]
      rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
      exact ⟨y, hy1, hy2⟩
    have hsf : Tendsto s atTop (𝓝 f) := by
      have h := (eB.hasSum_repr f).tendsto_sum_nat
      simp only [HilbertBasis.repr_apply_apply] at h
      exact h
    have htg : Tendsto t atTop (𝓝 g) := by
      have h := (eB.hasSum_repr g).tendsto_sum_nat
      simp only [HilbertBasis.repr_apply_apply, hg] at h
      exact h
    have hmem : (f, g) ∈ (DClosed.graph : Set (H × H)) :=
      DClosed_graph_isClosed.mem_of_tendsto (hsf.prodMk_nhds htg) (Eventually.of_forall hgraph)
    obtain ⟨y, hy1, _⟩ := (LinearPMap.mem_graph_iff DClosed).mp hmem
    have hy : (y : H) = f := hy1
    exact hy ▸ y.2

/-- **(8)–(9), the action:** `D̄ x = ∑ n(n+1) ⟨P_n, x⟩ P_n`. -/
theorem DClosed_hasSum (x : DClosed.domain) :
    HasSum (fun n => (((eig n : ℝ) : ℂ) * ⟪eB n, (x : H)⟫_ℂ) • eB n) (DClosed x) := by
  have h := eB.hasSum_repr (DClosed x)
  simp only [HilbertBasis.repr_apply_apply, coeff_DClosed] at h
  exact h

/-- `D̄` is selfadjoint. -/
theorem DClosed_isSelfAdjoint : IsSelfAdjoint DClosed := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hdense : Dense (DClosed.domain : Set H) := DPMap_domain_dense.mono DPMap_le_DClosed.1
  have hle : DClosed ≤ DClosed.adjoint :=
    LinearPMap.IsFormalAdjoint.le_adjoint hdense (fun x y => DClosed_symm x y)
  have hdom : DClosed.adjoint.domain ≤ DClosed.domain := by
    intro y hy
    rw [DClosed_domain_iff]
    refine (summable_sq (DClosed.adjoint ⟨y, hy⟩)).congr fun n => ?_
    have h := LinearPMap.adjoint_isFormalAdjoint hdense ⟨y, hy⟩ ⟨e n, e_mem n⟩
    rw [DClosed_e, inner_smul_right] at h
    have h' : ⟪eB n, DClosed.adjoint ⟨y, hy⟩⟫_ℂ = ((eig n : ℝ) : ℂ) * ⟪eB n, y⟫_ℂ := by
      rw [eB_apply, ← inner_conj_symm, h, map_mul, Complex.conj_ofReal, inner_conj_symm]
    rw [h', norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hdomeq : DClosed.adjoint.domain = DClosed.domain := le_antisymm hdom hle.1
  refine LinearPMap.ext hdomeq ?_
  intro x hx1 hx2
  exact (hle.2 (x := ⟨x, hx2⟩) (y := ⟨x, hx1⟩) rfl).symm

/-! ## Diagonal multipliers and the resolvent of `D̄` -/

local notation "ℓ²" => lp (fun _ : ℕ => ℂ) 2

theorem l2_norm_mono {f g : ℓ²} (h : ∀ i, ‖f i‖ ≤ ‖g i‖) : ‖f‖ ≤ ‖g‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  apply lp.norm_le_of_tsum_le hp (norm_nonneg g)
  rw [lp.norm_rpow_eq_tsum hp]
  exact Summable.tsum_le_tsum (fun i => Real.rpow_le_rpow (norm_nonneg _) (h i) hp.le)
    ((lp.memℓp f).summable hp) ((lp.memℓp g).summable hp)

theorem memℓp_mul (c : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖c n‖ ≤ C) (a : ℓ²) :
    Memℓp (fun n => c n * a n) 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  apply memℓp_gen
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (((lp.memℓp a).summable hp).mul_left (C ^ (2 : ENNReal).toReal))
  rw [norm_mul, ← Real.mul_rpow hC0 (norm_nonneg _)]
  exact Real.rpow_le_rpow (by positivity)
    (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _)) hp.le

/-- The bounded diagonal multiplier `f ↦ ∑ c_n ⟨P_n, f⟩ P_n`. -/
def mulOp (c : ℕ → ℂ) (C : ℝ) (hC : ∀ n, ‖c n‖ ≤ C) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun f => eB.repr.symm ⟨fun n => c n * eB.repr f n, memℓp_mul c hC (eB.repr f)⟩
      map_add' := fun f g => by
        rw [← map_add]; congr 1; ext n
        simp [mul_add] <;> rfl
      map_smul' := fun r f => by
        rw [← map_smul]; congr 1; ext n
        simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    C (fun f => by
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearIsometryEquiv.norm_map]
      calc _ ≤ ‖C • eB.repr f‖ := l2_norm_mono fun i => by
              simp only [norm_mul, lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
                abs_of_nonneg hC0]
              exact mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)
        _ ≤ ‖C‖ * ‖eB.repr f‖ := norm_smul_le _ _
        _ = C * ‖f‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hC0, LinearIsometryEquiv.norm_map])

theorem mulOp_inner (c : ℕ → ℂ) (C : ℝ) (hC : ∀ n, ‖c n‖ ≤ C) (f : H) (n : ℕ) :
    ⟪eB n, mulOp c C hC f⟫_ℂ = c n * ⟪eB n, f⟫_ℂ := by
  rw [← HilbertBasis.repr_apply_apply, ← HilbertBasis.repr_apply_apply]
  simp [mulOp]

theorem mulOp_norm_le (c : ℕ → ℂ) (C : ℝ) (hC : ∀ n, ‖c n‖ ≤ C) (hC0 : 0 ≤ C) :
    ‖mulOp c C hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC0 _

/-- The resolvent multipliers `(t + n(n+1))⁻¹`. -/
def rmult (t : ℝ) (n : ℕ) : ℂ := (((t + eig n)⁻¹ : ℝ) : ℂ)

theorem rmult_eq (t : ℝ) (n : ℕ) : rmult t n = ((t + eig n : ℝ) : ℂ)⁻¹ := by
  rw [rmult, Complex.ofReal_inv]

theorem rmult_bound (t : ℝ) (ht : 0 < t) (n : ℕ) : ‖rmult t n‖ ≤ t⁻¹ := by
  have hpos : 0 < t + eig n := by linarith [eig_nonneg n]
  rw [rmult, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  exact inv_anti₀ ht (by linarith [eig_nonneg n])

/-- `(D̄ + t)⁻¹` as a bounded diagonal operator. -/
def Rt (t : ℝ) (ht : 0 < t) : H →L[ℂ] H := mulOp (rmult t) t⁻¹ (rmult_bound t ht)

theorem Rt_inner (t : ℝ) (ht : 0 < t) (f : H) (n : ℕ) :
    ⟪eB n, Rt t ht f⟫_ℂ = rmult t n * ⟪eB n, f⟫_ℂ :=
  mulOp_inner _ _ _ f n

theorem Rt_norm_le (t : ℝ) (ht : 0 < t) : ‖Rt t ht‖ ≤ t⁻¹ :=
  mulOp_norm_le _ _ _ (inv_nonneg.mpr ht.le)

theorem Rt_mem (t : ℝ) (ht : 0 < t) (f : H) : Rt t ht f ∈ DClosed.domain := by
  rw [DClosed_domain_iff]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (summable_sq f)
  have hpos : 0 < t + eig n := by linarith [eig_nonneg n]
  have hr : ‖rmult t n * ⟪eB n, f⟫_ℂ‖ = (t + eig n)⁻¹ * ‖⟪eB n, f⟫_ℂ‖ := by
    rw [norm_mul, rmult, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  rw [Rt_inner, hr]
  have h1 : eig n * (t + eig n)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hpos]
    linarith
  have h0 : 0 ≤ eig n * (t + eig n)⁻¹ := mul_nonneg (eig_nonneg n) (inv_nonneg.mpr hpos.le)
  have h2 : (eig n * (t + eig n)⁻¹) ^ 2 ≤ 1 := by nlinarith
  have hre : eig n ^ 2 * ((t + eig n)⁻¹ * ‖⟪eB n, f⟫_ℂ‖) ^ 2 =
      (eig n * (t + eig n)⁻¹) ^ 2 * ‖⟪eB n, f⟫_ℂ‖ ^ 2 := by ring
  rw [hre]
  exact mul_le_of_le_one_left (sq_nonneg _) h2

/-- `(D̄ + t) (D̄ + t)⁻¹ = I`. -/
theorem DClosed_Rt (t : ℝ) (ht : 0 < t) (f : H) :
    DClosed ⟨Rt t ht f, Rt_mem t ht f⟩ + (t : ℂ) • Rt t ht f = f := by
  apply eB_ext
  intro n
  have hne : ((t + eig n : ℝ) : ℂ) ≠ 0 := by
    have : t + eig n ≠ 0 := by linarith [eig_nonneg n]
    exact_mod_cast this
  rw [inner_add_right, inner_smul_right, coeff_DClosed, Rt_inner, rmult_eq]
  calc ((eig n : ℝ) : ℂ) * (((t + eig n : ℝ) : ℂ)⁻¹ * ⟪eB n, f⟫_ℂ) +
        (t : ℂ) * (((t + eig n : ℝ) : ℂ)⁻¹ * ⟪eB n, f⟫_ℂ)
      = (((t + eig n : ℝ) : ℂ) * ((t + eig n : ℝ) : ℂ)⁻¹) * ⟪eB n, f⟫_ℂ := by
        push_cast
        ring
    _ = ⟪eB n, f⟫_ℂ := by rw [mul_inv_cancel₀ hne, one_mul]

/-- `(D̄ + t)⁻¹ (D̄ + t) = I` on `Dom(D̄)`. -/
theorem Rt_DClosed (t : ℝ) (ht : 0 < t) (x : DClosed.domain) :
    Rt t ht (DClosed x + (t : ℂ) • (x : H)) = x := by
  apply eB_ext
  intro n
  have hne : ((t + eig n : ℝ) : ℂ) ≠ 0 := by
    have : t + eig n ≠ 0 := by linarith [eig_nonneg n]
    exact_mod_cast this
  rw [Rt_inner, inner_add_right, inner_smul_right, coeff_DClosed, rmult_eq]
  calc ((t + eig n : ℝ) : ℂ)⁻¹ *
        (((eig n : ℝ) : ℂ) * ⟪eB n, (x : H)⟫_ℂ + (t : ℂ) * ⟪eB n, (x : H)⟫_ℂ)
      = (((t + eig n : ℝ) : ℂ)⁻¹ * ((t + eig n : ℝ) : ℂ)) * ⟪eB n, (x : H)⟫_ℂ := by
        push_cast
        ring
    _ = ⟪eB n, (x : H)⟫_ℂ := by rw [inv_mul_cancel₀ hne, one_mul]

/-! ## Compactness of `(D̄ + t)⁻¹` -/

theorem rankOne_compact (v : H) :
    IsCompactOperator ((ContinuousLinearMap.toSpanSingleton ℂ v).comp (innerSL ℂ v)) :=
  (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ v)).comp_clm (innerSL ℂ v)

/-- The finite spectral truncations of `(D̄ + t)⁻¹`. -/
def trunc (t : ℝ) (N : ℕ) : H →L[ℂ] H :=
  ∑ n ∈ Finset.range N,
    rmult t n • (ContinuousLinearMap.toSpanSingleton ℂ (eB n)).comp (innerSL ℂ (eB n))

/-- The truncations are compact: finite sums in the submodule `compactOperator` of
rank-one operators. -/
theorem trunc_compact (t : ℝ) (N : ℕ) : IsCompactOperator (trunc t N) := by
  show (∑ n ∈ Finset.range N,
      rmult t n • (ContinuousLinearMap.toSpanSingleton ℂ (eB n)).comp (innerSL ℂ (eB n))) ∈
    compactOperator (RingHom.id ℂ) H H
  exact Submodule.sum_mem _ fun n _ =>
    Submodule.smul_mem _ (rmult t n) (rankOne_compact (eB n))

theorem inner_trunc (t : ℝ) (N : ℕ) (f : H) (m : ℕ) :
    ⟪eB m, trunc t N f⟫_ℂ = if m < N then rmult t m * ⟪eB m, f⟫_ℂ else 0 := by
  classical
  have ho := orthonormal_iff_ite.mp eB.orthonormal
  simp only [trunc, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, coe_innerSL_apply,
    inner_sum, inner_smul_right, ho m, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_range]

/-- The tail multipliers. -/
def tail (t : ℝ) (N n : ℕ) : ℂ := if n < N then 0 else rmult t n

theorem tail_bound (t : ℝ) (ht : 0 < t) (N n : ℕ) : ‖tail t N n‖ ≤ (t + eig N)⁻¹ := by
  have hposN : 0 < t + eig N := by linarith [eig_nonneg N]
  unfold tail
  split_ifs with h
  · rw [norm_zero]
    exact inv_nonneg.mpr hposN.le
  · have hpos : 0 < t + eig n := by linarith [eig_nonneg n]
    rw [rmult, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    apply inv_anti₀ hposN
    have : eig N ≤ eig n := eig_mono (not_lt.mp h)
    linarith

theorem Rt_sub_trunc (t : ℝ) (ht : 0 < t) (N : ℕ) :
    Rt t ht - trunc t N = mulOp (tail t N) (t + eig N)⁻¹ (tail_bound t ht N) := by
  refine ContinuousLinearMap.ext fun f => eB_ext fun m => ?_
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, Rt_inner, inner_trunc, mulOp_inner, tail]
  split_ifs <;> ring

/-- **`(D̄ + t)⁻¹` is compact.** -/
theorem Rt_compact (t : ℝ) (ht : 0 < t) : IsCompactOperator (Rt t ht) := by
  have hbound : ∀ N : ℕ, ‖trunc t N - Rt t ht‖ ≤ (t + eig N)⁻¹ := by
    intro N
    rw [norm_sub_rev, Rt_sub_trunc]
    exact mulOp_norm_le _ _ _ (inv_nonneg.mpr (by linarith [eig_nonneg N]))
  have hinf : Tendsto (fun N : ℕ => t + eig N) atTop atTop := by
    refine tendsto_atTop_mono (fun N => ?_) tendsto_natCast_atTop_atTop
    linarith [le_eig N]
  have hzero : Tendsto (fun N : ℕ => (t + eig N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hinf
  have hlim : Tendsto (fun N => trunc t N) atTop (𝓝 (Rt t ht)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero (fun N => norm_nonneg _) hbound hzero)
  exact isCompactOperator_of_tendsto hlim (Eventually.of_forall (trunc_compact t))

/-! ## The compact resolvent of `𝒜_c` -/

theorem M_norm_le : ‖M‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- **Compact resolvent of `𝒜_c`:** for every real `c`, `𝒜_c + (c² + 1)` has a compact bounded
two-sided inverse `R` on `Dom(𝒜_c)`. -/
theorem AClosed_compact_resolvent (c : ℝ) :
    ∃ R : H →L[ℂ] H, IsCompactOperator R ∧
      (∀ f : H, ∃ h : R f ∈ (AClosed c).domain,
        AClosed c ⟨R f, h⟩ + ((c ^ 2 + 1 : ℝ) : ℂ) • R f = f) ∧
      (∀ x : (AClosed c).domain,
        R (AClosed c x + ((c ^ 2 + 1 : ℝ) : ℂ) • (x : H)) = x) := by
  have ht : (0 : ℝ) < c ^ 2 + 1 := by positivity
  have hRt := Rt_norm_le (c ^ 2 + 1) ht
  have hnorm : ‖((c : ℂ) ^ 2)‖ = c ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  obtain ⟨K, hKapp, hK⟩ : ∃ K : H →L[ℂ] H,
      (∀ z, K z = ((c : ℂ) ^ 2) • M (Rt (c ^ 2 + 1) ht z)) ∧ ‖K‖ < 1 := by
    refine ⟨((c : ℂ) ^ 2) • M.comp (Rt (c ^ 2 + 1) ht), fun z => rfl, ?_⟩
    have h1 : ‖((c : ℂ) ^ 2) • M.comp (Rt (c ^ 2 + 1) ht)‖ ≤ c ^ 2 * (c ^ 2 + 1)⁻¹ := by
      calc ‖((c : ℂ) ^ 2) • M.comp (Rt (c ^ 2 + 1) ht)‖
          ≤ ‖((c : ℂ) ^ 2)‖ * ‖M.comp (Rt (c ^ 2 + 1) ht)‖ :=
            ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ c ^ 2 * (‖M‖ * ‖Rt (c ^ 2 + 1) ht‖) :=
            mul_le_mul (le_of_eq hnorm) (ContinuousLinearMap.opNorm_comp_le _ _)
              (norm_nonneg _) (sq_nonneg c)
        _ ≤ c ^ 2 * (1 * (c ^ 2 + 1)⁻¹) :=
            mul_le_mul_of_nonneg_left (mul_le_mul M_norm_le hRt (norm_nonneg _) zero_le_one)
              (sq_nonneg c)
        _ = c ^ 2 * (c ^ 2 + 1)⁻¹ := by ring
    have h2 : c ^ 2 * (c ^ 2 + 1)⁻¹ < 1 := by
      rw [mul_inv_lt_iff₀ ht]
      linarith
    linarith
  obtain ⟨V, hV1, hV2⟩ : ∃ V : H →L[ℂ] H, (1 - K) * V = 1 ∧ V * (1 - K) = 1 := by
    refine ⟨↑(Units.oneSub K hK)⁻¹, ?_, ?_⟩
    · have h := (Units.oneSub K hK).mul_inv
      rwa [Units.val_oneSub] at h
    · have h := (Units.oneSub K hK).inv_mul
      rwa [Units.val_oneSub] at h
  refine ⟨(Rt (c ^ 2 + 1) ht).comp V, (Rt_compact (c ^ 2 + 1) ht).comp_clm V, ?_, ?_⟩
  · intro f
    refine ⟨Rt_mem (c ^ 2 + 1) ht (V f), ?_⟩
    have h1 := DClosed_Rt (c ^ 2 + 1) ht (V f)
    have h2 : V f - K (V f) = f := by
      have h := DFunLike.congr_fun hV1 f
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply] at h
      exact h
    calc AClosed c ⟨Rt (c ^ 2 + 1) ht (V f), Rt_mem (c ^ 2 + 1) ht (V f)⟩ +
          ((c ^ 2 + 1 : ℝ) : ℂ) • Rt (c ^ 2 + 1) ht (V f)
        = (DClosed ⟨Rt (c ^ 2 + 1) ht (V f), Rt_mem (c ^ 2 + 1) ht (V f)⟩ +
            ((c ^ 2 + 1 : ℝ) : ℂ) • Rt (c ^ 2 + 1) ht (V f)) -
            ((c : ℂ) ^ 2) • M (Rt (c ^ 2 + 1) ht (V f)) := by
          rw [AClosed_apply]
          abel
      _ = V f - K (V f) := by rw [h1, hKapp]
      _ = f := h2
  · intro x
    have hx := Rt_DClosed (c ^ 2 + 1) ht x
    have h3 : (1 - K) (DClosed x + ((c ^ 2 + 1 : ℝ) : ℂ) • (x : H)) =
        AClosed c x + ((c ^ 2 + 1 : ℝ) : ℂ) • (x : H) := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hKapp, hx,
        AClosed_apply]
      abel
    have h4 : V ((1 - K) (DClosed x + ((c ^ 2 + 1 : ℝ) : ℂ) • (x : H))) =
        DClosed x + ((c ^ 2 + 1 : ℝ) : ℂ) • (x : H) := by
      have h := DFunLike.congr_fun hV2 (DClosed x + ((c ^ 2 + 1 : ℝ) : ℂ) • (x : H))
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h
      exact h
    show Rt (c ^ 2 + 1) ht (V (AClosed c x + ((c ^ 2 + 1 : ℝ) : ℂ) • (x : H))) = x
    rw [← h3, h4, hx]

#print axioms Manuscript14Gram.Spectral.eB_polynomial
#print axioms Manuscript14Gram.Spectral.DClosed_domain_iff
#print axioms Manuscript14Gram.Spectral.DClosed_hasSum
#print axioms Manuscript14Gram.Spectral.DClosed_isSelfAdjoint
#print axioms Manuscript14Gram.Spectral.Rt_compact
#print axioms Manuscript14Gram.Spectral.AClosed_compact_resolvent

end Manuscript14Gram.Spectral

end
