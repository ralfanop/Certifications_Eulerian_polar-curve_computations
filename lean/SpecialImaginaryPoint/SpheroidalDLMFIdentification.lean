import Mathlib
import SpecialImaginaryPoint.SpheroidalProposition54

/-!
# Manuscript 14, Proposition 5.4: identification with the angular spheroidal functions of DLMF §30

The eigenvectors `ψ_n` of Proposition 5.4 are identified with the angular spheroidal wave
functions `Ps_n^0(·, γ²)` of DLMF §30 at `γ² = -c²` (the oblate case, imaginary bandwidth
`-ic`), with `λ_n^0(-c²) = χ_n + c²`.

DLMF §30 has no Mathlib counterpart, so its definition enters as an explicit hypothesis, the
structure `OblateInput c`, which records, for `μ = 0` and `γ² = -c²`:

* the eigenvalues `λ_n^0(γ²)`, a strictly increasing sequence (DLMF §30.3(i));
* the eigenfunctions `Ps_n^0(·, γ²)`, real, not identically zero on `[-1,1]`, solutions on
  `[-1,1]` of DLMF (30.2.1), `(1-x²) w'' - 2x w' + (λ + γ²(1-x²)) w = 0` (§30.2(i)); since
  `L²(ν_{1/2})` only sees `[-1,1]`, each is taken as a `C²` function on the real line;
* the characterisation of DLMF §30.2(iii): a `C²` solution of (30.2.1) on `[-1,1]` that is not
  identically zero there exists only for `λ = λ_n^0(γ²)`, and it is a multiple of
  `Ps_n^0(·, γ²)`.

Kernel-checked here, for every `c > 0` and every such input:

* `Ps_eigen`: each `Ps_n^0(·, -c²)` lies in `Dom(𝒜_c)` (the closed operator of Theorem 5.2) and
  `𝒜_c Ps_n^0 = (λ_n^0(-c²) - c²) Ps_n^0`;
* `basis_ode`: every vector of the joint eigenbasis of Proposition 5.4 is the class of a smooth
  function solving (30.2.1) on `[-1,1]` with `λ = χ + c²`;
* `spheroidal_DLMF_identification`: `L²(ν_{1/2}; ℂ)` has a Hilbert basis `(ψ_n)_{n ∈ ℕ}` of
  common eigenvectors of `𝒜_c`, `S_{1/2,c}` and `Π`, with `𝒜_c ψ_n = (λ_n^0(-c²) - c²) ψ_n`,
  `S_{1/2,c} ψ_n = σ_n ψ_n`, `σ_n > 0`, `∑ σ_n = ₁F₁(1/2; 3/2; c)`, and `ψ_n` a nonzero
  multiple of `Ps_n^0(·, -c²)`; that is, `χ_n + c² = λ_n^0(-c²)` with the DLMF numbering.

Method: a basis vector `ψ` is an eigenvector of `S_{1/2,c}` with `σ > 0`, so `ψ = σ⁻¹ S ψ` is
the class of the smooth kernel integral; on smooth functions `𝒜_c` acts as the differential
expression (Lemma 4 of Theorem 5.2), and two continuous functions that agree `ν`-almost
everywhere agree on `[-1,1]`.  The DLMF characterisation then attaches an index `N(ψ)` to each
basis vector; `N` is injective by orthonormality and surjective because each `Ps_n^0` is a
nonzero eigenvector of the symmetric `𝒜_c`, hence not orthogonal to the whole basis.
-/

noncomputable section

open MeasureTheory Polynomial Set
open scoped InnerProductSpace ENNReal

namespace Manuscript14Gram.DLMF30

open Manuscript14Gram.Theorem52 Manuscript14Gram.Prop54

/-! ## The DLMF equation and its input -/

/-- The angular spheroidal expression of DLMF (30.2.1) with `μ = 0`:
`(1 - x²) w'' - 2x w' + (λ + γ²(1 - x²)) w`. -/
def spheroidalExpr (γsq l : ℝ) (w : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((1 - x ^ 2 : ℝ) : ℂ) * deriv (deriv w) x - ((2 * x : ℝ) : ℂ) * deriv w x
    + ((l + γsq * (1 - x ^ 2) : ℝ) : ℂ) * w x

/-- **DLMF §30.2–§30.3 for `μ = 0`, `γ² = -c²`, as input.**  `lam n = λ_n^0(-c²)` and
`Ps n = Ps_n^0(·, -c²)` on `[-1,1]`. -/
structure OblateInput (c : ℝ) where
  lam : ℕ → ℝ
  lam_strictMono : StrictMono lam
  Ps : ℕ → ℝ → ℂ
  Ps_real : ∀ n x, (Ps n x).im = 0
  Ps_contDiff : ∀ n, ContDiff ℝ 2 (Ps n)
  Ps_eq : ∀ n, ∀ x ∈ Icc (-1 : ℝ) 1, spheroidalExpr (-c ^ 2) (lam n) (Ps n) x = 0
  Ps_ne : ∀ n, ∃ x ∈ Icc (-1 : ℝ) 1, Ps n x ≠ 0
  unique : ∀ (l : ℝ) (w : ℝ → ℂ), ContDiff ℝ 2 w →
    (∀ x ∈ Icc (-1 : ℝ) 1, spheroidalExpr (-c ^ 2) l w x = 0) →
    (∃ x ∈ Icc (-1 : ℝ) 1, w x ≠ 0) →
    ∃ n, l = lam n ∧ ∃ a : ℂ, ∀ x ∈ Icc (-1 : ℝ) 1, w x = a * Ps n x

/-! ## Calculus and measure-theoretic lemmas -/

/-- `D_{1/2} g = -[(1-u²) g'' - 2u g']` for `C²` functions. -/
theorem DExpr_eq (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) (u : ℝ) :
    DExpr g u = -(((1 - u ^ 2 : ℝ) : ℂ) * deriv (deriv g) u - ((2 * u : ℝ) : ℂ) * deriv g u) := by
  have hg2 : ContDiff ℝ (1 + 1) g := by norm_num; exact hg
  have hgd : ContDiff ℝ 1 (deriv g) := hg2.deriv'
  have h2 : HasDerivAt (deriv g) (deriv (deriv g) u) u :=
    (hgd.differentiable one_ne_zero u).hasDerivAt
  have h0 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * u)) u := by
    simpa using (hasDerivAt_pow 2 u).const_sub 1
  have h1 : HasDerivAt (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ)) ((-(2 * u) : ℝ) : ℂ) u :=
    h0.ofReal_comp
  have hd : deriv (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) * deriv g t) u
      = ((-(2 * u) : ℝ) : ℂ) * deriv g u + ((1 - u ^ 2 : ℝ) : ℂ) * deriv (deriv g) u :=
    (h1.mul h2).deriv
  simp only [DExpr]
  rw [hd]
  push_cast
  ring

theorem AExpr_continuous (c : ℝ) (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) : Continuous (AExpr c g) := by
  have hq : Continuous (fun u : ℝ => ((c ^ 2 * u ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (by fun_prop)
  exact (DExpr_continuous g hg).sub (hq.mul hg.continuous)

/-- `𝒜_c` acts on `C²` functions as the differential expression. -/
theorem AClosed_cLp (c : ℝ) (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) :
    ∃ hmem : cLp g hg.continuous ∈ (AClosed c).domain,
      ((AClosed c ⟨cLp g hg.continuous, hmem⟩ : H) : ℝ → ℂ) =ᵐ[ν] AExpr c g := by
  obtain ⟨hmem, hval⟩ := smooth_mem_closure_domain g hg
  refine ⟨hmem, ?_⟩
  have e1 : AClosed c ⟨cLp g hg.continuous, hmem⟩
      = DClosed ⟨cLp g hg.continuous, hmem⟩ - ((c : ℂ) ^ 2) • M (cLp g hg.continuous) := rfl
  rw [e1]
  filter_upwards [Lp.coeFn_sub (DClosed ⟨cLp g hg.continuous, hmem⟩)
      (((c : ℂ) ^ 2) • M (cLp g hg.continuous)),
    Lp.coeFn_smul ((c : ℂ) ^ 2) (M (cLp g hg.continuous)), hval,
    M_apply_ae (cLp g hg.continuous), cLp_ae_eq g hg.continuous] with u h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, h5, AExpr_eq, smul_eq_mul]
  push_cast
  ring

/-- `Lebesgue|_{(-1,1)} ≪ ν`. -/
theorem volume_Ioo_ac : (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 1) ≪ ν := by
  have hfm : Measurable (fun u : ℝ =>
      ENNReal.ofReal (GegenbauerFock.Ultraspherical.eulerianUniformDensity u)) := by
    apply ENNReal.measurable_ofReal.comp
    unfold GegenbauerFock.Ultraspherical.eulerianUniformDensity
    exact Measurable.ite measurableSet_Ioo measurable_const measurable_const
  have hne : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 1)),
      ENNReal.ofReal (GegenbauerFock.Ultraspherical.eulerianUniformDensity x) ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx' : -1 < x ∧ x < 1 := hx
    have hd : GegenbauerFock.Ultraspherical.eulerianUniformDensity x = 1 / 2 := by
      unfold GegenbauerFock.Ultraspherical.eulerianUniformDensity
      rw [if_pos hx']
    rw [hd, Ne, ENNReal.ofReal_eq_zero]
    norm_num
  have h1 := withDensity_absolutelyContinuous' hfm.aemeasurable hne
  refine h1.trans ?_
  have h2 : ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 1)).withDensity
      (fun u : ℝ => ENNReal.ofReal (GegenbauerFock.Ultraspherical.eulerianUniformDensity u))
      = ν.restrict (Ioo (-1) 1) := by
    change _ = (GegenbauerFock.Ultraspherical.measure (1 / 2 : ℝ)).restrict (Ioo (-1) 1)
    rw [GegenbauerFock.Ultraspherical.measure_half_eq_uniformDensity,
      restrict_withDensity measurableSet_Ioo]
  rw [h2]
  exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self

/-- Continuous functions that agree `ν`-almost everywhere agree on `[-1,1]`. -/
theorem eqOn_Icc_of_ae_eq (g h : ℝ → ℂ) (hg : Continuous g) (hh : Continuous h)
    (hgh : g =ᵐ[ν] h) : EqOn g h (Icc (-1 : ℝ) 1) := by
  have hae : g =ᵐ[(volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 1)] h := volume_Ioo_ac.ae_eq hgh
  have hIoo : EqOn g h (Ioo (-1 : ℝ) 1) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Ioo hg.continuousOn hh.continuousOn
  exact hIoo.of_subset_closure hg.continuousOn hh.continuousOn Ioo_subset_Icc_self
    (closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)).ge

/-- Classes of continuous functions that agree on `[-1,1]` coincide. -/
theorem cLp_congr_Icc (g h : ℝ → ℂ) (hg : Continuous g) (hh : Continuous h)
    (hgh : ∀ x ∈ Icc (-1 : ℝ) 1, g x = h x) : cLp g hg = cLp h hh := by
  apply Lp.ext
  filter_upwards [cLp_ae_eq g hg, cLp_ae_eq h hh, ae_mem_Icc] with u h1 h2 hu
  rw [h1, h2, hgh u hu]

theorem cLp_smul (a : ℂ) (g : ℝ → ℂ) (hg : Continuous g) :
    a • cLp g hg = cLp (fun u => a * g u) (continuous_const.mul hg) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul a (cLp g hg), cLp_ae_eq g hg,
    cLp_ae_eq (fun u => a * g u) (continuous_const.mul hg)] with u h1 h2 h3
  rw [h1, Pi.smul_apply, h2, h3, smul_eq_mul]

/-- The class of a continuous function that does not vanish identically on `[-1,1]` is nonzero. -/
theorem cLp_ne_zero (g : ℝ → ℂ) (hg : Continuous g) (hne : ∃ x ∈ Icc (-1 : ℝ) 1, g x ≠ 0) :
    cLp g hg ≠ 0 := by
  intro h0
  obtain ⟨x, hx, hgx⟩ := hne
  have h1 := cLp_ae_eq g hg
  rw [h0] at h1
  have hae : g =ᵐ[ν] fun _ => (0 : ℂ) := h1.symm.trans (Lp.coeFn_zero ℂ 2 ν)
  exact hgx (eqOn_Icc_of_ae_eq g (fun _ => (0 : ℂ)) hg continuous_const hae hx)

theorem cLp_zero : cLp (fun _ => (0 : ℂ)) continuous_const = 0 := by
  apply Lp.ext
  filter_upwards [cLp_ae_eq (fun _ => (0 : ℂ)) continuous_const, Lp.coeFn_zero ℂ 2 ν]
    with u h1 h2
  simp only [h1, h2, Pi.zero_apply]

/-! ## The DLMF eigenfunctions are eigenvectors of `𝒜_c` -/

variable {c : ℝ}

theorem Ps_continuous (D : OblateInput c) (n : ℕ) : Continuous (D.Ps n) :=
  (D.Ps_contDiff n).continuous

/-- `Ps_n^0(·, -c²) ∈ Dom(𝒜_c)` and `𝒜_c Ps_n^0 = (λ_n^0(-c²) - c²) Ps_n^0`. -/
theorem Ps_eigen (D : OblateInput c) (n : ℕ) :
    ∃ hmem : cLp (D.Ps n) (Ps_continuous D n) ∈ (AClosed c).domain,
      AClosed c ⟨cLp (D.Ps n) (Ps_continuous D n), hmem⟩
        = ((D.lam n - c ^ 2 : ℝ) : ℂ) • cLp (D.Ps n) (Ps_continuous D n) := by
  obtain ⟨hmem, hval⟩ := AClosed_cLp c (D.Ps n) (D.Ps_contDiff n)
  refine ⟨hmem, Lp.ext ?_⟩
  filter_upwards [hval, Lp.coeFn_smul ((D.lam n - c ^ 2 : ℝ) : ℂ) (cLp (D.Ps n) (Ps_continuous D n)),
    cLp_ae_eq (D.Ps n) (Ps_continuous D n), ae_mem_Icc] with u h1 h2 h3 hu
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul, AExpr_eq, DExpr_eq _ (D.Ps_contDiff n)]
  have h := D.Ps_eq n u hu
  simp only [spheroidalExpr] at h
  push_cast at h ⊢
  linear_combination (-1 : ℂ) * h

theorem Ps_cLp_ne_zero (D : OblateInput c) (n : ℕ) : cLp (D.Ps n) (Ps_continuous D n) ≠ 0 :=
  cLp_ne_zero _ _ (D.Ps_ne n)

/-! ## The basis vectors of Proposition 5.4 solve the DLMF equation -/

/-- A vector `ψ ∈ Dom(𝒜_c)` with `𝒜_c ψ = χ ψ` (`χ` real) and `S_{1/2,c} ψ = σ ψ` (`σ > 0`) is
the class of a smooth function solving (30.2.1) on `[-1,1]` with `γ² = -c²`, `λ = χ + c²`. -/
theorem basis_ode (hc : 0 < c) (ψ : H) (hψ : ψ ∈ (AClosed c).domain) (χ σ : ℝ) (hσ : 0 < σ)
    (hA : AClosed c ⟨ψ, hψ⟩ = (χ : ℂ) • ψ) (hS : S c hc ψ = (σ : ℂ) • ψ) :
    ∃ (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g), ψ = cLp g hg.continuous ∧
      ∀ x ∈ Icc (-1 : ℝ) 1, spheroidalExpr (-c ^ 2) (χ + c ^ 2) g x = 0 := by
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℂ, g = fun u => ((σ : ℂ))⁻¹ * SFun c (ψ : ℝ → ℂ) u :=
    ⟨_, rfl⟩
  have hg : ContDiff ℝ 2 g := by
    rw [hgdef]
    exact contDiff_const.mul (SFun_contDiff c hc ψ 2)
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hψg : ψ = cLp g hg.continuous := by
    have h1 : ψ = ((σ : ℂ))⁻¹ • S c hc ψ := by
      rw [hS, smul_smul, inv_mul_cancel₀ hσ0, one_smul]
    have h2 : ((σ : ℂ))⁻¹ • S c hc ψ = cLp g hg.continuous := by
      rw [S_eq_cLp, cLp_smul]
      congr 1
      exact hgdef.symm
    exact h1.trans h2
  refine ⟨g, hg, hψg, ?_⟩
  obtain ⟨hmem, hval⟩ := AClosed_cLp c g hg
  have hsame : AClosed c ⟨cLp g hg.continuous, hmem⟩ = (χ : ℂ) • cLp g hg.continuous := by
    have hv : (⟨cLp g hg.continuous, hmem⟩ : (AClosed c).domain) = ⟨ψ, hψ⟩ :=
      Subtype.ext hψg.symm
    rw [hv, hA, hψg]
  have hae : AExpr c g =ᵐ[ν] fun u => (χ : ℂ) * g u := by
    rw [hsame] at hval
    filter_upwards [hval, Lp.coeFn_smul (χ : ℂ) (cLp g hg.continuous),
      cLp_ae_eq g hg.continuous] with u h1 h2 h3
    rw [← h1, h2, Pi.smul_apply, h3, smul_eq_mul]
  have heq := eqOn_Icc_of_ae_eq (AExpr c g) (fun u => (χ : ℂ) * g u) (AExpr_continuous c g hg)
    (continuous_const.mul hg.continuous) hae
  intro x hx
  have h := heq hx
  simp only [AExpr_eq, DExpr_eq g hg] at h
  simp only [spheroidalExpr]
  push_cast at h ⊢
  linear_combination (-1 : ℂ) * h

/-! ## The identification -/

/-- **Proposition 5.4, identification with DLMF §30:** for every `c > 0` and the DLMF input at
`γ² = -c²`, `L²(ν_{1/2}; ℂ)` has a Hilbert basis `(ψ_n)_{n ∈ ℕ}` of common eigenvectors of
`𝒜_c`, `S_{1/2,c}` and `Π` with `𝒜_c ψ_n = (λ_n^0(-c²) - c²) ψ_n`, `S_{1/2,c} ψ_n = σ_n ψ_n`,
`σ_n > 0`, `∑ σ_n = ₁F₁(1/2; 3/2; c)`, and `ψ_n` a nonzero multiple of `Ps_n^0(·, -c²)`. -/
theorem spheroidal_DLMF_identification (hc : 0 < c) (D : OblateInput c) :
    ∃ (b : HilbertBasis ℕ ℂ H) (σ : ℕ → ℝ) (e : ℕ → Bool)
      (hdom : ∀ n, (b n : H) ∈ (AClosed c).domain),
      (∀ n, AClosed c ⟨b n, hdom n⟩ = ((D.lam n - c ^ 2 : ℝ) : ℂ) • b n) ∧
      (∀ n, S c hc (b n) = (σ n : ℂ) • b n) ∧ (∀ n, 0 < σ n) ∧
      (∀ n, Par (b n) = sgn (e n) • b n) ∧
      HasSum σ (GegenbauerFock.KummerCoefficients.kummerSeries (1 / 2) c) ∧
      (∀ n, ∃ a : ℂ, a ≠ 0 ∧ b n = a • cLp (D.Ps n) (Ps_continuous D n)) := by
  obtain ⟨κ, b, χ, σ, par, hdom, hA, hS, hσ, hPar, hsum⟩ := spheroidal_joint_eigenbasis c hc
  -- each basis vector is a multiple of some `Ps_N`
  have hN : ∀ i, ∃ n, χ i + c ^ 2 = D.lam n ∧ ∃ a : ℂ, a ≠ 0 ∧
      b i = a • cLp (D.Ps n) (Ps_continuous D n) := by
    intro i
    obtain ⟨g, hg, hbg, hode⟩ := basis_ode hc (b i) (hdom i) (χ i) (σ i) (hσ i) (hA i) (hS i)
    have hne : ∃ x ∈ Icc (-1 : ℝ) 1, g x ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply b.orthonormal.ne_zero i
      rw [hbg, cLp_congr_Icc g (fun _ => (0 : ℂ)) hg.continuous continuous_const hcon]
      exact cLp_zero
    obtain ⟨n, hn, a, ha⟩ := D.unique (χ i + c ^ 2) g hg hode hne
    have hb : b i = a • cLp (D.Ps n) (Ps_continuous D n) := by
      rw [hbg, cLp_smul]
      exact cLp_congr_Icc _ _ _ _ ha
    refine ⟨n, hn, a, ?_, hb⟩
    rintro rfl
    apply b.orthonormal.ne_zero i
    rw [hb, zero_smul]
  choose N hNlam a ha hb using hN
  -- `N` is injective
  have hinj : Function.Injective N := by
    intro i j hij
    by_contra hne
    set P := cLp (D.Ps (N i)) (Ps_continuous D (N i)) with hP
    have hbj : b j = a j • P := by
      rw [hb j, hP]
      congr 1
      rw [hij]
    have hP0 : P ≠ 0 := Ps_cLp_ne_zero D (N i)
    have hPP : ⟪P, P⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hP0
    have h0 : ⟪b i, b j⟫_ℂ = 0 := b.orthonormal.inner_eq_zero hne
    rw [hb i, hbj, inner_smul_left, inner_smul_right] at h0
    have hai : (starRingEnd ℂ) (a i) ≠ 0 := by
      rw [map_ne_zero]
      exact ha i
    exact mul_ne_zero hai (mul_ne_zero (ha j) hPP) h0
  -- `N` is surjective
  have hsurj : Function.Surjective N := by
    intro n
    set P := cLp (D.Ps n) (Ps_continuous D n) with hP
    obtain ⟨hmem, hAP⟩ := Ps_eigen D n
    have hP0 : P ≠ 0 := Ps_cLp_ne_zero D n
    have hex : ∃ i, ⟪b i, P⟫_ℂ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hP0
      have h := b.hasSum_repr P
      have hz : (fun i => b.repr P i • b i) = fun _ => (0 : H) := by
        funext i
        rw [HilbertBasis.repr_apply_apply, hcon i, zero_smul]
      rw [hz] at h
      exact h.unique hasSum_zero
    obtain ⟨i, hi⟩ := hex
    have hsym := AClosed_symm c ⟨b i, hdom i⟩ ⟨P, hmem⟩
    have hAP' : AClosed c ⟨P, hmem⟩ = ((D.lam n - c ^ 2 : ℝ) : ℂ) • P := hAP
    rw [hA i, hAP', inner_smul_left, inner_smul_right, Complex.conj_ofReal] at hsym
    have hχ : ((χ i : ℝ) : ℂ) = ((D.lam n - c ^ 2 : ℝ) : ℂ) := mul_right_cancel₀ hi hsym
    have hχ' : χ i = D.lam n - c ^ 2 := by exact_mod_cast hχ
    refine ⟨i, D.lam_strictMono.injective ?_⟩
    rw [← hNlam i, hχ']
    ring
  -- reindex the basis by `ℕ`
  obtain ⟨eN, heqN⟩ : ∃ e : κ ≃ ℕ, ∀ i, e i = N i :=
    ⟨Equiv.ofBijective N ⟨hinj, hsurj⟩, fun i => rfl⟩
  have hNe : ∀ n, N (eN.symm n) = n := fun n => by
    rw [← heqN, Equiv.apply_symm_apply]
  have hon : Orthonormal ℂ (⇑b ∘ ⇑eN.symm) := b.orthonormal.comp _ eN.symm.injective
  have hsp : ⊤ ≤ (Submodule.span ℂ (Set.range (⇑b ∘ ⇑eN.symm))).topologicalClosure := by
    rw [EquivLike.range_comp]
    exact b.dense_span.ge
  obtain ⟨B, hBn⟩ : ∃ B : HilbertBasis ℕ ℂ H, ∀ n, B n = b (eN.symm n) :=
    ⟨HilbertBasis.mk hon hsp, fun n => by simp only [HilbertBasis.coe_mk, Function.comp_apply]⟩
  have hdomB : ∀ n, (B n : H) ∈ (AClosed c).domain := fun n => by
    rw [hBn]
    exact hdom (eN.symm n)
  refine ⟨B, σ ∘ eN.symm, par ∘ eN.symm, hdomB, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have hv : (⟨B n, hdomB n⟩ : (AClosed c).domain) = ⟨b (eN.symm n), hdom (eN.symm n)⟩ :=
      Subtype.ext (hBn n)
    have hχn : χ (eN.symm n) = D.lam n - c ^ 2 := by
      have h := hNlam (eN.symm n)
      rw [hNe n] at h
      linarith
    rw [hv, hA, hBn, hχn]
  · intro n
    rw [hBn]
    exact hS (eN.symm n)
  · intro n
    exact hσ (eN.symm n)
  · intro n
    rw [hBn]
    exact hPar (eN.symm n)
  · exact (Equiv.hasSum_iff eN.symm).mpr hsum
  · intro n
    refine ⟨a (eN.symm n), ha (eN.symm n), ?_⟩
    have h := hb (eN.symm n)
    rw [hBn, h]
    congr 1
    rw [hNe n]

end Manuscript14Gram.DLMF30

end

#print axioms Manuscript14Gram.DLMF30.Ps_eigen
#print axioms Manuscript14Gram.DLMF30.basis_ode
#print axioms Manuscript14Gram.DLMF30.spheroidal_DLMF_identification
