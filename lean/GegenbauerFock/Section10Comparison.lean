import GegenbauerFock.Section3Ultraspherical
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicEigenPolynomial
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealSpectralModes
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2HilbertBasis
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2BasisResolvent
import GegenbauerFock.UltrasphericalSturmLiouvilleRealClosedFullResolvent
import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventSpectralGraph
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Manuscript 13, Section 10: comparison with Fourier–Gegenbauer Green-function expansions

* **Proposition 10.1** (`prop:funk-hecke`, `proposition_10_1`). On `S^{d-1} ⊂ ℝ^d`, `d ≥ 3`,
  `λ = (d-2)/2`, with `σ` the normalized surface measure, the zonal convolution
  `𝒦_h Y_n(x) = ∫ h(x·y) Y_n(y) dσ(y)` acts on a degree-`n` spherical harmonic by
  `η_n(h) = (1/C_n^λ(1)) ∫ h C_n^λ dν_λ`.
  Mathlib has neither spherical harmonics nor the Funk–Hecke theorem; the
  classical Funk–Hecke formula, with its usual multiplier
  `ω_{d-2}/(ω_{d-1} C_n^λ(1)) ∫_{-1}^1 h(u) C_n^λ(u) (1-u²)^{λ-1/2} du`, enters as the explicit
  hypothesis `FunkHeckeFormula d`. What is proved is the manuscript's own content: the
  sphere-area ratio `ω_{d-2}/ω_{d-1}` equals `c_λ = Γ(λ+1)/(√π Γ(λ+1/2))`
  (`sphereArea_ratio`), hence the classical multiplier equals `η_n(h)` written with the
  library's `ν_λ` (`classicalMultiplier_eq_eta`).
* **Eq. (d4-bessel)** (`eq_d4_bessel`). `Φ_1(z) = ∑ (-1)ⁿ C_n z^{2n}/(4ⁿ (2n)!)` for every
  `z ∈ ℂ` (`C_n = binom(2n,n)/(n+1)` = `catalanC n`), `Φ_1(0) = 1`, `Φ_1` entire, and
  `Φ_1(t) = 2 J_1(t)/t` for real `t > 0` (`J_1` the library's power-series Bessel function).
  The coefficients are `(-1)ⁿ m_{2n}(1)/(2n)!` with the Catalan moments `m_{2n}(1) = C_n/4ⁿ`
  (`d4_coeff_eq_moment`).
* **Eq. (gegen-resolvent)** (`eq_gegen_resolvent`). The library resolvent
  `R_{λ,t} = sturmRealPositiveResolventFullCLM λ t` is `(D_λ + tI)⁻¹` with `D_λ = -A ≥ 0`,
  `A` the closed Sturm operator (eigenvalues `-n(n+2λ)`), and
  `R_{λ,t} P_n = (1/(t + n(n+2λ))) P_n` for every `n` and `t > 0`.
-/

noncomputable section

open MeasureTheory Set Complex Polynomial

namespace GegenbauerFock.Section10Comparison

open GegenbauerFock.Manuscript13 (ν Φ cl besselJ)

/-! ## Proposition 10.1 (normalized Funk–Hecke angular multiplier) -/

/-- The ambient space `ℝ^d`. -/
abbrev Eucl (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- The unit sphere `S^{d-1} ⊂ ℝ^d`. -/
abbrev Sph (d : ℕ) : Type := Metric.sphere (0 : Eucl d) 1

/-- Normalized surface measure `σ` on `S^{d-1}`, as a measure on `ℝ^d` carried by the sphere:
the radial projection `y ↦ y/‖y‖` of normalized Lebesgue measure on the unit ball (the classical
cone-measure description, `σ(A) = |{r a : 0 < r < 1, a ∈ A}| / |B|`). -/
def sigma (d : ℕ) : Measure (Eucl d) :=
  ((volume : Measure (Eucl d)) (Metric.ball 0 1))⁻¹ •
    Measure.map (fun y : Eucl d => ‖y‖⁻¹ • y)
      ((volume : Measure (Eucl d)).restrict (Metric.ball 0 1))

theorem measurable_radial (d : ℕ) : Measurable (fun y : Eucl d => ‖y‖⁻¹ • y) :=
  (measurable_norm.inv).smul measurable_id

/-- `σ` is a probability measure. -/
theorem sigma_isProbability (d : ℕ) : IsProbabilityMeasure (sigma d) := by
  have hball : (volume : Measure (Eucl d)) (Metric.ball 0 1) ≠ 0 := by
    first
    | exact (Metric.measure_ball_pos volume (0 : Eucl d) one_pos).ne'
    | exact (measure_ball_pos volume (0 : Eucl d) one_pos).ne'
  have htop : (volume : Measure (Eucl d)) (Metric.ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  constructor
  rw [sigma, Measure.smul_apply, smul_eq_mul, Measure.map_apply (measurable_radial d)
    MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hball htop

/-- `Y` is a (complex) solid spherical harmonic of degree `n` in `d` variables: `Y` is given by a
polynomial `P` that is homogeneous of degree `n` and harmonic (`∑ᵢ ∂ᵢ² P = 0`). Its restriction
to `S^{d-1}` is a degree-`n` spherical harmonic (only these values enter, since `σ` is carried by
the sphere). -/
def IsSphericalHarmonic (d n : ℕ) (Y : Eucl d → ℂ) : Prop :=
  ∃ P : MvPolynomial (Fin d) ℂ,
    (∀ m : Fin d →₀ ℕ, P.coeff m ≠ 0 → (∑ i : Fin d, m i) = n) ∧
    (∑ i : Fin d, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 ∧
    ∀ y : Eucl d, Y y = MvPolynomial.eval (fun i => ((EuclideanSpace.proj i y : ℝ) : ℂ)) P

/-- Constants are spherical harmonics of degree `0` (the class is not empty). -/
theorem isSphericalHarmonic_const (d : ℕ) (c : ℂ) :
    IsSphericalHarmonic d 0 (fun _ => c) := by
  refine ⟨MvPolynomial.C c, fun m hm => ?_, ?_, fun y => ?_⟩
  · rw [MvPolynomial.coeff_C] at hm
    by_cases h0 : 0 = m
    · rw [← h0]
      exact Finset.sum_eq_zero fun i _ => rfl
    · exact absurd (if_neg h0) hm
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [MvPolynomial.pderiv_C, map_zero]
  · rw [MvPolynomial.eval_C]

/-- The zonal convolution `(𝒦_h Y)(x) = ∫ h(x·y) Y(y) dσ(y)` (eq:funk-operator). -/
def zonalConv (d : ℕ) (h : ℝ → ℂ) (Y : Eucl d → ℂ) (x : Sph d) : ℂ :=
  ∫ y, h (inner ℝ (x : Eucl d) y) * Y y ∂(sigma d)

/-- `λ = (d-2)/2`. -/
def lamOf (d : ℕ) : ℝ := ((d : ℝ) - 2) / 2

/-- `ω_m = 2π^{(m+1)/2}/Γ((m+1)/2)`, the area of `S^m ⊂ ℝ^{m+1}`. -/
def sphereArea (m : ℕ) : ℝ :=
  2 * Real.pi ^ (((m : ℝ) + 1) / 2) / Real.Gamma (((m : ℝ) + 1) / 2)

/-- The classical Gegenbauer polynomial `C_n^λ`: the library's monic Gegenbauer eigenpolynomial
scaled by the classical leading coefficient `2ⁿ (λ)_n / n!`. -/
def gegenbauerC (lam : ℝ) (n : ℕ) : ℝ[X] :=
  Polynomial.C ((2 : ℝ) ^ n * (ascPochhammer ℝ n).eval lam / (n.factorial : ℝ)) *
    Ultraspherical.sturmMonicEigenCandidate lam n

/-- `C_n^λ` solves the Gegenbauer equation `(1-x²)y'' - (2λ+1)x y' = -n(n+2λ) y`. -/
theorem gegenbauerC_eigen (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    Ultraspherical.sturmPolynomial lam (gegenbauerC lam n) =
      Ultraspherical.sturmEigenvalue lam n • gegenbauerC lam n := by
  unfold gegenbauerC
  rw [← Polynomial.smul_eq_C_mul, Ultraspherical.sturmPolynomial_smul,
    Ultraspherical.sturmMonicEigenCandidate_eigen lam hlam n, smul_comm]

/-- The classical Funk–Hecke multiplier
`ω_{d-2}/(ω_{d-1} C_n^λ(1)) ∫_{-1}^1 h(u) C_n^λ(u) (1-u²)^{λ-1/2} du`. -/
def classicalMultiplier (d n : ℕ) (h : ℝ → ℂ) : ℂ :=
  ((sphereArea (d - 2) / (sphereArea (d - 1) * (gegenbauerC (lamOf d) n).eval 1) : ℝ) : ℂ) *
    ∫ u in (-1 : ℝ)..1, h u * (((gegenbauerC (lamOf d) n).eval u : ℝ) : ℂ) *
      (((1 - u ^ 2) ^ (lamOf d - 1 / 2) : ℝ) : ℂ)

/-- The normalized multiplier `η_n(h) = (1/C_n^λ(1)) ∫ h C_n^λ dν_λ` (eq:funk-hecke). -/
def eta (lam : ℝ) (n : ℕ) (h : ℝ → ℂ) : ℂ :=
  (((gegenbauerC lam n).eval 1 : ℝ) : ℂ)⁻¹ * ∫ u, h u * (((gegenbauerC lam n).eval u : ℝ) : ℂ) ∂(ν lam)

/-- **Classical Funk–Hecke formula** (Funk 1916, Hecke 1918), as an explicit hypothesis:
for `d ≥ 3`, every `h` integrable against `ν_λ` (i.e. against `(1-u²)^{λ-1/2} du` on `[-1,1]`)
and every degree-`n` spherical harmonic `Y`,
`∫ h(x·y) Y(y) dσ(y) = [ω_{d-2}/(ω_{d-1} C_n^λ(1)) ∫_{-1}^1 h C_n^λ (1-u²)^{λ-1/2} du] Y(x)`. -/
def FunkHeckeFormula (d : ℕ) : Prop :=
  3 ≤ d → ∀ (n : ℕ) (h : ℝ → ℂ) (Y : Eucl d → ℂ), Integrable h (ν (lamOf d)) →
    IsSphericalHarmonic d n Y → ∀ x : Sph d, zonalConv d h Y x = classicalMultiplier d n h * Y (x : Eucl d)

theorem lamOf_pos (d : ℕ) (hd : 3 ≤ d) : 0 < lamOf d := by
  have : (3 : ℝ) ≤ d := by exact_mod_cast hd
  unfold lamOf
  linarith

/-- The sphere-area ratio is the normalizing constant of `ν_λ`:
`ω_{d-2}/ω_{d-1} = Γ(λ+1)/(√π Γ(λ+1/2)) = c_λ`, `λ = (d-2)/2`. -/
theorem sphereArea_ratio (d : ℕ) (hd : 3 ≤ d) :
    sphereArea (d - 2) / sphereArea (d - 1) = cl (lamOf d) := by
  have hl := lamOf_pos d hd
  have h2 : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ d)]; norm_num
  have h1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]; norm_num
  have ea : (((d - 2 : ℕ) : ℝ) + 1) / 2 = lamOf d + 1 / 2 := by
    rw [h2]; unfold lamOf; ring
  have eb : (((d - 1 : ℕ) : ℝ) + 1) / 2 = lamOf d + 1 := by
    rw [h1]; unfold lamOf; ring
  have hp : Real.pi ^ (lamOf d + 1) = Real.pi ^ (lamOf d + 1 / 2) * Real.sqrt Real.pi := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos]
    congr 1
    ring
  unfold sphereArea cl
  rw [ea, eb, hp]
  have ha : 0 < Real.pi ^ (lamOf d + 1 / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have g1 : 0 < Real.Gamma (lamOf d + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have g2 : 0 < Real.Gamma (lamOf d + 1) := Real.Gamma_pos_of_pos (by linarith)
  have h2a : (2 * Real.pi ^ (lamOf d + 1 / 2)) / (2 * Real.pi ^ (lamOf d + 1 / 2)) = 1 :=
    div_self (by positivity)
  rw [div_div_eq_mul_div]
  calc 2 * Real.pi ^ (lamOf d + 1 / 2) / Real.Gamma (lamOf d + 1 / 2) * Real.Gamma (lamOf d + 1) /
        (2 * (Real.pi ^ (lamOf d + 1 / 2) * Real.sqrt Real.pi))
      = Real.Gamma (lamOf d + 1) / (Real.sqrt Real.pi * Real.Gamma (lamOf d + 1 / 2)) *
          ((2 * Real.pi ^ (lamOf d + 1 / 2)) / (2 * Real.pi ^ (lamOf d + 1 / 2))) := by
        ring
    _ = Real.Gamma (lamOf d + 1) / (Real.sqrt Real.pi * Real.Gamma (lamOf d + 1 / 2)) := by
        rw [h2a, mul_one]

/-- The classical Funk–Hecke multiplier equals `η_n(h)` written with the library's `ν_λ`. -/
theorem classicalMultiplier_eq_eta (d : ℕ) (hd : 3 ≤ d) (n : ℕ) (h : ℝ → ℂ) :
    classicalMultiplier d n h = eta (lamOf d) n h := by
  have hl : -1 / 2 < lamOf d := by have := lamOf_pos d hd; linarith
  set c1 : ℝ := (gegenbauerC (lamOf d) n).eval 1 with hc1
  have hconst : sphereArea (d - 2) / (sphereArea (d - 1) * c1) = cl (lamOf d) * c1⁻¹ := by
    rw [← div_div, sphereArea_ratio d hd, div_eq_mul_inv]
  have hint : (∫ u, h u * (((gegenbauerC (lamOf d) n).eval u : ℝ) : ℂ) ∂(ν (lamOf d))) =
      ∫ u in (-1 : ℝ)..1, ((cl (lamOf d) * (1 - u ^ 2) ^ (lamOf d - 1 / 2) : ℝ) : ℂ) *
        (h u * (((gegenbauerC (lamOf d) n).eval u : ℝ) : ℂ)) :=
    Manuscript13.integral_ν hl _
  have hpull : (∫ u in (-1 : ℝ)..1, ((cl (lamOf d) * (1 - u ^ 2) ^ (lamOf d - 1 / 2) : ℝ) : ℂ) *
        (h u * (((gegenbauerC (lamOf d) n).eval u : ℝ) : ℂ))) =
      (cl (lamOf d) : ℂ) * ∫ u in (-1 : ℝ)..1, h u * (((gegenbauerC (lamOf d) n).eval u : ℝ) : ℂ) *
        (((1 - u ^ 2) ^ (lamOf d - 1 / 2) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext u
    rw [Complex.ofReal_mul]
    ring
  unfold classicalMultiplier eta
  rw [← hc1, hconst, hint, hpull, Complex.ofReal_mul, Complex.ofReal_inv]
  ring

/-- **Proposition 10.1** (`prop:funk-hecke`). Under the classical Funk–Hecke formula, for
`d ≥ 3`, `h` integrable against `ν_λ` and `Y` a degree-`n` spherical harmonic,
`𝒦_h Y = η_n(h) Y` with `η_n(h) = (1/C_n^λ(1)) ∫ h C_n^λ dν_λ`, `λ = (d-2)/2`. -/
theorem proposition_10_1 (d : ℕ) (hd : 3 ≤ d) (hFH : FunkHeckeFormula d)
    (n : ℕ) (h : ℝ → ℂ) (hh : Integrable h (ν (lamOf d)))
    (Y : Eucl d → ℂ) (hY : IsSphericalHarmonic d n Y) :
    zonalConv d h Y = fun x : Sph d => eta (lamOf d) n h * Y (x : Eucl d) := by
  funext x
  rw [hFH hd n h Y hh hY x, classicalMultiplier_eq_eta d hd n h]

/-! ## Eq. (d4-bessel): the four-dimensional Gegenbauer–Bessel specialization -/

/-- The Catalan numbers of (catalan-numbers), `C_n = binom(2n,n)/(n+1)` (an exact division). -/
def catalanC (n : ℕ) : ℕ := Nat.centralBinom n / (n + 1)

theorem succ_mul_catalanC (n : ℕ) : (n + 1) * catalanC n = Nat.centralBinom n :=
  Nat.mul_div_cancel' (Nat.succ_dvd_centralBinom n)

/-- `(2n)! = C_n · n! · (n+1)!`. -/
theorem factorial_two_mul_eq_catalan (n : ℕ) :
    (2 * n).factorial = catalanC n * (n.factorial * (n + 1).factorial) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 2 * n - n = n by omega] at h1
  have h2 := succ_mul_catalanC n
  rw [Nat.centralBinom_eq_two_mul_choose] at h2
  rw [← h1, ← h2, Nat.factorial_succ]
  ring

theorem catalan_pos' (n : ℕ) : 0 < catalanC n := by
  have h2 := succ_mul_catalanC n
  have h3 := Nat.centralBinom_pos n
  rcases Nat.eq_zero_or_pos (catalanC n) with h | h
  · rw [h, mul_zero] at h2; omega
  · exact h

/-- The Catalan coefficient is `(-1)ⁿ m_{2n}(1)/(2n)!`, with the certified Catalan moments
`m_{2n}(1) = ∫ u^{2n} dν_1 = C_n/4ⁿ` (Proposition 3.6). -/
theorem d4_coeff_eq_moment (n : ℕ) :
    (-1 : ℂ) ^ n * (catalanC n : ℂ) / (4 ^ n * ((2 * n).factorial : ℂ)) =
      (-1 : ℂ) ^ n * (∫ u, ((u ^ (2 * n) : ℝ) : ℂ) ∂(ν 1)) / ((2 * n).factorial : ℂ) := by
  rw [Manuscript13.moment_one n]
  have hcat : ((catalanC n : ℝ)) = (Nat.choose (2 * n) n : ℝ) / (n + 1) := by
    have h2 := succ_mul_catalanC n
    rw [Nat.centralBinom_eq_two_mul_choose] at h2
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [eq_div_iff hn]
    exact_mod_cast (by rw [mul_comm]; exact h2)
  rw [← hcat]
  first
  | (push_cast; done)
  | (push_cast; ring)

/-- **Eq. (d4-bessel)**, `d = 4`, `λ = 1`:
`Φ_1(z) = ∑_{n≥0} (-1)ⁿ C_n z^{2n}/(4ⁿ (2n)!)` for every `z ∈ ℂ`, `Φ_1(0) = 1`, `Φ_1` is entire,
and `Φ_1(t) = 2 J_1(t)/t` for real `t > 0`. -/
theorem eq_d4_bessel :
    (∀ z : ℂ, HasSum (fun n : ℕ => (-1 : ℂ) ^ n * (catalanC n : ℂ) /
        (4 ^ n * ((2 * n).factorial : ℂ)) * z ^ (2 * n)) (Φ 1 z)) ∧
      Φ 1 0 = 1 ∧ Differentiable ℂ (Φ 1) ∧
      ∀ t : ℝ, 0 < t → Φ 1 t = ((2 * GegenbauerFock.Manuscript13.besselJ 1 t / t : ℝ) : ℂ) := by
  refine ⟨fun z => ?_, Manuscript13.Phi_zero (by norm_num), ?_, fun t ht => ?_⟩
  · have hs := Manuscript13.Phi_hasSum (l := 1) (by norm_num) z
    convert hs using 1
    funext n
    rw [show (1 : ℝ) + 1 = 2 by norm_num, Manuscript13.pochhammer_two n,
      factorial_two_mul_eq_catalan n]
    have hc : (catalanC n : ℂ) ≠ 0 := by exact_mod_cast (catalan_pos' n).ne'
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    have hf' : ((n + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (n + 1)).ne'
    have h4 : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [div_pow, ← pow_mul]
    push_cast
    first
    | (field_simp; done)
    | (field_simp; ring)
  · have h := Section3.Phi_differentiable 1 one_pos
    first
    | exact h
    | (intro z; exact h z)
  · rw [Manuscript13.Phi_bessel (by norm_num) ht]
    congr 1
    have hG : Real.Gamma (1 + 1) = 1 := by
      rw [Real.Gamma_add_one one_ne_zero, Real.Gamma_one, mul_one]
    rw [hG, Real.rpow_one]
    ring

/-! ## Eq. (gegen-resolvent): the diagonal Gegenbauer resolvent -/

open Ultraspherical in
/-- **Sign convention**: the library resolvent is `(D_λ + tI)⁻¹` with `D_λ = -A`, `A` the
closed Sturm operator (`A P_n = -n(n+2λ) P_n`): it is a two-sided inverse of `D_λ + tI` on
`Dom A`. -/
theorem resolvent_inverts_D_add_t (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    (∀ x : (sturmRealPartialOperator lam hlam).closure.domain,
      sturmRealPositiveResolventFullCLM lam t hlam ht
        (-((sturmRealPartialOperator lam hlam).closure x) + t • (x : Lp ℝ 2 (measure lam))) =
        (x : Lp ℝ 2 (measure lam))) ∧
    ∀ f : Lp ℝ 2 (measure lam), ∃ y : (sturmRealPartialOperator lam hlam).closure.domain,
      (y : Lp ℝ 2 (measure lam)) = sturmRealPositiveResolventFullCLM lam t hlam ht f ∧
        -((sturmRealPartialOperator lam hlam).closure y) + t • (y : Lp ℝ 2 (measure lam)) = f := by
  refine ⟨fun x => ?_, fun f => ?_⟩
  · rw [neg_add_eq_sub]
    exact sturmRealPositiveResolventFullCLM_left_inverse_closed_shift lam t hlam ht x
  · obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).mp
      (sturmRealPositiveResolventFullCLM_closed_graph lam t hlam ht f)
    have hy1' : (y : Lp ℝ 2 (measure lam)) = sturmRealPositiveResolventFullCLM lam t hlam ht f :=
      hy1
    have hy2' : (sturmRealPartialOperator lam hlam).closure y =
        t • sturmRealPositiveResolventFullCLM lam t hlam ht f - f := hy2
    refine ⟨y, hy1', ?_⟩
    rw [hy2', hy1', neg_sub, sub_add_cancel]

open Ultraspherical in
/-- `P_n ∈ Dom A` with `D_λ P_n = -A P_n = n(n+2λ) P_n` (normalized library eigenmode). -/
theorem gegen_mode_eigen (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    ∃ y : (sturmRealPartialOperator lam hlam).closure.domain,
      (y : Lp ℝ 2 (measure lam)) = sturmMonicEigenCandidate_realL2_normalized lam hlam n ∧
        -((sturmRealPartialOperator lam hlam).closure y) =
          ((n : ℝ) * ((n : ℝ) + 2 * lam)) • (y : Lp ℝ 2 (measure lam)) := by
  obtain ⟨x, hx, hAx⟩ := sturmMonicEigenCandidate_closed_domain_eigen lam hlam n
  refine ⟨(‖(x : Lp ℝ 2 (measure lam))‖)⁻¹ • x, ?_, ?_⟩
  · change (‖(x : Lp ℝ 2 (measure lam))‖)⁻¹ • (x : Lp ℝ 2 (measure lam)) = _
    rw [hx]
    rfl
  · have he : sturmEigenvalue lam n = -((n : ℝ) * ((n : ℝ) + 2 * lam)) := by
      unfold sturmEigenvalue
      ring
    rw [LinearPMap.map_smul, hAx, Submodule.coe_smul, he, neg_smul, smul_neg, neg_neg,
      smul_comm]

open Ultraspherical in
/-- **Eq. (gegen-resolvent)**: `R_{λ,t} P_n = (1/(t + n(n+2λ))) P_n` for every `n` and `t > 0`,
`R_{λ,t} = (D_λ + tI)⁻¹` the library's full-L² resolvent and `P_n` the normalized Gegenbauer
eigenmode. -/
theorem eq_gegen_resolvent (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    sturmRealPositiveResolventFullCLM lam t hlam ht
        (sturmMonicEigenCandidate_realL2_normalized lam hlam n) =
      (1 / (t + (n : ℝ) * ((n : ℝ) + 2 * lam))) •
        sturmMonicEigenCandidate_realL2_normalized lam hlam n := by
  rw [one_div]
  exact sturmMonicEigenCandidate_realL2_normalized_resolvent_diagonal lam t hlam ht n

end GegenbauerFock.Section10Comparison

#print axioms GegenbauerFock.Section10Comparison.sigma_isProbability
#print axioms GegenbauerFock.Section10Comparison.isSphericalHarmonic_const
#print axioms GegenbauerFock.Section10Comparison.gegenbauerC_eigen
#print axioms GegenbauerFock.Section10Comparison.sphereArea_ratio
#print axioms GegenbauerFock.Section10Comparison.classicalMultiplier_eq_eta
#print axioms GegenbauerFock.Section10Comparison.proposition_10_1
#print axioms GegenbauerFock.Section10Comparison.d4_coeff_eq_moment
#print axioms GegenbauerFock.Section10Comparison.eq_d4_bessel
#print axioms GegenbauerFock.Section10Comparison.resolvent_inverts_D_add_t
#print axioms GegenbauerFock.Section10Comparison.gegen_mode_eigen
#print axioms GegenbauerFock.Section10Comparison.eq_gegen_resolvent
