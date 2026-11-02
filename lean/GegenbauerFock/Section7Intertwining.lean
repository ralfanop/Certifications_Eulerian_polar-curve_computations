import GegenbauerFock.GegenbauerIntrinsicEntireBochnerEvaluation
import GegenbauerFock.GaussianAreaTaylorUniqueness
import GegenbauerFock.UltrasphericalSturmLiouvilleActualMoments
import GegenbauerFock.GaussianAreaNormalizedBasis
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Manuscript 13, Section 7 — the Fock-side differential operator and the intertwining

* Definition 7.1: the second-order operator
  `(𝒟_λ F)(z) = z² F''(z) + (2λ+1) z F'(z) + (z²/4) F(z)` on functions `ℂ → ℂ`.
* The Gegenbauer operator `D_λ p = −(1−u²) p'' + (2λ+1) u p'` on complex polynomials.
* Theorem 7.2: for every complex polynomial `p`, the entire representative of
  `C_{λ,α} p` is carried by `𝒟_λ` to the entire representative of `C_{λ,α}(D_λ p)`,
  pointwise at every `z ∈ ℂ`.
* Proposition 7.5: the ladder form of `𝒟_λ` and its action on the normalized
  Gaussian monomials `e_n`.

Proof of Theorem 7.2 (no integration by parts): the entire representative of
`C_{λ,α} p` is the Fourier–Bochner integral `G₀(z) = ∫ p(u) e^{izu/2} dν_λ`;
differentiation under the integral sign gives all its Taylor coefficients at `0`
in terms of the moments `M_n(p) = ∫ uⁿ p(u) dν_λ`; the moment identity
`M_n(D_λ p) = n(n+2λ) M_n(p) − n(n−1) M_{n−2}(p)` follows from the certified
two-step moment recurrence `(s+2λ) m_s = (s−1) m_{s−2}` of `ν_λ`; Taylor uniqueness
for entire functions concludes.
-/

noncomputable section

open MeasureTheory Polynomial Metric

namespace GegenbauerFock.Section7Intertwining

/-! ## Definitions -/

/-- Definition 7.1: the Fock-side operator
`(𝒟_λ F)(z) = z² F''(z) + (2λ+1) z F'(z) + (z²/4) F(z)`. -/
def fockDiff (lam : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  z ^ 2 * deriv (deriv F) z + ((2 * lam + 1 : ℝ) : ℂ) * z * deriv F z +
    z ^ 2 / 4 * F z

/-- The Gegenbauer operator `D_λ p = −(1−u²) p'' + (2λ+1) u p'` on `ℂ[X]`. -/
def gegenDiff (lam : ℝ) (p : ℂ[X]) : ℂ[X] :=
  -((1 - X ^ 2) * derivative (derivative p)) +
    C ((2 * lam + 1 : ℝ) : ℂ) * X * derivative p

/-- Annihilation operator `a_α = α^{-1/2} ∂_z`. -/
def aOp (alpha : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((Real.sqrt alpha : ℝ) : ℂ)⁻¹ * deriv F z

/-- Creation operator `a_α† = √α z`. -/
def aDag (alpha : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((Real.sqrt alpha : ℝ) : ℂ) * z * F z

/-! ## Boundedness and integrability on the support `[-1,1]` -/

theorem bounded_continuous_ae (lam : ℝ) (g : ℝ → ℂ) (hg : Continuous g) :
    ∃ B : ℝ, ∀ᵐ u ∂(Ultraspherical.measure lam), ‖g u‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨B, ?_⟩
  filter_upwards [GeneralUltrasphericalFock.ae_abs_le_one lam] with u hu
  exact hB u ⟨(abs_le.mp hu).1, (abs_le.mp hu).2⟩

theorem integrable_of_continuous (lam : ℝ) (hlam : 0 < lam) (g : ℝ → ℂ)
    (hg : Continuous g) : Integrable g (Ultraspherical.measure lam) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  obtain ⟨B, hB⟩ := bounded_continuous_ae lam g hg
  exact Integrable.of_bound hg.aestronglyMeasurable B hB

theorem continuous_eval_ofReal (p : ℂ[X]) :
    Continuous (fun u : ℝ => p.eval (u : ℂ)) :=
  p.continuous.comp Complex.continuous_ofReal

/-- Every complex polynomial is in `L²(ν_λ)` (bounded on the support `[-1,1]`). -/
theorem poly_memLp (lam : ℝ) (hlam : 0 < lam) (p : ℂ[X]) :
    MemLp (fun u : ℝ => p.eval (u : ℂ)) 2 (Ultraspherical.measure lam) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  obtain ⟨B, hB⟩ := bounded_continuous_ae lam _ (continuous_eval_ofReal p)
  exact MemLp.of_bound (continuous_eval_ofReal p).aestronglyMeasurable B hB

/-- The `L²(ν_λ)` class of `u ↦ p(u)`. -/
def polyLp (lam : ℝ) (hlam : 0 < lam) (p : ℂ[X]) : Lp ℂ 2 (Ultraspherical.measure lam) :=
  (poly_memLp lam hlam p).toLp (fun u : ℝ => p.eval (u : ℂ))

theorem polyLp_ae (lam : ℝ) (hlam : 0 < lam) (p : ℂ[X]) :
    (polyLp lam hlam p : ℝ → ℂ) =ᵐ[Ultraspherical.measure lam]
      (fun u : ℝ => p.eval (u : ℂ)) :=
  (poly_memLp lam hlam p).coeFn_toLp

/-! ## Moments -/

/-- `M_n(p) = ∫ uⁿ p(u) dν_λ`. -/
def mom (lam : ℝ) (p : ℂ[X]) (n : ℕ) : ℂ :=
  ∫ u : ℝ, (u : ℂ) ^ n * p.eval (u : ℂ) ∂(Ultraspherical.measure lam)

/-- The real moment `m_j = ∫ u^j dν_λ`, cast to `ℂ`. -/
def cm (lam : ℝ) (j : ℕ) : ℂ := ((Ultraspherical.sturmMoment lam j : ℝ) : ℂ)

theorem integral_cpow (lam : ℝ) (j : ℕ) :
    ∫ u : ℝ, (u : ℂ) ^ j ∂(Ultraspherical.measure lam) = cm lam j := by
  have h : (fun u : ℝ => (u : ℂ) ^ j) = fun u : ℝ => ((u ^ j : ℝ) : ℂ) := by
    funext u
    rw [Complex.ofReal_pow]
  rw [h, integral_complex_ofReal]
  rfl

theorem integral_two (lam : ℝ) (hlam : 0 < lam) (A B : ℂ) (i j : ℕ) :
    ∫ u : ℝ, (A * (u : ℂ) ^ i + B * (u : ℂ) ^ j) ∂(Ultraspherical.measure lam) =
      A * cm lam i + B * cm lam j := by
  have hi : Integrable (fun u : ℝ => A * (u : ℂ) ^ i) (Ultraspherical.measure lam) :=
    integrable_of_continuous lam hlam _
      (continuous_const.mul (Complex.continuous_ofReal.pow i))
  have hj : Integrable (fun u : ℝ => B * (u : ℂ) ^ j) (Ultraspherical.measure lam) :=
    integrable_of_continuous lam hlam _
      (continuous_const.mul (Complex.continuous_ofReal.pow j))
  rw [integral_add hi hj, integral_const_mul, integral_const_mul, integral_cpow,
    integral_cpow]

theorem cm_rec (lam : ℝ) (hlam : 0 < lam) (j : ℕ) :
    ((j : ℂ) + 2 + 2 * (lam : ℂ)) * cm lam (j + 2) = ((j : ℂ) + 1) * cm lam j := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) (Ultraspherical.sturmMoment_two_step lam hlam j)
  push_cast at h
  unfold cm
  linear_combination h

theorem cm_one (lam : ℝ) (hlam : 0 < lam) : cm lam 1 = 0 := by
  have h1 : Ultraspherical.sturmMoment lam 1 = Ultraspherical.oddMoment lam 0 :=
    Ultraspherical.sturmMoment_odd lam 0
  unfold cm
  rw [h1, Ultraspherical.oddMoment_eq_zero lam hlam 0, Complex.ofReal_zero]

theorem mom_add (lam : ℝ) (hlam : 0 < lam) (p q : ℂ[X]) (n : ℕ) :
    mom lam (p + q) n = mom lam p n + mom lam q n := by
  unfold mom
  have hp : Integrable (fun u : ℝ => (u : ℂ) ^ n * p.eval (u : ℂ))
      (Ultraspherical.measure lam) :=
    integrable_of_continuous lam hlam _
      ((Complex.continuous_ofReal.pow n).mul (continuous_eval_ofReal p))
  have hq : Integrable (fun u : ℝ => (u : ℂ) ^ n * q.eval (u : ℂ))
      (Ultraspherical.measure lam) :=
    integrable_of_continuous lam hlam _
      ((Complex.continuous_ofReal.pow n).mul (continuous_eval_ofReal q))
  rw [← integral_add hp hq]
  have hfun : (fun u : ℝ => (u : ℂ) ^ n * (p + q).eval (u : ℂ)) =
      fun u : ℝ => (u : ℂ) ^ n * p.eval (u : ℂ) + (u : ℂ) ^ n * q.eval (u : ℂ) := by
    funext u
    rw [eval_add]
    ring
  rw [hfun]

theorem mom_C_mul (lam : ℝ) (a : ℂ) (q : ℂ[X]) (n : ℕ) :
    mom lam (C a * q) n = a * mom lam q n := by
  unfold mom
  have hfun : (fun u : ℝ => (u : ℂ) ^ n * (C a * q).eval (u : ℂ)) =
      fun u : ℝ => a * ((u : ℂ) ^ n * q.eval (u : ℂ)) := by
    funext u
    rw [eval_mul, eval_C]
    ring
  rw [hfun, integral_const_mul]

theorem mom_zero_poly (lam : ℝ) (n : ℕ) : mom lam 0 n = 0 := by
  unfold mom
  have hfun : (fun u : ℝ => (u : ℂ) ^ n * (0 : ℂ[X]).eval (u : ℂ)) = fun _ => (0 : ℂ) := by
    funext u
    rw [eval_zero, mul_zero]
  rw [hfun, integral_zero]

theorem mom_X_pow (lam : ℝ) (k n : ℕ) : mom lam (X ^ k) n = cm lam (n + k) := by
  unfold mom
  have hfun : (fun u : ℝ => (u : ℂ) ^ n * (X ^ k : ℂ[X]).eval (u : ℂ)) =
      fun u : ℝ => (u : ℂ) ^ (n + k) := by
    funext u
    rw [eval_pow, eval_X, pow_add]
  rw [hfun, integral_cpow]

/-! ## The Gegenbauer operator on monomials -/

theorem gegenDiff_add (lam : ℝ) (p q : ℂ[X]) :
    gegenDiff lam (p + q) = gegenDiff lam p + gegenDiff lam q := by
  unfold gegenDiff
  rw [derivative_add, derivative_add]
  ring

theorem gegenDiff_C_mul (lam : ℝ) (a : ℂ) (q : ℂ[X]) :
    gegenDiff lam (C a * q) = C a * gegenDiff lam q := by
  unfold gegenDiff
  rw [derivative_C_mul, derivative_C_mul]
  ring

theorem mom_gegenDiff_X_pow (lam : ℝ) (hlam : 0 < lam) (k n : ℕ) :
    mom lam (gegenDiff lam (X ^ k)) n =
      (n : ℂ) * ((n : ℂ) + 2 * (lam : ℂ)) * mom lam (X ^ k) n -
        (n : ℂ) * ((n : ℂ) - 1) * mom lam (X ^ k) (n - 2) := by
  rw [mom_X_pow, mom_X_pow]
  match k with
  | 0 =>
    have hg : gegenDiff lam (X ^ 0) = 0 := by
      unfold gegenDiff
      rw [pow_zero, derivative_one, derivative_zero]
      ring
    rw [hg, mom_zero_poly]
    match n with
    | 0 =>
      rw [Nat.cast_zero]
      ring
    | 1 =>
      rw [Nat.cast_one, Nat.add_zero, cm_one lam hlam]
      ring
    | m + 2 =>
      have r := cm_rec lam hlam m
      rw [show m + 2 + 0 = m + 2 by omega, show m + 2 - 2 + 0 = m by omega]
      push_cast
      linear_combination (-((m : ℂ) + 2)) * r
  | 1 =>
    have hg : gegenDiff lam (X ^ 1) = C ((2 * lam + 1 : ℝ) : ℂ) * X ^ 1 := by
      unfold gegenDiff
      rw [pow_one, derivative_X, derivative_one]
      ring
    rw [hg, mom_C_mul, mom_X_pow]
    match n with
    | 0 =>
      rw [Nat.cast_zero, Nat.zero_add, cm_one lam hlam]
      ring
    | 1 =>
      rw [Nat.cast_one]
      push_cast
      ring
    | m + 2 =>
      have r := cm_rec lam hlam (m + 1)
      rw [show m + 1 + 2 = m + 3 by omega] at r
      rw [show m + 2 + 1 = m + 3 by omega, show m + 2 - 2 + 1 = m + 1 by omega]
      push_cast at r ⊢
      linear_combination (1 - ((m : ℂ) + 2)) * r
  | j + 2 =>
    have hd1 : derivative (X ^ (j + 2) : ℂ[X]) = C (((j + 2 : ℕ) : ℂ)) * X ^ (j + 1) := by
      rw [derivative_X_pow, show j + 2 - 1 = j + 1 by omega]
    have hd2 : derivative (C (((j + 2 : ℕ) : ℂ)) * X ^ (j + 1) : ℂ[X]) =
        C (((j + 2 : ℕ) : ℂ)) * (C (((j + 1 : ℕ) : ℂ)) * X ^ j) := by
      rw [derivative_C_mul, derivative_X_pow, show j + 1 - 1 = j by omega]
    have hmom : mom lam (gegenDiff lam (X ^ (j + 2))) n =
        (-(((j : ℂ) + 2) * ((j : ℂ) + 1))) * cm lam (n + j) +
          (((j : ℂ) + 2) * ((j : ℂ) + 1) + (2 * (lam : ℂ) + 1) * ((j : ℂ) + 2)) *
            cm lam (n + j + 2) := by
      rw [← integral_two lam hlam]
      unfold mom gegenDiff
      rw [hd1, hd2]
      congr 1
      funext u
      simp only [eval_add, eval_neg, eval_mul, eval_sub, eval_one, eval_pow, eval_X,
        eval_C]
      push_cast
      ring
    rw [hmom]
    match n with
    | 0 =>
      have r := cm_rec lam hlam j
      rw [Nat.zero_add, Nat.zero_add]
      push_cast
      linear_combination ((j : ℂ) + 2) * r
    | 1 =>
      have r := cm_rec lam hlam (j + 1)
      rw [show j + 1 + 2 = j + 3 by omega] at r
      rw [show 1 + j + 2 = j + 3 by omega, show 1 + (j + 2) = j + 3 by omega,
        show 1 + j = j + 1 by omega]
      push_cast at r ⊢
      linear_combination ((j : ℂ) + 2 - 1) * r
    | m + 2 =>
      have r := cm_rec lam hlam (m + j + 2)
      rw [show m + j + 2 + 2 = m + j + 4 by omega] at r
      rw [show m + 2 + j + 2 = m + j + 4 by omega, show m + 2 + (j + 2) = m + j + 4 by omega,
        show m + 2 + j = m + j + 2 by omega, show m + 2 - 2 + (j + 2) = m + j + 2 by omega]
      push_cast at r ⊢
      linear_combination ((j : ℂ) + 2 - ((m : ℂ) + 2)) * r

/-- The moment identity `M_n(D_λ p) = n(n+2λ) M_n(p) − n(n−1) M_{n−2}(p)`
(the second term vanishes for `n < 2`). -/
theorem mom_gegenDiff (lam : ℝ) (hlam : 0 < lam) (p : ℂ[X]) (n : ℕ) :
    mom lam (gegenDiff lam p) n =
      (n : ℂ) * ((n : ℂ) + 2 * (lam : ℂ)) * mom lam p n -
        (n : ℂ) * ((n : ℂ) - 1) * mom lam p (n - 2) := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    rw [gegenDiff_add, mom_add lam hlam, mom_add lam hlam, mom_add lam hlam, hp, hq]
    ring
  · intro k a
    rw [← C_mul_X_pow_eq_monomial, gegenDiff_C_mul, mom_C_mul, mom_C_mul, mom_C_mul,
      mom_gegenDiff_X_pow lam hlam]
    ring

/-! ## The Fourier–Bochner family and differentiation under the integral -/

/-- `G_k(z) = ∫ p(u) (iu/2)^k e^{izu/2} dν_λ`. -/
def G (lam : ℝ) (p : ℂ[X]) (k : ℕ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, p.eval (u : ℂ) *
    ((Complex.I * (u : ℂ) / 2) ^ k * Complex.exp (Complex.I * z * (u : ℂ) / 2))
    ∂(Ultraspherical.measure lam)

theorem norm_kernel_le (k : ℕ) (x : ℂ) (u : ℝ) (hu : |u| ≤ 1) :
    ‖(Complex.I * (u : ℂ) / 2) ^ k * Complex.exp (Complex.I * x * (u : ℂ) / 2)‖ ≤
      Real.exp (‖x‖ / 2) := by
  have h1 : ‖Complex.I * (u : ℂ) / 2‖ ≤ 1 := by
    rw [norm_div, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_two]
    linarith [abs_nonneg u]
  have h2 : ‖(Complex.I * (u : ℂ) / 2) ^ k‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) h1
  have h3 : ‖Complex.exp (Complex.I * x * (u : ℂ) / 2)‖ ≤ Real.exp (‖x‖ / 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have h4 : ‖Complex.I * x * (u : ℂ) / 2‖ ≤ ‖x‖ / 2 := by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_two]
      have := mul_le_mul_of_nonneg_left hu (norm_nonneg x)
      linarith
    exact (Complex.re_le_norm _).trans h4
  calc
    ‖(Complex.I * (u : ℂ) / 2) ^ k * Complex.exp (Complex.I * x * (u : ℂ) / 2)‖ =
        ‖(Complex.I * (u : ℂ) / 2) ^ k‖ * ‖Complex.exp (Complex.I * x * (u : ℂ) / 2)‖ :=
      norm_mul _ _
    _ ≤ 1 * Real.exp (‖x‖ / 2) := mul_le_mul h2 h3 (norm_nonneg _) zero_le_one
    _ = Real.exp (‖x‖ / 2) := one_mul _

theorem kernel_continuous (p : ℂ[X]) (k : ℕ) (x : ℂ) :
    Continuous (fun u : ℝ => p.eval (u : ℂ) *
      ((Complex.I * (u : ℂ) / 2) ^ k * Complex.exp (Complex.I * x * (u : ℂ) / 2))) := by
  have hI : Continuous (fun u : ℝ => Complex.I * (u : ℂ) / 2) :=
    (continuous_const.mul Complex.continuous_ofReal).div_const 2
  have hE : Continuous (fun u : ℝ => Complex.exp (Complex.I * x * (u : ℂ) / 2)) :=
    Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).div_const 2)
  exact (continuous_eval_ofReal p).mul ((hI.pow k).mul hE)

theorem kernel_hasDerivAt (p : ℂ[X]) (k : ℕ) (u : ℝ) (x : ℂ) :
    HasDerivAt (fun x : ℂ => p.eval (u : ℂ) *
        ((Complex.I * (u : ℂ) / 2) ^ k * Complex.exp (Complex.I * x * (u : ℂ) / 2)))
      (p.eval (u : ℂ) *
        ((Complex.I * (u : ℂ) / 2) ^ (k + 1) *
          Complex.exp (Complex.I * x * (u : ℂ) / 2))) x := by
  have h1 : HasDerivAt (fun x : ℂ => Complex.I * x * (u : ℂ) / 2)
      (Complex.I * (u : ℂ) / 2) x :=
    ((((hasDerivAt_id' x).const_mul Complex.I).mul_const (u : ℂ)).div_const 2).congr_deriv
      (by ring)
  exact ((h1.cexp.const_mul ((Complex.I * (u : ℂ) / 2) ^ k)).const_mul
    (p.eval (u : ℂ))).congr_deriv (by ring)

/-- Differentiation under the integral sign: `G_k' = G_{k+1}` everywhere. -/
theorem G_hasDerivAt (lam : ℝ) (hlam : 0 < lam) (p : ℂ[X]) (k : ℕ) (z : ℂ) :
    HasDerivAt (G lam p k) (G lam p (k + 1) z) z := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  obtain ⟨B, hB⟩ := bounded_continuous_ae lam _ (continuous_eval_ofReal p)
  have h_bound : ∀ᵐ (u : ℝ) ∂(Ultraspherical.measure lam), ∀ x ∈ ball z 1,
      ‖p.eval (u : ℂ) * ((Complex.I * (u : ℂ) / 2) ^ (k + 1) *
        Complex.exp (Complex.I * x * (u : ℂ) / 2))‖ ≤
        B * Real.exp ((‖z‖ + 1) / 2) := by
    filter_upwards [hB, GeneralUltrasphericalFock.ae_abs_le_one lam] with u hBu hu
    intro x hx
    have hxz : ‖x‖ ≤ ‖z‖ + 1 := by
      have hd : dist x z < 1 := hx
      rw [dist_eq_norm] at hd
      have := norm_le_insert' x z
      linarith
    have hk := norm_kernel_le (k + 1) x u hu
    have hexp : Real.exp (‖x‖ / 2) ≤ Real.exp ((‖z‖ + 1) / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [norm_mul]
    exact mul_le_mul hBu (hk.trans hexp) (norm_nonneg _) ((norm_nonneg _).trans hBu)
  have h_diff : ∀ᵐ (u : ℝ) ∂(Ultraspherical.measure lam), ∀ x ∈ ball z 1,
      HasDerivAt (fun x : ℂ => p.eval (u : ℂ) *
        ((Complex.I * (u : ℂ) / 2) ^ k * Complex.exp (Complex.I * x * (u : ℂ) / 2)))
        (p.eval (u : ℂ) * ((Complex.I * (u : ℂ) / 2) ^ (k + 1) *
          Complex.exp (Complex.I * x * (u : ℂ) / 2))) x :=
    Filter.Eventually.of_forall (fun u x _ => kernel_hasDerivAt p k u x)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := Ultraspherical.measure lam)
    (F := fun (x : ℂ) (u : ℝ) => p.eval (u : ℂ) *
      ((Complex.I * (u : ℂ) / 2) ^ k * Complex.exp (Complex.I * x * (u : ℂ) / 2)))
    (F' := fun (x : ℂ) (u : ℝ) => p.eval (u : ℂ) *
      ((Complex.I * (u : ℂ) / 2) ^ (k + 1) * Complex.exp (Complex.I * x * (u : ℂ) / 2)))
    (x₀ := z) (bound := fun _ => B * Real.exp ((‖z‖ + 1) / 2)) (ε := 1) one_pos
    (Filter.Eventually.of_forall (fun x => (kernel_continuous p k x).aestronglyMeasurable))
    (integrable_of_continuous lam hlam _ (kernel_continuous p k z))
    (kernel_continuous p (k + 1) z).aestronglyMeasurable
    h_bound (integrable_const _) h_diff
  exact key.2

theorem G_deriv (lam : ℝ) (hlam : 0 < lam) (p : ℂ[X]) (k : ℕ) :
    deriv (G lam p k) = G lam p (k + 1) :=
  funext fun z => (G_hasDerivAt lam hlam p k z).deriv

theorem G_at_zero (lam : ℝ) (p : ℂ[X]) (k : ℕ) :
    G lam p k 0 = (Complex.I / 2) ^ k * mom lam p k := by
  unfold G mom
  have hfun : (fun u : ℝ => p.eval (u : ℂ) *
      ((Complex.I * (u : ℂ) / 2) ^ k * Complex.exp (Complex.I * 0 * (u : ℂ) / 2))) =
      fun u : ℝ => (Complex.I / 2) ^ k * ((u : ℂ) ^ k * p.eval (u : ℂ)) := by
    funext u
    rw [show Complex.I * 0 * (u : ℂ) / 2 = 0 by ring, Complex.exp_zero]
    ring
  rw [hfun, integral_const_mul]

/-- Pointwise Bochner identification of the entire representative of `C_{λ,α} p`. -/
theorem entireRepresentative_polyLp_eq_G (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (p : ℂ[X]) :
    GaussianArea.entireRepresentative alpha
        (GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha (polyLp lam hlam p)) =
      G lam p 0 := by
  funext z
  rw [GeneralUltrasphericalFock.C_intrinsicEntire_pointwiseBochner]
  unfold G
  apply integral_congr_ae
  filter_upwards [polyLp_ae lam hlam p] with u hu
  rw [hu, pow_zero, one_mul]

/-! ## Iterated derivatives of entire functions -/

/-- All iterated complex derivatives are differentiable. -/
def AllDiff (H : ℂ → ℂ) : Prop := ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m H)

theorem family_iteratedDeriv (Φ : ℕ → ℂ → ℂ)
    (hΦ : ∀ k z, HasDerivAt (Φ k) (Φ (k + 1) z) z) (k m : ℕ) :
    iteratedDeriv m (Φ k) = Φ (k + m) := by
  induction m with
  | zero => rw [iteratedDeriv_zero]; rfl
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    exact (hΦ (k + m) z).deriv

theorem family_allDiff (Φ : ℕ → ℂ → ℂ)
    (hΦ : ∀ k z, HasDerivAt (Φ k) (Φ (k + 1) z) z) (k : ℕ) : AllDiff (Φ k) := by
  intro m
  rw [family_iteratedDeriv Φ hΦ k m]
  exact fun z => (hΦ (k + m) z).differentiableAt

theorem iter_comb (A B Q : ℂ → ℂ) (hA : AllDiff A) (hB : AllDiff B) (hQ : AllDiff Q)
    (a b : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => A z + a * B z + b * Q z) =
      fun z => iteratedDeriv n A z + a * iteratedDeriv n B z + b * iteratedDeriv n Q z := by
  induction n with
  | zero =>
    funext z
    rw [iteratedDeriv_zero, iteratedDeriv_zero, iteratedDeriv_zero, iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    have hd : HasDerivAt
        (fun z => iteratedDeriv n A z + a * iteratedDeriv n B z + b * iteratedDeriv n Q z)
        (deriv (iteratedDeriv n A) z + a * deriv (iteratedDeriv n B) z +
          b * deriv (iteratedDeriv n Q) z) z :=
      (((hA n z).hasDerivAt.add ((hB n z).hasDerivAt.const_mul a)).add
        ((hQ n z).hasDerivAt.const_mul b))
    rw [hd.deriv, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ]

theorem allDiff_comb (A B Q : ℂ → ℂ) (hA : AllDiff A) (hB : AllDiff B) (hQ : AllDiff Q)
    (a b : ℂ) : AllDiff (fun z => A z + a * B z + b * Q z) := by
  intro m
  rw [iter_comb A B Q hA hB hQ a b m]
  exact ((hA m).add ((hB m).const_mul a)).add ((hQ m).const_mul b)

theorem iter_sub (f g : ℂ → ℂ) (hf : AllDiff f) (hg : AllDiff g) (n : ℕ) :
    iteratedDeriv n (fun z => f z - g z) = fun z => iteratedDeriv n f z - iteratedDeriv n g z := by
  induction n with
  | zero =>
    funext z
    rw [iteratedDeriv_zero, iteratedDeriv_zero, iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    have hd : HasDerivAt (fun z => iteratedDeriv n f z - iteratedDeriv n g z)
        (deriv (iteratedDeriv n f) z - deriv (iteratedDeriv n g) z) z :=
      (hf n z).hasDerivAt.sub (hg n z).hasDerivAt
    rw [hd.deriv, iteratedDeriv_succ, iteratedDeriv_succ]

theorem iter_mul_id (H : ℂ → ℂ) (hH : AllDiff H) (n : ℕ) :
    iteratedDeriv (n + 1) (fun z => z * H z) =
      fun z => z * iteratedDeriv (n + 1) H z + ((n : ℂ) + 1) * iteratedDeriv n H z := by
  have hd : ∀ k z, deriv (iteratedDeriv k H) z = iteratedDeriv (k + 1) H z := by
    intro k z
    rw [iteratedDeriv_succ]
  induction n with
  | zero =>
    have h0 : Differentiable ℂ H := by
      have := hH 0
      rwa [iteratedDeriv_zero] at this
    rw [iteratedDeriv_one]
    funext z
    have hz : HasDerivAt (fun z => z * H z) (1 * H z + z * deriv H z) z :=
      (hasDerivAt_id' z).mul (h0 z).hasDerivAt
    rw [hz.deriv, iteratedDeriv_one, iteratedDeriv_zero, Nat.cast_zero]
    ring
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    have hz : HasDerivAt
        (fun z => z * iteratedDeriv (n + 1) H z + ((n : ℂ) + 1) * iteratedDeriv n H z)
        (1 * iteratedDeriv (n + 1) H z + z * deriv (iteratedDeriv (n + 1) H) z +
          ((n : ℂ) + 1) * deriv (iteratedDeriv n H) z) z :=
      ((hasDerivAt_id' z).mul (hH (n + 1) z).hasDerivAt).add
        ((hH n z).hasDerivAt.const_mul ((n : ℂ) + 1))
    rw [hz.deriv, hd, hd]
    push_cast
    ring

theorem allDiff_mul_id (H : ℂ → ℂ) (hH : AllDiff H) : AllDiff (fun z => z * H z) := by
  intro m
  match m with
  | 0 =>
    have h0 : Differentiable ℂ H := by
      have := hH 0
      rwa [iteratedDeriv_zero] at this
    rw [iteratedDeriv_zero]
    exact fun z => differentiableAt_id.mul (h0 z)
  | n + 1 =>
    rw [iter_mul_id H hH n]
    exact (differentiable_id.mul (hH (n + 1))).add ((hH n).const_mul _)

theorem iter_mul_id_zero_succ (H : ℂ → ℂ) (hH : AllDiff H) (n : ℕ) :
    iteratedDeriv (n + 1) (fun z => z * H z) 0 = ((n : ℂ) + 1) * iteratedDeriv n H 0 := by
  rw [iter_mul_id H hH n]
  show (0 : ℂ) * iteratedDeriv (n + 1) H 0 + ((n : ℂ) + 1) * iteratedDeriv n H 0 = _
  ring

theorem iter_mul_id_zero_zero (H : ℂ → ℂ) :
    iteratedDeriv 0 (fun z => z * H z) 0 = 0 := by
  rw [iteratedDeriv_zero]
  show (0 : ℂ) * H 0 = 0
  ring

theorem iter_mul_id_zero_one (H : ℂ → ℂ) (hH : AllDiff H) :
    iteratedDeriv 1 (fun z => z * H z) 0 = H 0 := by
  have h := iter_mul_id_zero_succ H hH 0
  rw [Nat.cast_zero, zero_add (1 : ℂ), one_mul, iteratedDeriv_zero] at h
  exact h

theorem iter_sq_zero_succ_succ (H : ℂ → ℂ) (hH : AllDiff H) (n : ℕ) :
    iteratedDeriv (n + 2) (fun z => z * (z * H z)) 0 =
      ((n : ℂ) + 2) * ((n : ℂ) + 1) * iteratedDeriv n H 0 := by
  have h1 : iteratedDeriv (n + 2) (fun z => z * (z * H z)) 0 =
      (((n + 1 : ℕ) : ℂ) + 1) * iteratedDeriv (n + 1) (fun z => z * H z) 0 :=
    iter_mul_id_zero_succ (fun z => z * H z) (allDiff_mul_id H hH) (n + 1)
  rw [h1, iter_mul_id_zero_succ H hH n]
  push_cast
  ring

theorem iter_sq_zero_zero (H : ℂ → ℂ) :
    iteratedDeriv 0 (fun z => z * (z * H z)) 0 = 0 := by
  rw [iteratedDeriv_zero]
  show (0 : ℂ) * (0 * H 0) = 0
  ring

theorem iter_sq_zero_one (H : ℂ → ℂ) (hH : AllDiff H) :
    iteratedDeriv 1 (fun z => z * (z * H z)) 0 = 0 := by
  have h := iter_mul_id_zero_one (fun z => z * H z) (allDiff_mul_id H hH)
  rw [h]
  show (0 : ℂ) * H 0 = 0
  ring

/-! ## Taylor coefficients of `𝒟_λ G₀` and of `G₀(D_λ p)` -/

theorem G_family (lam : ℝ) (hlam : 0 < lam) (p : ℂ[X]) :
    ∀ k z, HasDerivAt (G lam p k) (G lam p (k + 1) z) z :=
  fun k z => G_hasDerivAt lam hlam p k z

theorem G_iter_at_zero (lam : ℝ) (hlam : 0 < lam) (p : ℂ[X]) (k m : ℕ) :
    iteratedDeriv m (G lam p k) 0 = (Complex.I / 2) ^ (k + m) * mom lam p (k + m) := by
  rw [family_iteratedDeriv (G lam p) (G_family lam hlam p) k m, G_at_zero]

theorem fockDiff_G (lam : ℝ) (hlam : 0 < lam) (p : ℂ[X]) :
    fockDiff lam (G lam p 0) = fun z => z * (z * G lam p 2 z) +
      ((2 * lam + 1 : ℝ) : ℂ) * (z * G lam p 1 z) + (1 / 4 : ℂ) * (z * (z * G lam p 0 z)) := by
  funext z
  unfold fockDiff
  rw [G_deriv lam hlam p 0, G_deriv lam hlam p 1]
  ring

theorem fockDiff_G_allDiff (lam : ℝ) (hlam : 0 < lam) (p : ℂ[X]) :
    AllDiff (fockDiff lam (G lam p 0)) := by
  rw [fockDiff_G lam hlam p]
  have hG := family_allDiff (G lam p) (G_family lam hlam p)
  exact allDiff_comb _ _ _
    (allDiff_mul_id _ (allDiff_mul_id _ (hG 2))) (allDiff_mul_id _ (hG 1))
    (allDiff_mul_id _ (allDiff_mul_id _ (hG 0))) _ _

theorem fockDiff_G_iter_at_zero (lam : ℝ) (hlam : 0 < lam) (p : ℂ[X]) (n : ℕ) :
    iteratedDeriv n (fockDiff lam (G lam p 0)) 0 =
      (Complex.I / 2) ^ n * ((n : ℂ) * ((n : ℂ) + 2 * (lam : ℂ)) * mom lam p n -
        (n : ℂ) * ((n : ℂ) - 1) * mom lam p (n - 2)) := by
  have hG := family_allDiff (G lam p) (G_family lam hlam p)
  rw [fockDiff_G lam hlam p]
  rw [iter_comb (fun z => z * (z * G lam p 2 z)) (fun z => z * G lam p 1 z)
    (fun z => z * (z * G lam p 0 z))
    (allDiff_mul_id _ (allDiff_mul_id _ (hG 2))) (allDiff_mul_id _ (hG 1))
    (allDiff_mul_id _ (allDiff_mul_id _ (hG 0)))]
  show iteratedDeriv n (fun z => z * (z * G lam p 2 z)) 0 +
      ((2 * lam + 1 : ℝ) : ℂ) * iteratedDeriv n (fun z => z * G lam p 1 z) 0 +
      (1 / 4 : ℂ) * iteratedDeriv n (fun z => z * (z * G lam p 0 z)) 0 = _
  match n with
  | 0 =>
    rw [iter_sq_zero_zero, iter_mul_id_zero_zero, iter_sq_zero_zero, Nat.cast_zero]
    ring
  | 1 =>
    rw [iter_sq_zero_one _ (hG 2), iter_mul_id_zero_one _ (hG 1), iter_sq_zero_one _ (hG 0),
      G_at_zero, Nat.cast_one]
    push_cast
    ring
  | m + 2 =>
    have hB : iteratedDeriv (m + 2) (fun z => z * G lam p 1 z) 0 =
        (((m + 1 : ℕ) : ℂ) + 1) * iteratedDeriv (m + 1) (G lam p 1) 0 :=
      iter_mul_id_zero_succ _ (hG 1) (m + 1)
    rw [iter_sq_zero_succ_succ _ (hG 2) m, hB, iter_sq_zero_succ_succ _ (hG 0) m,
      G_iter_at_zero lam hlam p 2 m, G_iter_at_zero lam hlam p 1 (m + 1),
      G_iter_at_zero lam hlam p 0 m, show 2 + m = m + 2 by omega,
      show 1 + (m + 1) = m + 2 by omega, show 0 + m = m by omega,
      show m + 2 - 2 = m by omega]
    push_cast
    linear_combination ((1 / 4 : ℂ) * ((m : ℂ) + 2) * ((m : ℂ) + 1) * (Complex.I / 2) ^ m *
      mom lam p m) * Complex.I_sq

theorem G_gegenDiff_iter_at_zero (lam : ℝ) (hlam : 0 < lam) (p : ℂ[X]) (n : ℕ) :
    iteratedDeriv n (G lam (gegenDiff lam p) 0) 0 =
      (Complex.I / 2) ^ n * ((n : ℂ) * ((n : ℂ) + 2 * (lam : ℂ)) * mom lam p n -
        (n : ℂ) * ((n : ℂ) - 1) * mom lam p (n - 2)) := by
  rw [G_iter_at_zero lam hlam (gegenDiff lam p) 0 n, Nat.zero_add, mom_gegenDiff lam hlam p n]

/-! ## Theorem 7.2 -/

/-- Fourier–Bochner form of Theorem 7.2: `𝒟_λ G₀[p] = G₀[D_λ p]` on all of `ℂ`. -/
theorem fockDiff_G_eq (lam : ℝ) (hlam : 0 < lam) (p : ℂ[X]) (z : ℂ) :
    fockDiff lam (G lam p 0) z = G lam (gegenDiff lam p) 0 z := by
  have hA := fockDiff_G_allDiff lam hlam p
  have hB := family_allDiff (G lam (gegenDiff lam p)) (G_family lam hlam (gegenDiff lam p)) 0
  have hdiff : Differentiable ℂ
      (fun z => fockDiff lam (G lam p 0) z - G lam (gegenDiff lam p) 0 z) := by
    have h0A : Differentiable ℂ (fockDiff lam (G lam p 0)) := by
      have := hA 0
      rwa [iteratedDeriv_zero] at this
    have h0B : Differentiable ℂ (G lam (gegenDiff lam p) 0) := by
      have := hB 0
      rwa [iteratedDeriv_zero] at this
    exact h0A.sub h0B
  have hzero : ∀ n : ℕ, iteratedDeriv n
      (fun z => fockDiff lam (G lam p 0) z - G lam (gegenDiff lam p) 0 z) 0 = 0 := by
    intro n
    rw [iter_sub _ _ hA hB n]
    show iteratedDeriv n (fockDiff lam (G lam p 0)) 0 -
      iteratedDeriv n (G lam (gegenDiff lam p) 0) 0 = 0
    rw [fockDiff_G_iter_at_zero lam hlam p n, G_gegenDiff_iter_at_zero lam hlam p n, sub_self]
  have hfun := GaussianArea.entireFunction_eq_zero_of_iteratedDeriv_zero _ hdiff hzero
  have hz : fockDiff lam (G lam p 0) z - G lam (gegenDiff lam p) 0 z = 0 := congrFun hfun z
  exact sub_eq_zero.mp hz

/-- **Theorem 7.2** (intertwining). For every complex polynomial `p`,
`𝒟_λ (C_{λ,α} p) = C_{λ,α} (D_λ p)`, pointwise for the entire representatives. -/
theorem intertwining (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (p : ℂ[X]) (z : ℂ) :
    fockDiff lam (GaussianArea.entireRepresentative alpha
        (GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha (polyLp lam hlam p))) z =
      GaussianArea.entireRepresentative alpha
        (GeneralUltrasphericalFock.C_intrinsicEntire lam alpha hlam ha
          (polyLp lam hlam (gegenDiff lam p))) z := by
  rw [entireRepresentative_polyLp_eq_G lam alpha hlam ha p,
    entireRepresentative_polyLp_eq_G lam alpha hlam ha (gegenDiff lam p)]
  exact fockDiff_G_eq lam hlam p z

/-! ## Proposition 7.5 -/

/-- Proposition 7.5, first display: the ladder form
`𝒟_λ = (a_α†)² a_α² + (2λ+1) a_α† a_α + (a_α†)²/(4α)`, valid for every `F : ℂ → ℂ`. -/
theorem fockDiff_eq_ladder (lam alpha : ℝ) (ha : 0 < alpha) (F : ℂ → ℂ) (z : ℂ) :
    fockDiff lam F z =
      aDag alpha (aDag alpha (aOp alpha (aOp alpha F))) z +
        ((2 * lam + 1 : ℝ) : ℂ) * aDag alpha (aOp alpha F) z +
        1 / (4 * (alpha : ℂ)) * aDag alpha (aDag alpha F) z := by
  set s : ℂ := ((Real.sqrt alpha : ℝ) : ℂ) with hs_def
  have hs0 : s ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ha).ne'
  have h1 : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0
  have h2 : s * s = (alpha : ℂ) := by
    rw [hs_def, ← Complex.ofReal_mul, Real.mul_self_sqrt ha.le]
  have h3 : (alpha : ℂ) * (alpha : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ha.ne')
  have hA1 : aOp alpha F = fun z => s⁻¹ * deriv F z := rfl
  have hA2 : aOp alpha (aOp alpha F) = fun z => s⁻¹ * (s⁻¹ * deriv (deriv F) z) := by
    funext w
    show s⁻¹ * deriv (aOp alpha F) w = _
    rw [hA1, deriv_const_mul_field']
  have hD : ∀ G : ℂ → ℂ, aDag alpha G = fun z => s * z * G z := fun G => rfl
  unfold fockDiff
  simp only [hD, hA2]
  simp only [hA1]
  linear_combination
    (-(z ^ 2 * deriv (deriv F) z * (1 + s * s⁻¹)) - ((2 * lam + 1 : ℝ) : ℂ) * z * deriv F z) *
      h1 + (-(z ^ 2 * F z / 4 * (alpha : ℂ)⁻¹)) * h2 + (-(z ^ 2 * F z / 4)) * h3

theorem monomialWeight_ratio (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) * alpha =
      Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) *
        Real.sqrt (alpha ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) := by
  have hF0 : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hK : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  have hfac : (Nat.factorial (n + 2) : ℝ) =
      (Nat.factorial n : ℝ) * (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hprod : ((n : ℝ) + 1) * ((n : ℝ) + 2) *
      (alpha ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) =
      alpha ^ 2 * (alpha ^ n / (Nat.factorial n : ℝ)) := by
    rw [hfac]
    calc
      ((n : ℝ) + 1) * ((n : ℝ) + 2) *
          (alpha ^ (n + 2) / ((Nat.factorial n : ℝ) * (((n : ℝ) + 1) * ((n : ℝ) + 2)))) =
          (alpha ^ 2 * alpha ^ n * (((n : ℝ) + 1) * ((n : ℝ) + 2))) /
            ((Nat.factorial n : ℝ) * (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
        rw [mul_div_assoc']
        congr 1
        ring
      _ = alpha ^ 2 * alpha ^ n / (Nat.factorial n : ℝ) := mul_div_mul_right _ _ hK.ne'
      _ = alpha ^ 2 * (alpha ^ n / (Nat.factorial n : ℝ)) := mul_div_assoc _ _ _
  rw [← Real.sqrt_mul hK.le, hprod, Real.sqrt_mul (sq_nonneg alpha), Real.sqrt_sq ha.le]
  ring

/-- **Proposition 7.5** (second display): on the normalized Gaussian monomials
`e_n = √(αⁿ/n!) zⁿ`,
`𝒟_λ e_n = n(n+2λ) e_n + √((n+1)(n+2))/(4α) · e_{n+2}`. -/
theorem fockDiff_normalizedMonomial (lam alpha : ℝ) (ha : 0 < alpha) (n : ℕ) (z : ℂ) :
    fockDiff lam (GaussianArea.normalizedMonomial alpha n) z =
      (n : ℂ) * ((n : ℂ) + 2 * (lam : ℂ)) * GaussianArea.normalizedMonomial alpha n z +
        ((Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) : ℝ) : ℂ) / (4 * (alpha : ℂ)) *
          GaussianArea.normalizedMonomial alpha (n + 2) z := by
  set w : ℂ := GaussianArea.monomialWeight alpha n with hw_def
  have hcoef : ((Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) : ℝ) : ℂ) / (4 * (alpha : ℂ)) *
      GaussianArea.monomialWeight alpha (n + 2) = w / 4 := by
    have hr := congrArg (fun x : ℝ => (x : ℂ)) (monomialWeight_ratio alpha ha n)
    simp only [Complex.ofReal_mul] at hr
    have hα0 : (alpha : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    rw [div_mul_eq_mul_div]
    unfold GaussianArea.monomialWeight
    rw [← hr, hw_def]
    unfold GaussianArea.monomialWeight
    rw [mul_div_mul_right _ _ hα0]
  have hfun : GaussianArea.normalizedMonomial alpha n = fun z => w * z ^ n := rfl
  have hd1 : deriv (fun z => w * z ^ n) = fun z => w * ((n : ℂ) * z ^ (n - 1)) :=
    funext fun z => ((hasDerivAt_pow n z).const_mul w).deriv
  have hd2 : deriv (fun z => w * ((n : ℂ) * z ^ (n - 1))) =
      fun z => w * ((n : ℂ) * (((n - 1 : ℕ) : ℂ) * z ^ (n - 1 - 1))) :=
    funext fun z => (((hasDerivAt_pow (n - 1) z).const_mul (n : ℂ)).const_mul w).deriv
  have hlast : ((Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) : ℝ) : ℂ) / (4 * (alpha : ℂ)) *
      GaussianArea.normalizedMonomial alpha (n + 2) z = w / 4 * z ^ (n + 2) := by
    unfold GaussianArea.normalizedMonomial
    rw [← mul_assoc, hcoef]
  rw [hlast]
  unfold fockDiff
  rw [hfun, hd1, hd2]
  match n with
  | 0 =>
    rw [Nat.cast_zero]
    ring
  | 1 =>
    rw [Nat.cast_one, show 1 - 1 = 0 by omega, Nat.cast_zero]
    push_cast
    ring
  | m + 2 =>
    rw [show m + 2 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega]
    push_cast
    ring

#print axioms GegenbauerFock.Section7Intertwining.mom_gegenDiff
#print axioms GegenbauerFock.Section7Intertwining.G_hasDerivAt
#print axioms GegenbauerFock.Section7Intertwining.fockDiff_G_eq
#print axioms GegenbauerFock.Section7Intertwining.intertwining
#print axioms GegenbauerFock.Section7Intertwining.fockDiff_eq_ladder
#print axioms GegenbauerFock.Section7Intertwining.fockDiff_normalizedMonomial

end GegenbauerFock.Section7Intertwining
