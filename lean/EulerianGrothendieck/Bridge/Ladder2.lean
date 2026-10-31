import Bridge.Ladder
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Proposition 3.8 (continued): Gaussian integrability, integration by parts, orthogonality

`J_{nm}(t,s) = ∫ \overline{φ_n(t,z)} φ_m(s,z) dμ_α(z)` satisfies `J_{n+1,m+1} = (m+1)α J_{nm}`,
`J_{n+1,0} = J_{0,m+1} = 0` and `J_{00} = e^{st/α}`, hence `J_{nm} = δ_{nm} n! αⁿ e^{st/α}`.
-/

open MeasureTheory Complex Set Filter Topology intervalIntegral
open scoped ComplexConjugate Nat

namespace EulerianBridge.Ladder

open EulerianGrothendieck.Fock

/-! ## Gaussian integrability -/

theorem integrable_exp_abs_re_im {α : ℝ} (hα : 0 < α) (K : ℝ) :
    Integrable (fun z : ℂ => Real.exp (K * (|z.re| + |z.im|)) * fockDensity α z) := by
  rw [integrable_complex_iff_prod]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl]
  have h1 := (integrable_exp_neg_mul_sq_add_mul hα K).add (integrable_exp_neg_mul_sq_add_mul hα (-K))
  have hprod := (h1.mul_prod h1).const_mul (α / Real.pi)
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      Real.exp (K * (|(⟨p.1, p.2⟩ : ℂ).re| + |(⟨p.1, p.2⟩ : ℂ).im|)) * fockDensity α ⟨p.1, p.2⟩) := by
    have h2 : Measurable (fun p : ℝ × ℝ => fockDensity α ⟨p.1, p.2⟩) :=
      (continuous_fockDensity α).measurable.comp measurable_mk
    exact (Real.measurable_exp.comp (measurable_const.mul
      ((continuous_abs.measurable.comp (Complex.measurable_re.comp measurable_mk)).add
        (continuous_abs.measurable.comp (Complex.measurable_im.comp measurable_mk))))).mul h2
  refine hprod.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun p => ?_))
  show ‖Real.exp (K * (|(⟨p.1, p.2⟩ : ℂ).re| + |(⟨p.1, p.2⟩ : ℂ).im|)) * fockDensity α ⟨p.1, p.2⟩‖ ≤
    α / Real.pi * ((Real.exp (-α * p.1 ^ 2 + K * p.1) + Real.exp (-α * p.1 ^ 2 + -K * p.1)) *
      (Real.exp (-α * p.2 ^ 2 + K * p.2) + Real.exp (-α * p.2 ^ 2 + -K * p.2)))
  simp only [fockDensity, mk_norm_sq]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hab : ∀ x : ℝ, Real.exp (K * |x|) * Real.exp (-α * x ^ 2) ≤
      Real.exp (-α * x ^ 2 + K * x) + Real.exp (-α * x ^ 2 + -K * x) := by
    intro x
    rw [← Real.exp_add]
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h, show K * x + -α * x ^ 2 = -α * x ^ 2 + K * x by ring]
      linarith [Real.exp_pos (-α * x ^ 2 + -K * x)]
    · rw [abs_of_nonpos h, show K * -x + -α * x ^ 2 = -α * x ^ 2 + -K * x by ring]
      linarith [Real.exp_pos (-α * x ^ 2 + K * x)]
  have he : Real.exp (K * (|p.1| + |p.2|)) * (α / Real.pi * Real.exp (-α * (p.1 ^ 2 + p.2 ^ 2))) =
      α / Real.pi * ((Real.exp (K * |p.1|) * Real.exp (-α * p.1 ^ 2)) *
        (Real.exp (K * |p.2|) * Real.exp (-α * p.2 ^ 2))) := by
    have h0 : Real.exp (K * (|p.1| + |p.2|)) * Real.exp (-α * (p.1 ^ 2 + p.2 ^ 2)) =
        (Real.exp (K * |p.1|) * Real.exp (-α * p.1 ^ 2)) * (Real.exp (K * |p.2|) * Real.exp (-α * p.2 ^ 2)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc _ = α / Real.pi * (Real.exp (K * (|p.1| + |p.2|)) * Real.exp (-α * (p.1 ^ 2 + p.2 ^ 2))) := by ring
      _ = _ := by rw [h0]
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul (hab p.1) (hab p.2) (by positivity) (by positivity)

theorem integrable_exp_norm {α : ℝ} (hα : 0 < α) (K : ℝ) :
    Integrable (fun z : ℂ => Real.exp (K * ‖z‖) * fockDensity α z) := by
  refine (integrable_exp_abs_re_im hα (max K 0)).mono' ?_ (Eventually.of_forall (fun z => ?_))
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_norm)).mul
      (continuous_fockDensity α)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (fockDensity_nonneg hα.le z))]
    apply mul_le_mul_of_nonneg_right _ (fockDensity_nonneg hα.le z)
    apply Real.exp_le_exp.mpr
    have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    calc K * ‖z‖ ≤ max K 0 * ‖z‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max K 0 * (|z.re| + |z.im|) := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)

/-- A continuous function bounded by `C e^{K|z|}` is integrable against `μ_α`. -/
theorem integrable_of_exp_bound {α : ℝ} (hα : 0 < α) {f : ℂ → ℂ} (hf : Continuous f) (C K : ℝ)
    (hb : ∀ z, ‖f z‖ ≤ C * Real.exp (K * ‖z‖)) :
    Integrable (fun z => f z * (fockDensity α z : ℂ)) := by
  refine ((integrable_exp_norm hα K).const_mul C).mono' ?_ (Eventually.of_forall (fun z => ?_))
  · exact (hf.mul (Complex.continuous_ofReal.comp (continuous_fockDensity α))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fockDensity_nonneg hα.le z), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hb z) (fockDensity_nonneg hα.le z)

/-! ## Exponential bounds for `φ_n` -/

theorem pow_le_exp (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : x ^ n ≤ n ! * Real.exp x := by
  have h := Real.pow_div_factorial_le_exp x hx n
  have hf : (0:ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf] at h; linarith

theorem norm_P_le (α : ℝ) (hα : 0 < α) (t : ℝ) (z : ℂ) : ‖(α:ℂ) * conj z - I * t‖ ≤ α * ‖z‖ + |t| := by
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_conj, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hα]

theorem norm_e_le (t : ℝ) (z : ℂ) : ‖cexp (I * t * z)‖ ≤ Real.exp (|t| * ‖z‖) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have : (I * (t:ℂ) * z).re = -(t * z.im) := by simp [Complex.mul_re]
  rw [this]
  calc -(t * z.im) ≤ |t * z.im| := neg_le_abs _
    _ = |t| * |z.im| := abs_mul _ _
    _ ≤ |t| * ‖z‖ := mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) (abs_nonneg _)

theorem norm_phi_le (α : ℝ) (hα : 0 < α) (n : ℕ) (t : ℝ) (z : ℂ) :
    ‖phi α n t z‖ ≤ (n ! * Real.exp |t|) * Real.exp ((α + |t|) * ‖z‖) := by
  unfold phi
  rw [norm_mul, norm_pow]
  have h1 : ‖(α:ℂ) * conj z - I * t‖ ^ n ≤ n ! * Real.exp (α * ‖z‖ + |t|) :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_P_le α hα t z) n).trans
      (pow_le_exp _ (by positivity) n)
  calc ‖(α:ℂ) * conj z - I * t‖ ^ n * ‖cexp (I * t * z)‖
      ≤ (n ! * Real.exp (α * ‖z‖ + |t|)) * Real.exp (|t| * ‖z‖) :=
        mul_le_mul h1 (norm_e_le t z) (norm_nonneg _) (by positivity)
    _ = (n ! * Real.exp |t|) * Real.exp ((α + |t|) * ‖z‖) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]; congr 2; ring

end EulerianBridge.Ladder
