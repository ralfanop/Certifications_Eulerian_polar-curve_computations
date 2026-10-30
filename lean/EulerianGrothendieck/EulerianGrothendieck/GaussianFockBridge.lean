import EulerianGrothendieck.RawScaleAsymptotics
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Task A, part 1: the Gaussian Fock norm of `r_E^M`

`rE z = ∫_{-1/2}^{1/2} e^{i t z} dt` is the entire function of the manuscript
(value `1` at `z = 0`).  The Fock weight is `dμ_α(z) = (α/π) e^{-α|z|^2} dA(z)`,
written here with the explicit density `fockDensity α` against Lebesgue measure on `ℂ`.

Main results (namespace `EulerianGrothendieck.Fock`):
* `gaussian_pairing`: `∫_ℂ e^{i z s - i \bar z t} dμ_α(z) = e^{s t/α}` for real `s, t`;
* `sum_charFun`: `E e^{i z S_M} = r_E(z)^M` for complex `z`;
* `fock_norm_eq_probability_integral`:
  `∫_ℂ |r_E(z)^M|^2 dμ_α(z) = E exp(S_M T_M / α)` with `T_M` an independent copy
  (realised, exactly as in the certified asymptotic theorems, on `μ.prod μ`);
* `fock_norm_eq_moment_series`: the same quantity equals
  `∑_k (μ_{2k}^{[M]})^2 / ((2k)! α^{2k})`;
* `fock_norm_scaled_eq_uniformNormSeries`: at `α = c M` it is `uniformNormSeries M (1/(12c))`,
  the series of the certified asymptotic theory.
No hypothesis contains the conclusion: the probabilistic hypotheses are measurability,
independence and the uniform law only. -/

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Finset Complex

namespace EulerianGrothendieck.Fock

/-- The manuscript's entire function `r_E(z) = ∫_{-1/2}^{1/2} e^{itz} dt`. -/
def rE (z : ℂ) : ℂ := ∫ t in (-1/2:ℝ)..(1/2), cexp (I * (t:ℂ) * z)

/-- `r_E(z) = sin(z/2)/(z/2)` for `z ≠ 0`: the manuscript's Eulerian sine-cardinal profile. -/
theorem rE_eq_sin_div {z : ℂ} (hz : z ≠ 0) : rE z = Complex.sin (z / 2) / (z / 2) := by
  unfold rE
  have hc : I * z ≠ 0 := mul_ne_zero I_ne_zero hz
  have h : ∀ t : ℝ, cexp (I * (t:ℂ) * z) = cexp ((I * z) * (t:ℂ)) := fun t => by ring_nf
  simp_rw [h]
  rw [integral_exp_mul_complex hc, Complex.sin]
  have e1 : I * z * ((1/2:ℝ):ℂ) = z / 2 * I := by push_cast; ring
  have e2 : I * z * ((-1/2:ℝ):ℂ) = -(z / 2) * I := by push_cast; ring
  rw [e1, e2]
  obtain ⟨A, hA⟩ : ∃ A : ℂ, A = cexp (z / 2 * I) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℂ, B = cexp (-(z / 2) * I) := ⟨_, rfl⟩
  rw [← hA, ← hB]
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  rw [div_eq_div_iff hc hz2]
  linear_combination ((A - B) * z / 2) * I_sq

theorem rE_zero : rE 0 = 1 := by
  simp only [rE, mul_zero, Complex.exp_zero, intervalIntegral.integral_const, real_smul, mul_one]
  norm_num

/-- The Gaussian density `(α/π) e^{-α|z|^2}` of the Fock weight `μ_α`. -/
def fockDensity (α : ℝ) (z : ℂ) : ℝ := α / Real.pi * Real.exp (-α * ‖z‖ ^ 2)

theorem fockDensity_nonneg {α : ℝ} (hα : 0 ≤ α) (z : ℂ) : 0 ≤ fockDensity α z := by
  unfold fockDensity
  exact mul_nonneg (div_nonneg hα Real.pi_pos.le) (Real.exp_pos _).le

theorem continuous_fockDensity (α : ℝ) : Continuous (fockDensity α) := by
  unfold fockDensity
  fun_prop

theorem measurable_mk : Measurable (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) :=
  Complex.measurableEquivRealProd.symm.measurable

/-- Integrals over `ℂ` are integrals over `ℝ × ℝ` in the coordinates `(Re z, Im z)`. -/
theorem integral_complex_eq_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) : ∫ z, f z = ∫ p : ℝ × ℝ, f (⟨p.1, p.2⟩ : ℂ) := by
  have h := (MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod).integral_comp' f
  rw [← h]
  rfl

theorem integrable_complex_iff_prod {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) : Integrable f ↔ Integrable (fun p : ℝ × ℝ => f (⟨p.1, p.2⟩ : ℂ)) := by
  have h := MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod
  rw [← h.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  rfl

theorem mk_norm_sq (x y : ℝ) : ‖(⟨x, y⟩ : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem conj_mk (x y : ℝ) : conj (⟨x, y⟩ : ℂ) = (x:ℂ) - (y:ℂ) * I := by
  apply Complex.ext <;> simp

theorem mk_eq (x y : ℝ) : (⟨x, y⟩ : ℂ) = (x:ℂ) + (y:ℂ) * I := Complex.mk_eq_add_mul_I x y

/-- Pointwise factorisation of the Gaussian pairing integrand in real coordinates. -/
theorem pairing_integrand_factor (α s t x y : ℝ) :
    cexp (I * (⟨x, y⟩ : ℂ) * s - I * conj (⟨x, y⟩ : ℂ) * t) * (fockDensity α ⟨x, y⟩ : ℂ) =
      ((α / Real.pi : ℝ) : ℂ) *
        (cexp (-(α:ℂ) * (x:ℂ) ^ 2 + (I * ((s:ℂ) - t)) * x + 0) *
          cexp (-(α:ℂ) * (y:ℂ) ^ 2 + (-((s:ℂ) + t)) * y + 0)) := by
  have hd : (fockDensity α ⟨x, y⟩ : ℂ) =
      ((α / Real.pi : ℝ) : ℂ) * cexp (-(α:ℂ) * ((x:ℂ) ^ 2 + (y:ℂ) ^ 2)) := by
    unfold fockDensity
    rw [mk_norm_sq, Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    ring_nf
  rw [hd, conj_mk, mk_eq]
  calc cexp (I * ((x:ℂ) + y * I) * s - I * ((x:ℂ) - y * I) * t) *
        (((α / Real.pi : ℝ) : ℂ) * cexp (-(α:ℂ) * ((x:ℂ) ^ 2 + (y:ℂ) ^ 2)))
      = ((α / Real.pi : ℝ) : ℂ) * cexp ((I * ((x:ℂ) + y * I) * s - I * ((x:ℂ) - y * I) * t) +
          (-(α:ℂ) * ((x:ℂ) ^ 2 + (y:ℂ) ^ 2))) := by
        rw [Complex.exp_add]; ring
    _ = ((α / Real.pi : ℝ) : ℂ) *
        (cexp (-(α:ℂ) * (x:ℂ) ^ 2 + (I * ((s:ℂ) - t)) * x + 0) *
          cexp (-(α:ℂ) * (y:ℂ) ^ 2 + (-((s:ℂ) + t)) * y + 0)) := by
        rw [← Complex.exp_add]
        congr 2
        linear_combination ((y:ℂ) * s + (y:ℂ) * t) * I_sq

/-- The Gaussian pairing: `∫_ℂ e^{i z s - i \bar z t} dμ_α(z) = e^{st/α}` for real `s, t`. -/
theorem gaussian_pairing {α : ℝ} (hα : 0 < α) (s t : ℝ) :
    ∫ z : ℂ, cexp (I * z * s - I * conj z * t) * (fockDensity α z : ℂ) =
      cexp ((s:ℂ) * (t:ℂ) / (α:ℂ)) := by
  rw [integral_complex_eq_prod]
  simp_rw [pairing_integrand_factor]
  rw [integral_const_mul]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl]
  rw [integral_prod_mul (fun x : ℝ => cexp (-(α:ℂ) * (x:ℂ) ^ 2 + (I * ((s:ℂ) - t)) * x + 0))
    (fun y : ℝ => cexp (-(α:ℂ) * (y:ℂ) ^ 2 + (-((s:ℂ) + t)) * y + 0))]
  have hb : (-(α:ℂ)).re < 0 := by simpa using hα
  rw [integral_cexp_quadratic hb, integral_cexp_quadratic hb]
  have hα' : (α:ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hpi : ((Real.pi:ℝ):ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hP : ((Real.pi:ℂ) / -(-(α:ℂ))) ^ (1/2:ℂ) * ((Real.pi:ℂ) / -(-(α:ℂ))) ^ (1/2:ℂ) =
      (Real.pi:ℂ) / α := by
    rw [← sq, one_div, Complex.cpow_ofNat_inv_pow, neg_neg]
  have hexp : (0 - (I * ((s:ℂ) - t)) ^ 2 / (4 * -(α:ℂ))) +
      (0 - (-((s:ℂ) + t)) ^ 2 / (4 * -(α:ℂ))) = (s:ℂ) * t / α := by
    rw [mul_pow, I_sq]
    field_simp
    ring
  have hone : ((α / Real.pi : ℝ) : ℂ) * ((Real.pi:ℂ) / α) = 1 := by
    push_cast
    rw [div_mul_div_comm, mul_comm (α:ℂ) (Real.pi:ℂ), div_self (mul_ne_zero hpi hα')]
  calc ((α / Real.pi : ℝ) : ℂ) *
        (((Real.pi:ℂ) / -(-(α:ℂ))) ^ (1/2:ℂ) * cexp (0 - (I * ((s:ℂ) - t)) ^ 2 / (4 * -(α:ℂ))) *
          (((Real.pi:ℂ) / -(-(α:ℂ))) ^ (1/2:ℂ) * cexp (0 - (-((s:ℂ) + t)) ^ 2 / (4 * -(α:ℂ)))))
        = ((α / Real.pi : ℝ) : ℂ) *
            (((Real.pi:ℂ) / -(-(α:ℂ))) ^ (1/2:ℂ) * ((Real.pi:ℂ) / -(-(α:ℂ))) ^ (1/2:ℂ)) *
            cexp ((0 - (I * ((s:ℂ) - t)) ^ 2 / (4 * -(α:ℂ))) +
              (0 - (-((s:ℂ) + t)) ^ 2 / (4 * -(α:ℂ)))) := by
          rw [Complex.exp_add]; ring
    _ = cexp ((s:ℂ) * (t:ℂ) / (α:ℂ)) := by
          rw [hP, hexp, hone, one_mul]

/-- Characteristic function of one centred uniform variable, at complex argument. -/
theorem uniform_charFun {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {U : Ω → ℝ}
    (hU : Measurable U) (hlaw : μ.map U = V033.UniformSum.uniformLaw) (z : ℂ) :
    ∫ ω, cexp (I * z * (U ω : ℂ)) ∂μ = rE z := by
  have hc : Continuous (fun x : ℝ => cexp (I * z * (x:ℂ))) := by fun_prop
  rw [← integral_map hU.aemeasurable hc.aestronglyMeasurable, hlaw, V033.UniformSum.uniformLaw,
    rE, intervalIntegral.integral_of_le (by norm_num)]
  congr 1
  funext x
  ring_nf

/-- `E e^{i z S_M} = r_E(z)^M` for every complex `z`. -/
theorem sum_charFun {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (z : ℂ) (M : ℕ) :
    ∫ ω, cexp (I * z * ((∑ i ∈ range M, U i ω : ℝ) : ℂ)) ∂μ = rE z ^ M := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hI : IndepFun (fun ω => ∑ i ∈ range M, U i ω) (U M) μ := by
      have he : (∑ i ∈ range M, U i) = (fun ω => ∑ i ∈ range M, U i ω) := by
        ext ω
        simp
      rw [← he]
      exact hind.indepFun_finset_sum_of_notMem hU (Finset.notMem_range_self (n := M))
    have hS : Measurable (fun ω => ∑ i ∈ range M, U i ω) :=
      Finset.measurable_fun_sum (range M) (fun i _ => hU i)
    have hf : Continuous (fun x : ℝ => cexp (I * z * (x:ℂ))) := by fun_prop
    have key := hI.integral_fun_comp_mul_comp (f := fun x : ℝ => cexp (I * z * (x:ℂ)))
      (g := fun x : ℝ => cexp (I * z * (x:ℂ))) hS.aemeasurable (hU M).aemeasurable
      hf.aestronglyMeasurable hf.aestronglyMeasurable
    have hsplit : ∀ ω, cexp (I * z * ((∑ i ∈ range (M+1), U i ω : ℝ) : ℂ)) =
        cexp (I * z * ((∑ i ∈ range M, U i ω : ℝ) : ℂ)) * cexp (I * z * (U M ω : ℂ)) := by
      intro ω
      rw [Finset.sum_range_succ, ofReal_add, mul_add, Complex.exp_add]
    simp_rw [hsplit]
    rw [key, ih, uniform_charFun (hU M) (hlaw M), pow_succ]

/-- The squared modulus `|r_E(z)^M|^2` as a product-law expectation. -/
theorem norm_sq_rE_pow {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (z : ℂ) (M : ℕ) :
    ((‖rE z ^ M‖ ^ 2 : ℝ) : ℂ) =
      ∫ xy, cexp (I * z * ((∑ i ∈ range M, U i xy.1 : ℝ) : ℂ) -
        I * conj z * ((∑ i ∈ range M, U i xy.2 : ℝ) : ℂ)) ∂μ.prod μ := by
  have hw := sum_charFun U hU hind hlaw z M
  have hconj : conj (rE z ^ M) =
      ∫ ω, cexp (-I * conj z * ((∑ i ∈ range M, U i ω : ℝ) : ℂ)) ∂μ := by
    rw [← hw, ← integral_conj]
    congr 1
    funext ω
    rw [← Complex.exp_conj, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hnorm : ((‖rE z ^ M‖ ^ 2 : ℝ) : ℂ) = rE z ^ M * conj (rE z ^ M) := by
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [hnorm, hconj]
  conv_lhs => rw [← hw]
  rw [← integral_prod_mul]
  congr 1
  funext xy
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The bound `‖r_E(z)‖ ≤ e^{|Im z|/2}`. -/
theorem norm_rE_le (z : ℂ) : ‖rE z‖ ≤ Real.exp (|z.im| / 2) := by
  unfold rE
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1/2:ℝ)) (b := 1/2) (C := Real.exp (|z.im| / 2))
    (f := fun t : ℝ => cexp (I * (t:ℂ) * z)) (by
      intro t ht
      rw [Set.uIoc_of_le (by norm_num)] at ht
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hre : (I * (t:ℂ) * z).re = -(t * z.im) := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im]
        ring
      rw [hre]
      have ht' : |t| ≤ 1/2 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      calc -(t * z.im) ≤ |t * z.im| := neg_le_abs _
        _ = |t| * |z.im| := abs_mul _ _
        _ ≤ (1/2) * |z.im| := mul_le_mul_of_nonneg_right ht' (abs_nonneg _)
        _ = |z.im| / 2 := by ring)
  calc _ ≤ Real.exp (|z.im| / 2) * |1/2 - (-1/2:ℝ)| := h
    _ = Real.exp (|z.im| / 2) := by norm_num

/-- One-dimensional integrability of `e^{-α y^2 + c y}`. -/
theorem integrable_exp_neg_mul_sq_add_mul {α : ℝ} (hα : 0 < α) (c : ℝ) :
    Integrable (fun y : ℝ => Real.exp (-α * y ^ 2 + c * y)) := by
  have h := (integrable_cexp_quadratic (b := (α:ℂ)) (by simpa using hα) (c:ℂ) 0).norm
  refine h.congr (Filter.Eventually.of_forall (fun y => ?_))
  beta_reduce
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_re, ← Complex.ofReal_pow]
  ring

/-- Integrability of `e^{C |Im z|}` against the Fock density. -/
theorem integrable_exp_abs_im_mul_fockDensity {α : ℝ} (hα : 0 < α) (C : ℝ) :
    Integrable (fun z : ℂ => Real.exp (C * |z.im|) * fockDensity α z) := by
  rw [integrable_complex_iff_prod]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl]
  have hx := integrable_exp_neg_mul_sq hα
  have hy := (integrable_exp_neg_mul_sq_add_mul hα C).add (integrable_exp_neg_mul_sq_add_mul hα (-C))
  have hprod := (hx.mul_prod hy).const_mul (α / Real.pi)
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      Real.exp (C * |(⟨p.1, p.2⟩ : ℂ).im|) * fockDensity α ⟨p.1, p.2⟩) := by
    have h1 : Measurable (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ).im) :=
      Complex.measurable_im.comp measurable_mk
    have h2 : Measurable (fun p : ℝ × ℝ => fockDensity α ⟨p.1, p.2⟩) :=
      (continuous_fockDensity α).measurable.comp measurable_mk
    exact (Real.measurable_exp.comp (measurable_const.mul (continuous_abs.measurable.comp h1))).mul h2
  refine hprod.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun p => ?_))
  show ‖Real.exp (C * |(⟨p.1, p.2⟩ : ℂ).im|) * fockDensity α ⟨p.1, p.2⟩‖ ≤
    α / Real.pi * (Real.exp (-α * p.1 ^ 2) *
      (Real.exp (-α * p.2 ^ 2 + C * p.2) + Real.exp (-α * p.2 ^ 2 + -C * p.2)))
  have him : (⟨p.1, p.2⟩ : ℂ).im = p.2 := rfl
  simp only [fockDensity, mk_norm_sq]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hab : Real.exp (C * |p.2|) ≤ Real.exp (C * p.2) + Real.exp (-C * p.2) := by
    rcases le_total 0 p.2 with h2 | h2
    · rw [abs_of_nonneg h2]; linarith [Real.exp_pos (-C * p.2)]
    · rw [abs_of_nonpos h2, show C * -p.2 = -C * p.2 by ring]; linarith [Real.exp_pos (C * p.2)]
  have he : Real.exp (-α * (p.1 ^ 2 + p.2 ^ 2)) =
      Real.exp (-α * p.1 ^ 2) * Real.exp (-α * p.2 ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsum : (Real.exp (C * p.2) + Real.exp (-C * p.2)) * Real.exp (-α * p.2 ^ 2) =
      Real.exp (-α * p.2 ^ 2 + C * p.2) + Real.exp (-α * p.2 ^ 2 + -C * p.2) := by
    rw [add_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  rw [he]
  calc Real.exp (C * |p.2|) * (α / Real.pi * (Real.exp (-α * p.1 ^ 2) * Real.exp (-α * p.2 ^ 2)))
      ≤ (Real.exp (C * p.2) + Real.exp (-C * p.2)) *
          (α / Real.pi * (Real.exp (-α * p.1 ^ 2) * Real.exp (-α * p.2 ^ 2))) :=
        mul_le_mul_of_nonneg_right hab (by positivity)
    _ = α / Real.pi * (Real.exp (-α * p.1 ^ 2) *
          (Real.exp (-α * p.2 ^ 2 + C * p.2) + Real.exp (-α * p.2 ^ 2 + -C * p.2))) := by
        rw [← hsum]; ring

/-- Fubini for the Gaussian pairing of two bounded real random variables. -/
theorem gaussian_fubini {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'}
    [IsProbabilityMeasure ν] {X Y : Ω' → ℝ} (hX : Measurable X) (hY : Measurable Y) (B : ℝ)
    (hXB : ∀ᵐ ω ∂ν, |X ω| ≤ B) (hYB : ∀ᵐ ω ∂ν, |Y ω| ≤ B) {α : ℝ} (hα : 0 < α) :
    ∫ z : ℂ, (∫ ω, cexp (I * z * (X ω : ℂ) - I * conj z * (Y ω : ℂ)) ∂ν) * (fockDensity α z : ℂ) =
      ∫ ω, cexp ((X ω : ℂ) * (Y ω : ℂ) / (α:ℂ)) ∂ν := by
  have hmeas : Measurable (Function.uncurry (fun (z : ℂ) (ω : Ω') =>
      cexp (I * z * (X ω : ℂ) - I * conj z * (Y ω : ℂ)) * (fockDensity α z : ℂ))) := by
    have h1 : Measurable (fun p : ℂ × Ω' => p.1) := measurable_fst
    have hXs : Measurable (fun p : ℂ × Ω' => ((X p.2 : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (hX.comp measurable_snd)
    have hYs : Measurable (fun p : ℂ × Ω' => ((Y p.2 : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (hY.comp measurable_snd)
    have hc : Measurable (fun p : ℂ × Ω' => conj p.1) :=
      Complex.continuous_conj.measurable.comp measurable_fst
    have hd : Measurable (fun p : ℂ × Ω' => ((fockDensity α p.1 : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp ((continuous_fockDensity α).measurable.comp measurable_fst)
    exact (((measurable_const.mul h1).mul hXs |>.sub ((measurable_const.mul hc).mul hYs)).cexp).mul hd
  have hint : Integrable (Function.uncurry (fun (z : ℂ) (ω : Ω') =>
      cexp (I * z * (X ω : ℂ) - I * conj z * (Y ω : ℂ)) * (fockDensity α z : ℂ)))
      ((volume : Measure ℂ).prod ν) := by
    have hg := (integrable_exp_abs_im_mul_fockDensity hα (2 * B)).comp_fst ν
    refine hg.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hXB,
      Measure.quasiMeasurePreserving_snd.ae hYB] with p hpX hpY
    simp only [Function.uncurry, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (fockDensity_nonneg hα.le _)]
    apply mul_le_mul_of_nonneg_right _ (fockDensity_nonneg hα.le _)
    apply Real.exp_le_exp.mpr
    have hre : (I * p.1 * (X p.2 : ℂ) - I * conj p.1 * (Y p.2 : ℂ)).re =
        -(X p.2 * p.1.im) - Y p.2 * p.1.im := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [hre]
    have h1 : -(X p.2 * p.1.im) ≤ B * |p.1.im| := by
      calc -(X p.2 * p.1.im) ≤ |X p.2 * p.1.im| := neg_le_abs _
        _ = |X p.2| * |p.1.im| := abs_mul _ _
        _ ≤ B * |p.1.im| := mul_le_mul_of_nonneg_right hpX (abs_nonneg _)
    have h2 : -(Y p.2 * p.1.im) ≤ B * |p.1.im| := by
      calc -(Y p.2 * p.1.im) ≤ |Y p.2 * p.1.im| := neg_le_abs _
        _ = |Y p.2| * |p.1.im| := abs_mul _ _
        _ ≤ B * |p.1.im| := mul_le_mul_of_nonneg_right hpY (abs_nonneg _)
    linarith
  calc ∫ z : ℂ, (∫ ω, cexp (I * z * (X ω : ℂ) - I * conj z * (Y ω : ℂ)) ∂ν) * (fockDensity α z : ℂ)
      = ∫ z : ℂ, ∫ ω, cexp (I * z * (X ω : ℂ) - I * conj z * (Y ω : ℂ)) * (fockDensity α z : ℂ) ∂ν := by
        congr 1
        funext z
        rw [integral_mul_const]
    _ = ∫ ω, (∫ z : ℂ, cexp (I * z * (X ω : ℂ) - I * conj z * (Y ω : ℂ)) * (fockDensity α z : ℂ)) ∂ν :=
        integral_integral_swap hint
    _ = ∫ ω, cexp ((X ω : ℂ) * (Y ω : ℂ) / (α:ℂ)) ∂ν := by
        congr 1
        funext ω
        exact gaussian_pairing hα (X ω) (Y ω)

/-- **Theorem 9.2, first equality.**  For every `α > 0` and every `M`,
`∫_ℂ |r_E(z)^M|^2 (α/π) e^{-α|z|^2} dA(z) = E exp(S_M T_M / α)`,
with `T_M` the independent copy carried by the second factor of `μ.prod μ`. -/
theorem fock_norm_eq_probability_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (M : ℕ) {α : ℝ} (hα : 0 < α) :
    ∫ z : ℂ, ‖rE z ^ M‖ ^ 2 * fockDensity α z =
      ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / α) ∂μ.prod μ := by
  have hS : Measurable (fun ω => ∑ i ∈ range M, U i ω) :=
    Finset.measurable_fun_sum (range M) (fun i _ => hU i)
  have hB := EulerianGrothendieck.uniform_sum_ae_bound U hU hlaw M
  have hX : Measurable (fun xy : Ω × Ω => ∑ i ∈ range M, U i xy.1) := hS.comp measurable_fst
  have hY : Measurable (fun xy : Ω × Ω => ∑ i ∈ range M, U i xy.2) := hS.comp measurable_snd
  have hXB : ∀ᵐ xy ∂μ.prod μ, |∑ i ∈ range M, U i xy.1| ≤ (M:ℝ)/2 :=
    Measure.quasiMeasurePreserving_fst.ae hB
  have hYB : ∀ᵐ xy ∂μ.prod μ, |∑ i ∈ range M, U i xy.2| ≤ (M:ℝ)/2 :=
    Measure.quasiMeasurePreserving_snd.ae hB
  have hfub := gaussian_fubini hX hY ((M:ℝ)/2) hXB hYB hα
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  have hlhs : ∀ z : ℂ, (((‖rE z ^ M‖ ^ 2 * fockDensity α z : ℝ)) : ℂ) =
      (∫ xy, cexp (I * z * ((∑ i ∈ range M, U i xy.1 : ℝ) : ℂ) -
        I * conj z * ((∑ i ∈ range M, U i xy.2 : ℝ) : ℂ)) ∂μ.prod μ) * (fockDensity α z : ℂ) := by
    intro z
    rw [ofReal_mul, norm_sq_rE_pow U hU hind hlaw z M]
  simp_rw [hlhs]
  rw [hfub]
  congr 1
  funext xy
  rw [ofReal_exp, ofReal_div, ofReal_mul]

/-- **Theorem 9.2, second equality**: the same norm equals the moment series
`∑_k (μ_{2k}^{[M]})^2 / ((2k)! α^{2k})`, with `μ_n^{[M]} = E S_M^n`. -/
theorem fock_norm_eq_moment_series
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (M : ℕ) {α : ℝ} (hα : 0 < α) :
    ∫ z : ℂ, ‖rE z ^ M‖ ^ 2 * fockDensity α z =
      ∑' k : ℕ, (∫ ω, (∑ i ∈ range M, U i ω) ^ (2*k) ∂μ) ^ 2 /
        (((2*k).factorial : ℝ) * α ^ (2*k)) := by
  rw [fock_norm_eq_probability_integral U hU hind hlaw M hα]
  have hS : Measurable (fun ω => ∑ i ∈ range M, U i ω) :=
    Finset.measurable_fun_sum (range M) (fun i _ => hU i)
  have hodd : ∀ k : ℕ, (∫ ω, (∑ i ∈ range M, U i ω) ^ (2*k+1) ∂μ) = 0 := by
    intro k
    rw [(V033.UniformSum.all_sum_moments U hU hind hlaw M _).2, V033.UniformSum.sumMoment_odd]
  have h := EulerianGrothendieck.bounded_product_exp_even_series
    (fun ω => ∑ i ∈ range M, U i ω) hS ((M:ℝ)/2) (1/α) (by positivity)
    (EulerianGrothendieck.uniform_sum_ae_bound U hU hlaw M) hodd
  have hcongr : (fun xy : Ω × Ω =>
      Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / α)) =
      (fun xy : Ω × Ω =>
      Real.exp (1/α * ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2)))) := by
    funext xy; congr 1; ring
  rw [hcongr, h]
  apply tsum_congr
  intro k
  have hα' : α ≠ 0 := hα.ne'
  rw [div_pow, one_pow]
  field_simp

/-- At the scale `α = c M` used throughout the asymptotic theory, the Fock norm is the
certified series `uniformNormSeries M (1/(12c))`. -/
theorem fock_norm_scaled_eq_uniformNormSeries
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    {c : ℝ} (hc : 0 < c) (M : ℕ) (hM : M ≠ 0) :
    ∫ z : ℂ, ‖rE z ^ M‖ ^ 2 * fockDensity (c * M) z = uniformNormSeries M (1/(12*c)) := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  rw [fock_norm_eq_probability_integral U hU hind hlaw M (mul_pos hc hMpos)]
  exact EulerianGrothendieck.raw_uniform_kernel_identity U hU hind hlaw c hc.ne' M hM

end EulerianGrothendieck.Fock
