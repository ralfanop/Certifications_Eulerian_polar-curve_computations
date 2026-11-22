import PrivateApex.CardioidIdentities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
PRIVATE.  Manuscript 15: Eulerian Fourier reconstruction of the Mandelbrot cardioid.
Probabilistic representation.

* `unifLaw` is the uniform law on `[-1/2, 1/2]`, `unif01` the uniform law on `[0, 1]`;
* `charFun_unifLaw`: the characteristic function of `unifLaw` is `rE`;
* `charFun_unif01`, `charFun_unif01_eulerianB`: the characteristic function of `unif01` is
  `e^{iθ/2} rE θ`, which is the Eulerian factor `B(e^{iθ})` on the principal range;
* `triLaw` is the law of `1 + U₁ + U₂` (`U₁`, `U₂` independent with law `unifLaw`);
  `triLaw_eq` identifies it with the law of the sum of two independent uniform variables on
  `[0, 1]`;
* `cardioid_probabilistic`, `cardioid_expectation`:
  `c(θ) - 1/4 = (θ^2 / 4) E exp (i θ (1 + U₁ + U₂))`.
-/

namespace PrivateApex
namespace Cardioid
open Complex MeasureTheory ProbabilityTheory
open scoped Real

/-- The uniform law on `[-1/2, 1/2]`. -/
noncomputable def unifLaw : Measure ℝ := volume.restrict (Set.Icc (-(1 / 2) : ℝ) (1 / 2))

/-- The uniform law on `[0, 1]`. -/
noncomputable def unif01 : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unifLaw :=
  ⟨by rw [unifLaw, Measure.restrict_apply_univ, Real.volume_Icc]; norm_num⟩

instance : IsProbabilityMeasure unif01 :=
  ⟨by rw [unif01, Measure.restrict_apply_univ, Real.volume_Icc]; norm_num⟩

private theorem integral_exp_Icc {a b : ℝ} (hab : a ≤ b) {θ : ℝ} (hθ : θ ≠ 0) :
    ∫ x in Set.Icc a b, exp ((θ : ℂ) * x * I) =
      (exp ((θ : ℂ) * I * b) - exp ((θ : ℂ) * I * a)) / ((θ : ℂ) * I) := by
  have hc : (θ : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hθ) I_ne_zero
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    ← integral_exp_mul_complex hc]
  refine intervalIntegral.integral_congr fun x _ => ?_
  show exp ((θ : ℂ) * x * I) = exp ((θ : ℂ) * I * x)
  congr 1; ring

/-- The characteristic function of the uniform law on `[-1/2, 1/2]` is `r_E`. -/
theorem charFun_unifLaw (θ : ℝ) : charFun unifLaw θ = (rE θ : ℂ) := by
  by_cases h : θ = 0
  · subst h; simp [rE_zero]
  · have hc : (θ : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast h) I_ne_zero
    rw [charFun_apply_real, unifLaw, integral_exp_Icc (by norm_num) h]
    have e1 : exp ((θ : ℂ) * I * ((1 / 2 : ℝ) : ℂ)) = exp (((θ / 2 : ℝ) : ℂ) * I) := by
      congr 1; push_cast; ring
    have e2 : exp ((θ : ℂ) * I * ((-(1 / 2) : ℝ) : ℂ)) = exp (-(((θ / 2 : ℝ) : ℂ)) * I) := by
      congr 1; push_cast; ring
    have hs := sin_half_cast θ
    rw [Complex.ofReal_sin, Complex.sin] at hs
    have hI : I * I = -1 := Complex.I_mul_I
    rw [e1, e2, div_eq_iff hc]
    linear_combination (2 * I) * hs +
      (exp (((θ / 2 : ℝ) : ℂ) * I) - exp (-(((θ / 2 : ℝ) : ℂ)) * I)) * hI

/-- The characteristic function of the uniform law on `[0, 1]` is `e^{iθ/2} r_E(θ)`. -/
theorem charFun_unif01 (θ : ℝ) :
    charFun unif01 θ = exp (((θ / 2 : ℝ) : ℂ) * I) * (rE θ : ℂ) := by
  by_cases h : θ = 0
  · subst h; simp [rE_zero]
  · have hθ : (θ : ℂ) ≠ 0 := by exact_mod_cast h
    rw [charFun_apply_real, unif01, integral_exp_Icc zero_le_one h]
    have e1 : exp ((θ : ℂ) * I * ((1 : ℝ) : ℂ)) - exp ((θ : ℂ) * I * ((0 : ℝ) : ℂ)) =
        exp ((θ : ℂ) * I) - 1 := by simp
    rw [e1, exp_sub_one, sin_half_cast]
    field_simp

/-- On the principal range the Eulerian factor `B(e^{iθ})` is the characteristic function of
the uniform law on `[0, 1]`. -/
theorem charFun_unif01_eulerianB {θ : ℝ} (h1 : -π < θ) (h2 : θ ≤ π) :
    charFun unif01 θ = eulerianB (exp ((θ : ℂ) * I)) := by
  rw [charFun_unif01, eulerianB_exp h1 h2]

/-- The law of `1 + U₁ + U₂`, with `U₁`, `U₂` independent and uniform on `[-1/2, 1/2]`. -/
noncomputable def triLaw : Measure ℝ := (unifLaw ∗ unifLaw).map (fun x => 1 + x)

instance : IsProbabilityMeasure triLaw :=
  (Measure.isProbabilityMeasure_map_iff (Measurable.aemeasurable (by fun_prop))).mpr inferInstance

theorem charFun_map_one_add (μ : Measure ℝ) (θ : ℝ) :
    charFun (μ.map (fun x => 1 + x)) θ = exp ((θ : ℂ) * I) * charFun μ θ := by
  rw [charFun_apply_real, charFun_apply_real,
    integral_map (by fun_prop) (Continuous.aestronglyMeasurable (by fun_prop)),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show exp ((θ : ℂ) * ((1 + x : ℝ) : ℂ) * I) = exp ((θ : ℂ) * I) * exp ((θ : ℂ) * x * I)
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- The characteristic function of `1 + U₁ + U₂` is `e^{iθ} r_E(θ)^2`. -/
theorem charFun_triLaw (θ : ℝ) : charFun triLaw θ = exp ((θ : ℂ) * I) * (rE θ : ℂ) ^ 2 := by
  rw [triLaw, charFun_map_one_add, charFun_conv, charFun_unifLaw]; ring

/-- `1 + U₁ + U₂` has the law of the sum of two independent uniform variables on `[0, 1]`. -/
theorem triLaw_eq : triLaw = unif01 ∗ unif01 := by
  apply Measure.ext_of_charFun
  ext θ
  rw [charFun_triLaw, charFun_conv, charFun_unif01, exp_half_sq' θ]; ring

/-- Probabilistic form of the reconstruction:
`c(θ) - 1/4 = (θ^2 / 4) E exp (i θ (1 + U₁ + U₂))`, in terms of the law of `1 + U₁ + U₂`. -/
theorem cardioid_probabilistic (θ : ℝ) :
    cardioid θ - 1 / 4 = (θ : ℂ) ^ 2 / 4 * charFun triLaw θ := by
  rw [cardioid_eulerian, charFun_triLaw]; ring

/-- The same statement for random variables on an arbitrary probability space. -/
theorem cardioid_expectation {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {U₁ U₂ : Ω → ℝ} (m₁ : Measurable U₁) (m₂ : Measurable U₂)
    (hind : IndepFun U₁ U₂ P) (l₁ : P.map U₁ = unifLaw) (l₂ : P.map U₂ = unifLaw) (θ : ℝ) :
    cardioid θ - 1 / 4 =
      (θ : ℂ) ^ 2 / 4 * ∫ ω, exp ((θ : ℂ) * ((1 + (U₁ ω + U₂ ω) : ℝ) : ℂ) * I) ∂P := by
  have h1 : P.map (U₁ + U₂) = unifLaw ∗ unifLaw := by
    rw [hind.map_add_eq_map_conv_map₀ m₁.aemeasurable m₂.aemeasurable, l₁, l₂]
  have hlaw : P.map (fun ω => 1 + (U₁ ω + U₂ ω)) = triLaw := by
    rw [triLaw, ← h1, Measure.map_map (by fun_prop) (m₁.add m₂)]
    rfl
  rw [cardioid_probabilistic, ← hlaw, charFun_apply_real,
    integral_map (by fun_prop) (Continuous.aestronglyMeasurable (by fun_prop))]

end Cardioid
end PrivateApex
