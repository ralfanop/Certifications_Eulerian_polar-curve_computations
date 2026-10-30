import EulerianGrothendieck.UniformNormAsymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Identification with the actual exponential product-law integral, using
bounded random variables and dominated convergence of the exponential series. -/
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Finset Filter
namespace EulerianGrothendieck
set_option maxHeartbeats 1000000

theorem real_exp_hasSum (x : ℝ) :
    HasSum (fun n : ℕ => x^n/(n.factorial:ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp ℝ x

theorem bounded_exp_integral_hasSum
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (B t : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ B) :
    HasSum (fun n : ℕ => (t^n/(n.factorial:ℝ))*(∫ ω, X ω^n ∂μ))
      (∫ ω, Real.exp (t*X ω) ∂μ) := by
  have h : HasSum (fun n : ℕ => ∫ ω, (t*X ω)^n/(n.factorial:ℝ) ∂μ)
      (∫ ω, Real.exp (t*X ω) ∂μ) := hasSum_integral_of_dominated_convergence
    (fun n (_ : Ω) => (|t| * B)^n/(n.factorial:ℝ))
    (fun n => (((hX.const_mul t).pow_const n).div_const (n.factorial:ℝ)).aestronglyMeasurable)
    (fun n => by
      filter_upwards [hbound] with ω hω
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ n.factorial)]
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hω (abs_nonneg t)) n)
        (by positivity))
    (Filter.Eventually.of_forall (fun ω => (real_exp_hasSum (|t| * B)).summable))
    (by simpa only [(real_exp_hasSum (|t| * B)).tsum_eq] using
      (integrable_const (Real.exp (|t| * B)) : Integrable (fun _ : Ω => Real.exp (|t| * B)) μ))
    (Filter.Eventually.of_forall (fun ω => real_exp_hasSum (t*X ω)))
  convert h using 1
  ext n
  simp only [mul_pow]
  rw [show (fun ω => t^n*X ω^n/(n.factorial:ℝ)) =
      (fun ω => (t^n/(n.factorial:ℝ))*X ω^n) by funext ω; ring,
    integral_const_mul]

theorem bounded_product_exp_even_series
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ : Measurable Z) (B t : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ B)
    (hodd : ∀ k : ℕ, (∫ ω, Z ω^(2*k+1) ∂μ) = 0) :
    (∫ xy, Real.exp (t*(Z xy.1*Z xy.2)) ∂μ.prod μ) =
      ∑' k : ℕ, (t^(2*k)/((2*k).factorial:ℝ))*(∫ ω, Z ω^(2*k) ∂μ)^2 := by
  have hZprod : Measurable (fun xy : Ω×Ω => Z xy.1*Z xy.2) :=
    (hZ.comp measurable_fst).mul (hZ.comp measurable_snd)
  have hb : ∀ᵐ xy ∂μ.prod μ, |Z xy.1*Z xy.2| ≤ B^2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hbound,
      Measure.quasiMeasurePreserving_snd.ae hbound] with xy hx hy
    rw [abs_mul, pow_two]
    exact mul_le_mul hx hy (abs_nonneg _) hB
  have h := bounded_exp_integral_hasSum (fun xy : Ω×Ω => Z xy.1*Z xy.2)
    hZprod (B^2) t (sq_nonneg B) hb
  have he : ∀ n : ℕ, (∫ xy, (Z xy.1*Z xy.2)^n ∂μ.prod μ) = (∫ ω, Z ω^n ∂μ)^2 := by
    intro n
    simp_rw [mul_pow]
    rw [integral_prod_mul (fun ω => Z ω^n) (fun ω => Z ω^n), pow_two]
  simp_rw [he] at h
  let f := fun n : ℕ => (t^n/(n.factorial:ℝ))*(∫ ω, Z ω^n ∂μ)^2
  have hfe : Summable (fun k => f (2*k)) := h.summable.comp_injective (i := fun k : ℕ => 2*k) (by intro a b h; dsimp only at h; omega)
  have hfo : Summable (fun k => f (2*k+1)) := h.summable.comp_injective (i := fun k : ℕ => 2*k+1) (by intro a b h; dsimp only at h; omega)
  have hsplit := tsum_even_add_odd hfe hfo
  have hz : (∑' k, f (2*k+1)) = 0 := by simp [f, hodd]
  rw [hz, add_zero] at hsplit
  rw [← h.tsum_eq]
  exact hsplit.symm

end EulerianGrothendieck
