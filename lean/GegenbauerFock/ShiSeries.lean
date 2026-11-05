import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The hyperbolic sine integral and its power series

`Shi x = ∫₀ˣ sinh t / t dt`, and for every real `x`
`Shi x = ∑ₖ x^{2k+1} / ((2k+1)! (2k+1))` (`hasSum_shi`), obtained by integrating the sinh series
term by term on `[0, x]`.
-/

noncomputable section

open MeasureTheory Real intervalIntegral

namespace GegenbauerFock.Shi

/-- The hyperbolic sine integral `Shi x = ∫₀ˣ sinh t / t dt`. -/
def Shi (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, Real.sinh t / t

/-- `t ↦ t^{2k} / (2k+1)!` as a continuous map. -/
def term (k : ℕ) : C(ℝ, ℝ) := ⟨fun t => t ^ (2 * k) / ((2 * k + 1).factorial : ℝ), by fun_prop⟩

theorem summable_term_norm (x : ℝ) :
    Summable fun k : ℕ =>
      ‖(term k).restrict (⟨Set.uIcc 0 x, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
  have hs : Summable fun k : ℕ => |x| ^ (2 * k) / ((2 * k).factorial : ℝ) :=
    (Real.summable_pow_div_factorial |x|).comp_injective (mul_right_injective₀ two_ne_zero)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hs
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_
  have ht : |(t : ℝ)| ≤ |x| := by
    have h : (t : ℝ) ∈ Set.uIcc 0 x := t.2
    rw [Set.mem_uIcc] at h
    rw [abs_le]
    rcases h with h | h <;> constructor <;>
      cases abs_cases x <;> linarith [h.1, h.2]
  simp only [ContinuousMap.restrict_apply, term, ContinuousMap.coe_mk, Real.norm_eq_abs,
    abs_div, abs_pow, Nat.abs_cast]
  have hf : ((2 * k).factorial : ℝ) ≤ ((2 * k + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ _)
  have hf0 : (0 : ℝ) < ((2 * k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  calc |(t : ℝ)| ^ (2 * k) / ((2 * k + 1).factorial : ℝ)
      ≤ |x| ^ (2 * k) / ((2 * k + 1).factorial : ℝ) := by
        gcongr
    _ ≤ |x| ^ (2 * k) / ((2 * k).factorial : ℝ) := by
        gcongr

theorem sinh_div_hasSum {t : ℝ} (ht : t ≠ 0) :
    HasSum (fun k : ℕ => t ^ (2 * k) / ((2 * k + 1).factorial : ℝ)) (Real.sinh t / t) := by
  have h := (Real.hasSum_sinh t).div_const t
  convert h using 1
  funext k
  rw [pow_succ]
  field_simp

/-- **Series of the hyperbolic sine integral.** -/
theorem hasSum_shi (x : ℝ) :
    HasSum (fun k : ℕ => x ^ (2 * k + 1) / (((2 * k + 1).factorial : ℝ) * (2 * k + 1)))
      (Shi x) := by
  have h := hasSum_intervalIntegral_of_summable_norm (a := 0) (b := x) (summable_term_norm x)
  have hint : ∀ k : ℕ, ∫ t in (0 : ℝ)..x, term k t =
      x ^ (2 * k + 1) / (((2 * k + 1).factorial : ℝ) * (2 * k + 1)) := by
    intro k
    simp only [term, ContinuousMap.coe_mk]
    rw [intervalIntegral.integral_div, integral_pow]
    push_cast
    field_simp
    ring
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc 0 x →
      ∑' k : ℕ, term k t = Real.sinh t / t := by
    have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [h0] with t ht _
    exact (sinh_div_hasSum ht).tsum_eq
  rw [intervalIntegral.integral_congr_ae hae] at h
  have h' : HasSum (fun k : ℕ => ∫ t in (0 : ℝ)..x, term k t) (Shi x) := h
  have hfun : (fun k : ℕ => ∫ t in (0 : ℝ)..x, term k t) =
      fun k : ℕ => x ^ (2 * k + 1) / (((2 * k + 1).factorial : ℝ) * (2 * k + 1)) := funext hint
  rw [hfun] at h'
  exact h'

end GegenbauerFock.Shi
