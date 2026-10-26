import Mathlib

/-!
# V007: uniform L² control for every polynomial moment functional

This is a direct theorem about a genuine probability L² Hilbert space
whose measure is supported in [-1,1]. The ultraspherical Beta-pushforward
measure is already proven to satisfy these hypotheses.

It establishes L² membership and an explicit ≤1 norm bound for each
unscaled monomial Riesz functional. Factorial-weighted summability of
the Fock coefficient family and the full operator norm remain separate.
-/

open MeasureTheory
open scoped InnerProduct

namespace GegenbauerFock.MomentL2

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]
variable (hsupport : ∀ᵐ u ∂μ, |u| ≤ (1 : ℝ))

/-- Each monomial is genuinely L²-integrable for the probability measure. -/
theorem monomial_memLp (n : ℕ) :
    MemLp (fun u : ℝ => (u : ℂ) ^ n) 2 μ := by
  have hc : Continuous (fun u : ℝ => (u : ℂ) ^ n) := by fun_prop
  apply MemLp.of_bound hc.aestronglyMeasurable 1
  filter_upwards [hsupport] with u hu
  calc
    ‖(u : ℂ) ^ n‖ = |u| ^ n := by simp
    _ ≤ (1 : ℝ) ^ n := by gcongr
    _ = 1 := by simp

/-- The actual L² equivalence class of the n-th monomial. -/
noncomputable def monomialLp (n : ℕ) : Lp ℂ 2 μ :=
  (monomial_memLp μ hsupport n).toLp (fun u : ℝ => (u : ℂ) ^ n)

/-- Uniform bound on all ultraspherical-style L² moments. -/
theorem monomialLp_norm_le_one (n : ℕ) :
    ‖monomialLp μ hsupport n‖ ≤ 1 := by
  have hae : ∀ᵐ u ∂μ, ‖(monomialLp μ hsupport n : ℝ → ℂ) u‖ ≤ 1 := by
    filter_upwards [(monomial_memLp μ hsupport n).coeFn_toLp, hsupport]
      with u he hu
    rw [he]
    calc
      ‖(u : ℂ) ^ n‖ = |u| ^ n := by simp
      _ ≤ (1 : ℝ) ^ n := by gcongr
      _ = 1 := by simp
  simpa using (Lp.norm_le_of_ae_bound (p := (2 : ℝ≥0∞))
    (μ := μ) (by norm_num : (0 : ℝ) ≤ 1) hae)

/-- A genuine bounded Riesz moment functional on L²(μ). -/
noncomputable def momentFunctional (n : ℕ) : Lp ℂ 2 μ →L[ℂ] ℂ :=
  innerSL ℂ (monomialLp μ hsupport n)

/-- Uniform operator norm bound for all moment coefficients. -/
theorem momentFunctional_norm_le_one (n : ℕ) :
    ‖momentFunctional μ hsupport n‖ ≤ 1 := by
  rw [momentFunctional, innerSL_apply_norm]
  exact monomialLp_norm_le_one μ hsupport n

/-- Concrete adjoint of each moment functional. -/
theorem momentFunctional_adjoint (n : ℕ) :
    (momentFunctional μ hsupport n).adjoint =
      ContinuousLinearMap.toSpanSingleton ℂ (monomialLp μ hsupport n) := by
  exact ContinuousLinearMap.adjoint_innerSL_apply _

#print axioms GegenbauerFock.MomentL2.monomial_memLp
#print axioms GegenbauerFock.MomentL2.monomialLp_norm_le_one
#print axioms GegenbauerFock.MomentL2.momentFunctional_norm_le_one
#print axioms GegenbauerFock.MomentL2.momentFunctional_adjoint

end GegenbauerFock.MomentL2
