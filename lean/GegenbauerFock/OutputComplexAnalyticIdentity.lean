import GegenbauerFock.OutputComplexHolomorphy
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# V007 — analytic identity on the genuine imaginary-axis Fock restriction

An entire complex function vanishing along the ultraspherical open
imaginary interval must vanish globally. The proof supplies an explicit
accumulation point of zeros, rather than treating the real interval as
an open complex set.

The further coefficient-uniqueness step remains separate.
-/

noncomputable section

open Set
open scoped ENNReal InnerProduct

namespace GegenbauerFock.FockAnalyticRestriction

/-- Identity theorem for an entire function which vanishes on the
actual scaled imaginary-axis segment used by the Fock adjoint. -/
theorem entire_eq_zero_of_imaginary_interior_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hzero : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, f (imaginaryPoint alpha u) = 0) :
    f = 0 := by
  have hanalytic : AnalyticOnNhd ℂ f Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have hclosure : (0 : ℂ) ∈
      closure ({z : ℂ | f z = 0} \ ({0} : Set ℂ)) := by
    apply (mem_closure_iff_nhds).2
    intro s hs
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
    let u : ℝ := min (1 / 2 : ℝ) (ε * alpha)
    have hu : 0 < u := by
      dsimp [u]
      exact lt_min (by norm_num) (mul_pos hε ha)
    have hu_le : u ≤ ε * alpha := by
      dsimp [u]
      exact min_le_right _ _
    have hu_lt : u < 1 := by
      calc
        u ≤ (1 / 2 : ℝ) := min_le_left _ _
        _ < 1 := by norm_num
    have hmem : u ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hu_lt⟩
    have hnorm : ‖imaginaryPoint alpha u‖ < ε := by
      rw [norm_imaginaryPoint alpha u ha, abs_of_pos hu]
      apply (div_lt_iff₀ (by positivity : 0 < 2 * alpha)).mpr
      have hεα : 0 < ε * alpha := mul_pos hε ha
      nlinarith
    have hb : imaginaryPoint alpha u ∈ Metric.ball (0 : ℂ) ε := by
      simpa [Metric.mem_ball, dist_zero_right] using hnorm
    have hz_ne : imaginaryPoint alpha u ≠ 0 := by
      intro hz
      have hn := norm_imaginaryPoint alpha u ha
      rw [hz, norm_zero, abs_of_pos hu] at hn
      have hp : 0 < u / (2 * alpha) :=
        div_pos hu (by positivity)
      linarith
    exact ⟨imaginaryPoint alpha u,
      ⟨hball hb, ⟨hzero u hmem, by simpa using hz_ne⟩⟩⟩
  have hident : Set.EqOn f 0 Set.univ :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure
      hanalytic isPreconnected_univ (Set.mem_univ (0 : ℂ)) hclosure
  funext z
  exact hident (Set.mem_univ z)

/-- Entire coherent evaluation is globally zero if its actual
imaginary-axis restriction vanishes on the ultraspherical interior. -/
theorem complex_evaluation_eq_zero_of_interior_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients)
    (hzero : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, evaluate alpha ha F u = 0) :
    (fun z : ℂ => FockEvaluation.evaluation alpha ha z F) = 0 := by
  apply entire_eq_zero_of_imaginary_interior_zero alpha ha
    (fun z : ℂ => FockEvaluation.evaluation alpha ha z F)
    (FockEvaluation.differentiable_evaluation_complex alpha ha F)
  intro u hu
  exact hzero u hu

#print axioms GegenbauerFock.FockAnalyticRestriction.entire_eq_zero_of_imaginary_interior_zero
#print axioms GegenbauerFock.FockAnalyticRestriction.complex_evaluation_eq_zero_of_interior_zero

end GegenbauerFock.FockAnalyticRestriction

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- An element of the genuine Gegenbauer–Fock adjoint kernel has
identically zero entire coherent reconstruction. Coefficient extraction
is a subsequent, independent obligation. -/
theorem C_adjoint_zero_implies_complex_evaluation_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients)
    (hz : C_adjoint lam alpha hlam ha F = 0) :
    (fun z : ℂ => FockEvaluation.evaluation alpha ha z F) = 0 := by
  exact FockAnalyticRestriction.complex_evaluation_eq_zero_of_interior_zero
    alpha ha F
    ((C_adjoint_eq_zero_iff_interior_zero lam alpha hlam ha F).mp hz)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_zero_implies_complex_evaluation_zero

end GegenbauerFock.GeneralUltrasphericalFock
