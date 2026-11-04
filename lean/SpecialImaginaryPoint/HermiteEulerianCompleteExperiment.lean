import SpecialImaginaryPoint.HermiteLindemannPrExperiment
import SpecialImaginaryPoint.EulerianTranscendenceReduction

/-!
# Manuscript 14.10, sole Theorem 11.1 — experimental end-to-end Lean certificate

The sole deep upstream input is Mathlib PR #28013 `transcendental_exp`.
This proof is deliberately isolated on the separate experiment branch,
which uses Lean v4.36.0-rc2 and fork Mathlib commit 54fbfba6.
No additional axioms and no merge to the officially pinned PR #30.
-/

namespace Manuscript14Section11

open scoped Topology

/-- Full Theorem 11.1: the genuine Eulerian value has the established
floor-driven greedy block, the adjacent unique trinomial roots and the
exact orbit jump/defect; it is also transcendental and has an
infinite, not eventually periodic greedy expansion. -/
theorem eulerian_14_10_theorem11_1_complete :
  ((greedyDigit eulerianParameter 0 = 1 ∧
      (∀ k : ℕ, k < 30 → greedyDigit eulerianParameter (k + 1) = 0) ∧
      greedyDigit eulerianParameter 31 = 1) ∧
    ((313240 : ℝ) / 10 ^ 9 <
      1 - (greedyMap eulerianParameter)^[31] 1 ∧
      1 - (greedyMap eulerianParameter)^[31] 1 <
        (313241 : ℝ) / 10 ^ 9) ∧
    (∃ beta32 beta31 : ℝ,
      (1 < beta32 ∧ beta32 < 2 ∧ beta32 ^ 32 - beta32 ^ 31 - 1 = 0) ∧
      (1 < beta31 ∧ beta31 < 2 ∧ beta31 ^ 31 - beta31 ^ 30 - 1 = 0) ∧
      beta32 < eulerianParameter ∧ eulerianParameter < beta31 ∧
      (greedyMap beta31)^[31] 1 = 0 ∧
      Filter.Tendsto (fun beta : ℝ => (greedyMap beta)^[31] 1)
        (𝓝[<] beta31) (𝓝 (1 : ℝ)))) ∧
  (¬ IsAlgebraic ℚ eulerianParameter) ∧
  (¬ ∃ m p : ℕ, 0 < p ∧ ∀ n, m ≤ n →
     greedyDigit eulerianParameter (n + p) =
       greedyDigit eulerianParameter n) := by
  have hexp : ¬ IsAlgebraic ℚ (Real.exp (1 / Real.sqrt 2)) :=
    Manuscript14LindemannExperiment.exp_one_div_sqrt_two_transcendental
  exact ⟨eulerian_parry_dynamical_part_unconditional,
    eulerian_parameter_transcendental_of_exp hexp,
    eulerian_greedy_aperiodic_of_exp_transcendental hexp⟩

#print axioms Manuscript14Section11.eulerian_14_10_theorem11_1_complete

end Manuscript14Section11
