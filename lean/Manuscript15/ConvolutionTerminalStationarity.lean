import Manuscript15.ConvolutionTerminalDerivatives

/-!
# Manuscript 15 — exact stationary/regular endpoint dichotomy

This theorem is a direct kernel-level consequence of the independently
certified convolution terminal velocity classification. It does not
assert the still-open higher-order endpoint contact jet.
-/

noncomputable section
namespace Manuscript15

/-- For every positive convolution order, the terminal velocity
vanishes precisely in the one-summand case or when the geometric
scale itself vanishes. -/
theorem convolution_terminal_stationary_iff
    (a : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    (deriv (XConv a M) (2 * Real.pi),
       deriv (YConv a M) (2 * Real.pi)) = (0, 0) ↔
      M = 1 ∨ a = 0 := by
  rw [convolution_terminal_velocity_classification a M hM]
  constructor
  · intro h
    by_cases hm : M = 1
    · exact Or.inl hm
    · right
      simpa [hm] using congrArg Prod.fst h
  · intro h
    rcases h with hm | ha
    · simp [hm]
    · simp [ha]

#print axioms Manuscript15.convolution_terminal_stationary_iff

end Manuscript15
