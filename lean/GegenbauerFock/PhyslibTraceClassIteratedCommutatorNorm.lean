import GegenbauerFock.PhyslibTraceClassCommutatorNormSharp

/-!
# V007 — finite iterated commutator estimate in genuine CFC Schatten S₁

From the sharp bounded commutator estimate, we obtain for every n:
  ‖ad_A^n(T)‖₁ ≤ (2 ‖A‖)^n ‖T‖₁.

This holds on *all* complete complex Hilbert spaces, including the
zero-dimensional case, and for arbitrary non-selfadjoint T in the
actual CFC trace class. No series convergence is claimed. It uses
the previously independently checked two-sided ideal norm, not any
unverified exponential-functional-calculus statement.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem traceNorm_iteratedCommutator_le
    (A T : H →L[ℂ] H) (hT : IsTraceClass T) (n : ℕ) :
    traceNorm (iteratedCommutator A T n)
        (isTraceClass_iteratedCommutator A T hT n) ≤
      (2 * ‖A‖) ^ n * traceNorm T hT := by
  induction n with
  | zero =>
      simpa only [iteratedCommutator_zero, pow_zero, one_mul]
        using (le_refl (traceNorm T hT))
  | succ n ih =>
      let U : H →L[ℂ] H := iteratedCommutator A T n
      let hU : IsTraceClass U :=
        isTraceClass_iteratedCommutator A T hT n
      have hstep : traceNorm (iteratedCommutator A T (n + 1))
          (isTraceClass_iteratedCommutator A T hT (n + 1)) ≤
          2 * ‖A‖ * traceNorm U hU := by
        simpa only [iteratedCommutator_succ] using
          (traceNorm_commutator_le A U hU)
      calc
        traceNorm (iteratedCommutator A T (n + 1))
            (isTraceClass_iteratedCommutator A T hT (n + 1)) ≤
            2 * ‖A‖ * traceNorm U hU := hstep
        _ ≤ 2 * ‖A‖ * ((2 * ‖A‖) ^ n * traceNorm T hT) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (2 * ‖A‖) ^ (n + 1) * traceNorm T hT := by
          rw [pow_succ]
          ring

#print axioms ProbabilisticTheory.traceNorm_iteratedCommutator_le

end ProbabilisticTheory
