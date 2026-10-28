import GegenbauerFock.PhyslibTraceNormLowerSemicontinuity
import GegenbauerFock.PhyslibTraceClassNormedSpace

/-!
# V007 — operator-norm sequential closure of bounded S₁ trace-norm balls

An operator-norm limit of a sequence of genuine complex trace-class
operators in a fixed trace-norm closed ball belongs to the same ball,
with no finite-dimensional, positivity or common-basis restriction.

This sharp closure statement is independent of the pending
`CompleteSpace (TraceClass H)` instance. It is a consequence of the
already certified CFC trace-norm lower semicontinuity theorem.
-/

noncomputable section
namespace ProbabilisticTheory
open Filter

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bounded trace-norm ball in the genuine CFC S₁ subtype is
sequentially closed when viewed in the weaker operator norm on B(H).
The result constructs a proof-carrying S₁ limit element. -/
theorem traceClass_of_operator_limit_of_uniform_traceNorm_bound
    (u : ℕ → TraceClass H) (T : H →L[ℂ] H) (C : ℝ)
    (hbound : ∀ n, ‖u n‖ ≤ C)
    (htendsto : Tendsto (fun n => (u n).1) Filter.atTop (nhds T)) :
    ∃ V : TraceClass H, V.1 = T ∧ ‖V‖ ≤ C := by
  have hbound' : ∀ n,
      ProbabilisticTheory.traceNorm (u n).1 (u n).2 ≤ C := by
    intro n
    simpa only [TraceClass.norm_eq_genuineTraceNorm,
      TraceClass.traceNorm] using hbound n
  obtain ⟨hT, htr⟩ :=
    isTraceClass_of_tendsto_of_traceNorm_bounded_v007
      (fun n => (u n).2) hbound' htendsto
  refine ⟨⟨T, hT⟩, rfl, ?_⟩
  calc
    ‖(⟨T, hT⟩ : TraceClass H)‖ =
        TraceClass.traceNorm H (⟨T, hT⟩ : TraceClass H) :=
      TraceClass.norm_eq_genuineTraceNorm (⟨T, hT⟩ : TraceClass H)
    _ = ProbabilisticTheory.traceNorm T hT := rfl
    _ ≤ C := htr

#print axioms ProbabilisticTheory.traceClass_of_operator_limit_of_uniform_traceNorm_bound

end ProbabilisticTheory
