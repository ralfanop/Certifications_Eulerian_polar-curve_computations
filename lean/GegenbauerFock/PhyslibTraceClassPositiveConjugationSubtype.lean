import GegenbauerFock.PhyslibTraceClassSandwichSubtype
import GegenbauerFock.PhyslibPositiveConjugationTraceNormBound

/-!
# V007 — quantitative positive conjugation on the true S₁ subtype

The positive trace-class conjugation inequality is transported to the
proof-carrying Physlib-compatible CFC TraceClass H carrier. The new
operation is the already-defined genuine sandwich, not an invented
normed-operator surrogate.

No general nonpositive sharp bilateral S₁ norm inequality, triangle
inequality, or Banach completeness is assumed.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Sharp trace-norm conjugation estimate on the actual proof-carrying
trace-class type for an arbitrary positive input. -/
theorem conjugate_traceNorm_le_of_nonneg
    (T : TraceClass H) (hT : 0 ≤ T.1)
    (B : H →L[ℂ] H) :
    traceNorm H (conjugate T B) ≤
      ‖B‖ ^ 2 * traceNorm H T := by
  change ProbabilisticTheory.traceNorm
      (B.adjoint * T.1 * B)
      (ProbabilisticTheory.isTraceClass_twoSided T.1 T.2 B.adjoint B) ≤
    ‖B‖ ^ 2 * ProbabilisticTheory.traceNorm T.1 T.2
  exact ProbabilisticTheory.positive_traceNorm_conjugation_le
    T.1 hT T.2 B

/-- Contractive congruence on the genuinely positive S₁ cone:
for any bounded contraction B, the true CFC trace norm cannot grow. -/
theorem conjugate_traceNorm_le_of_nonneg_contraction
    (T : TraceClass H) (hT : 0 ≤ T.1)
    (B : H →L[ℂ] H) (hB : ‖B‖ ≤ 1) :
    traceNorm H (conjugate T B) ≤ traceNorm H T := by
  have hs : ‖B‖ ^ 2 ≤ (1 : ℝ) := by
    simpa only [one_pow] using
      ((sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hB)
  calc
    traceNorm H (conjugate T B) ≤
        ‖B‖ ^ 2 * traceNorm H T :=
      conjugate_traceNorm_le_of_nonneg T hT B
    _ ≤ (1 : ℝ) * traceNorm H T :=
      mul_le_mul_of_nonneg_right hs (traceNorm_nonneg T)
    _ = traceNorm H T := one_mul _

#print axioms ProbabilisticTheory.TraceClass.conjugate_traceNorm_le_of_nonneg
#print axioms ProbabilisticTheory.TraceClass.conjugate_traceNorm_le_of_nonneg_contraction

end ProbabilisticTheory.TraceClass
