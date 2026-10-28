import GegenbauerFock.PhyslibTraceClassIdealNormSharp
import GegenbauerFock.PhyslibTraceClassCommutatorIdeal
import GegenbauerFock.PhyslibTraceClassNormedSpace

/-!
# V007 — quantitative commutator bounds in the genuine CFC trace norm

Assuming the independent, not-yet-CI-certified general sharp S₁ ideal
norm inequality, we derive the familiar operator-ideal commutator
bound

  traceNorm (A*T - T*A) ≤ 2 * ‖A‖ * traceNorm T

for arbitrary complex trace-class T, bounded A, and no positivity or
finite-rank restriction. The proof uses the *actual* normed CFC S₁
subtype, not an abstract trace norm surrogate.

This candidate is independently compiled and axiom-audited; it makes
no Banach-completeness assumption or claim.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The quantitative bounded-commutator inequality with coefficient 2
in the genuine Physlib-compatible CFC Schatten-S₁ norm. -/
theorem traceNorm_commutator_le
    (A T : H →L[ℂ] H) (hT : IsTraceClass T) :
    traceNorm (A * T - T * A) (isTraceClass_commutator A T hT) ≤
      2 * ‖A‖ * traceNorm T hT := by
  let X : TraceClass H :=
    ⟨A * T, isTraceClass_mul_left T hT A⟩
  let Y : TraceClass H :=
    ⟨T * A, isTraceClass_mul_right T hT A⟩
  let Z : TraceClass H :=
    ⟨A * T - T * A, isTraceClass_commutator A T hT⟩
  have hZ : Z = X - Y := by
    apply Subtype.ext
    change A * T - T * A = A * T - T * A
    rfl
  have htriangle : ‖Z‖ ≤ ‖X‖ + ‖Y‖ := by
    rw [hZ]
    exact norm_sub_le X Y
  have hX : ‖X‖ ≤ ‖A‖ * traceNorm T hT := by
    change traceNorm (A * T) (isTraceClass_mul_left T hT A) ≤ _
    simpa only [mul_one, norm_one, mul_one] using
      (traceNorm_twoSided_le T A 1 hT)
  have hY : ‖Y‖ ≤ ‖A‖ * traceNorm T hT := by
    change traceNorm (T * A) (isTraceClass_mul_right T hT A) ≤ _
    simpa only [one_mul, norm_one] using
      (traceNorm_twoSided_le T 1 A hT)
  change ‖Z‖ ≤ 2 * ‖A‖ * traceNorm T hT
  nlinarith

#print axioms ProbabilisticTheory.traceNorm_commutator_le

end ProbabilisticTheory
