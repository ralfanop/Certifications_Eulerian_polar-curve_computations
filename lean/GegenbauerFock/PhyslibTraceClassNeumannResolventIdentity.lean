import GegenbauerFock.PhyslibTraceClassNeumannAmbientInverse
import GegenbauerFock.PhyslibTraceClassOperatorEmbedding

/-!
# V007 — the two-point Neumann resolvent identity in ambient B(H)

For any two genuine CFC Schatten-S₁ contractions T,U, put
  R_T := I + neumannCorrection(T)
  R_U := I + neumannCorrection(U).
The already kernel-certified inverse equations imply the
noncommutative resolvent identity

  S_T - S_U = R_T (T-U) R_U,

where S_T and S_U are themselves trace class.  Taking operator
norms yields a quantitative, dimension-independent stability
estimate involving the two explicitly defined inverses.

We do not presume that I lies in S₁ or that T and U commute.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact noncommutative two-point ambient Neumann-resolvent identity. -/
theorem neumann_ambient_resolvent_identity
    (T U : TraceClass H) (hT : ‖T‖ < 1) (hU : ‖U‖ < 1) :
    (neumannCorrection T).1 - (neumannCorrection U).1 =
      ((1 : H →L[ℂ] H) + (neumannCorrection T).1) *
      (T.1 - U.1) *
      ((1 : H →L[ℂ] H) + (neumannCorrection U).1) := by
  let a : H →L[ℂ] H := 1 - T.1
  let b : H →L[ℂ] H := 1 - U.1
  let x : H →L[ℂ] H := 1 + (neumannCorrection T).1
  let y : H →L[ℂ] H := 1 + (neumannCorrection U).1
  have ha : x * a = 1 := (neumann_ambient_two_sided_inverse T hT).2
  have hb : b * y = 1 := (neumann_ambient_two_sided_inverse U hU).1
  have hba : b - a = T.1 - U.1 := by
    dsimp [a, b]
    abel
  have hxy : x - y = x * (b - a) * y := by
    calc
      x - y = x * (b * y) - (x * a) * y := by rw [hb, ha, mul_one, one_mul]
      _ = x * (b - a) * y := by
        simp only [mul_sub, sub_mul, mul_assoc]
  calc
    (neumannCorrection T).1 - (neumannCorrection U).1 = x - y := by
      dsimp [x, y]
      abel
    _ = x * (b - a) * y := hxy
    _ = ((1 : H →L[ℂ] H) + (neumannCorrection T).1) *
        (T.1 - U.1) *
        ((1 : H →L[ℂ] H) + (neumannCorrection U).1) := by
      rw [hba]

/-- The true two-sided Neumann resolvent is locally stable in the
ambient operator norm without commutativity or positivity. -/
theorem neumann_ambient_resolvent_norm_le
    (T U : TraceClass H) (hT : ‖T‖ < 1) (hU : ‖U‖ < 1) :
    ‖(neumannCorrection T).1 - (neumannCorrection U).1‖ ≤
      (‖(1 : H →L[ℂ] H) + (neumannCorrection T).1‖ *
        ‖T.1 - U.1‖) *
      ‖(1 : H →L[ℂ] H) + (neumannCorrection U).1‖ := by
  rw [neumann_ambient_resolvent_identity T U hT hU]
  calc
    ‖(((1 : H →L[ℂ] H) + (neumannCorrection T).1) *
      (T.1 - U.1)) * (1 + (neumannCorrection U).1)‖ ≤
      ‖((1 : H →L[ℂ] H) + (neumannCorrection T).1) *
        (T.1 - U.1)‖ *
      ‖(1 : H →L[ℂ] H) + (neumannCorrection U).1‖ :=
        norm_mul_le _ _
    _ ≤ (‖(1 : H →L[ℂ] H) + (neumannCorrection T).1‖ *
        ‖T.1 - U.1‖) *
      ‖(1 : H →L[ℂ] H) + (neumannCorrection U).1‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)

/-- In particular the perturbation is controlled by the genuine
CFC trace norm of T-U (not just by its ambient operator norm). -/
theorem neumann_ambient_resolvent_traceNorm_le
    (T U : TraceClass H) (hT : ‖T‖ < 1) (hU : ‖U‖ < 1) :
    ‖(neumannCorrection T).1 - (neumannCorrection U).1‖ ≤
      (‖(1 : H →L[ℂ] H) + (neumannCorrection T).1‖ *
        traceNorm H (T - U)) *
      ‖(1 : H →L[ℂ] H) + (neumannCorrection U).1‖ := by
  have hdiff : ‖T.1 - U.1‖ ≤ traceNorm H (T - U) := by
    simpa only [sub_operator] using
      (operator_norm_le_trace_norm (T - U))
  calc
    ‖(neumannCorrection T).1 - (neumannCorrection U).1‖ ≤
        (‖(1 : H →L[ℂ] H) + (neumannCorrection T).1‖ *
          ‖T.1 - U.1‖) *
        ‖(1 : H →L[ℂ] H) + (neumannCorrection U).1‖ :=
          neumann_ambient_resolvent_norm_le T U hT hU
    _ ≤ (‖(1 : H →L[ℂ] H) + (neumannCorrection T).1‖ *
          traceNorm H (T - U)) *
        ‖(1 : H →L[ℂ] H) + (neumannCorrection U).1‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)

#print axioms ProbabilisticTheory.TraceClass.neumann_ambient_resolvent_identity
#print axioms ProbabilisticTheory.TraceClass.neumann_ambient_resolvent_norm_le
#print axioms ProbabilisticTheory.TraceClass.neumann_ambient_resolvent_traceNorm_le

end ProbabilisticTheory.TraceClass
