import GegenbauerFock.PhyslibTraceClassNeumannQuasiregular
import GegenbauerFock.PhyslibTraceClassGeometricSumBound

/-!
# V007 — exact bridge between iterated Neumann corrections and positive powers

The Neumann quasiregular theorem uses the Mathlib ring series
    ∑' n, ((· * T)^[n]) T.
Our quantitative geometric truncation bounds use the explicit S₁ series
    ∑' n, positivePower T n.
This module proves these are the *same* trace-class elements and sums,
not merely equally convergent surrogate sequences.

Hence the geometrically bounded S₁ sum itself obeys both exact
nonunital Neumann identities, with no trace-class identity operator.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Each Mathlib nonunital Neumann iterate equals the already
certified genuine CFC positive power, at the same index. -/
theorem neumann_iterate_eq_positivePower (T : TraceClass H) (n : ℕ) :
    ((· * T)^[n]) T = positivePower T n := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id_eq, positivePower_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

/-- The iterated Neumann sum is exactly the same Schatten-S₁
Banach limit as the positive-power series of the truncation module. -/
theorem neumann_tsum_eq_positivePowers (T : TraceClass H) :
    (∑' n : ℕ, ((· * T)^[n]) T) =
      ∑' n : ℕ, positivePower T n := by
  apply tsum_congr
  intro n
  exact neumann_iterate_eq_positivePower T n

/-- The quantitatively controlled positive-power sum itself,
rather than a separately named Neumann sum, satisfies both
quasiregular identities in the nonunital CFC S₁ ring. -/
theorem positivePowers_two_sided_Neumann
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    (T + (∑' n : ℕ, positivePower T n) * T =
      ∑' n : ℕ, positivePower T n) ∧
    (T + T * (∑' n : ℕ, positivePower T n) =
      ∑' n : ℕ, positivePower T n) := by
  simpa only [neumann_tsum_eq_positivePowers] using
    (neumann_two_sided_identities T hsmall)

/-- Genuine S₁ norm of the correction obtained from either
Neumann notation, bounded by the sharp geometric majorant. -/
theorem neumann_tsum_traceNorm_le
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    traceNorm H (∑' n : ℕ, ((· * T)^[n]) T) ≤
      ‖T‖ / (1 - ‖T‖) := by
  rw [neumann_tsum_eq_positivePowers]
  exact positivePowers_total_traceNorm_le T hsmall

#print axioms ProbabilisticTheory.TraceClass.neumann_iterate_eq_positivePower
#print axioms ProbabilisticTheory.TraceClass.neumann_tsum_eq_positivePowers
#print axioms ProbabilisticTheory.TraceClass.positivePowers_two_sided_Neumann
#print axioms ProbabilisticTheory.TraceClass.neumann_tsum_traceNorm_le

end ProbabilisticTheory.TraceClass
