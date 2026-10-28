import GegenbauerFock.PhyslibTraceClassNonUnitalBanachRing
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# V007 — nonunital Schatten S₁ Neumann identities and quasiregularity

For the genuine CFC complex Schatten trace-class Banach algebra,
a strict trace-norm contraction T has a summable nonunital
geometric series S = ∑' n, (· * T)^[n] T.

The two rigorous identities T + S*T = S and T + T*S = S
express the Neumann resolvent *correction* without assuming
that the identity is trace class in infinite dimension.

They also certify quasiregularity of -T in the actual Mathlib
nonunital normed-ring structure.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Geometric powers are summable in the actual CFC Schatten S₁ Banach ring. -/
theorem neumann_iterates_summable
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    Summable ((· * T)^[·] T) :=
  summable_iterate_mul_of_norm_lt_one hsmall

/-- Two-sided nonunital Neumann identities for the geometric
correction S, valid for nonnormal and nonpositive trace-class T. -/
theorem neumann_two_sided_identities
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    (T + (∑' n : ℕ, (· * T)^[n] T) * T =
      ∑' n : ℕ, (· * T)^[n] T) ∧
    (T + T * (∑' n : ℕ, (· * T)^[n] T) =
      ∑' n : ℕ, (· * T)^[n] T) := by
  have hs : Summable ((· * T)^[·] T) :=
    neumann_iterates_summable T hsmall
  exact ⟨hs.add_geom_series_mul_self, hs.add_self_mul_geom_series⟩

/-- A strict trace-norm contraction has a quasiregular negative
in the nonunital trace-class ring. No S₁ identity is asserted. -/
theorem neumann_negative_quasiregular
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    IsQuasiregular (-T) :=
  (summable_iterate_mul_iff_isQuasiregular hsmall).mp
    (neumann_iterates_summable T hsmall)

#print axioms ProbabilisticTheory.TraceClass.neumann_iterates_summable
#print axioms ProbabilisticTheory.TraceClass.neumann_two_sided_identities
#print axioms ProbabilisticTheory.TraceClass.neumann_negative_quasiregular

end ProbabilisticTheory.TraceClass
