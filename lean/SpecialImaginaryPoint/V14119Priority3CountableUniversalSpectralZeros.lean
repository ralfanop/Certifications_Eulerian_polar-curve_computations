import SpecialImaginaryPoint.V14119Priority3LocallyFiniteFredholmZeroSet
import Mathlib.Topology.Compactness.Lindelof

/-!
# Priority 3 — countability of the entire complex spectral zero set
# of EVERY genuine universal CFC Schatten-S₁ Fredholm determinant

For arbitrary complex trace-class Hilbert T, including nonnormal
and nonselfadjoint cases, define its actual universal Fredholm
spectral zero set Z(T) = {z : ℂ | det_F(I+zT)=0}.

The previous module certifies the set is CLOSED, DISCRETE, and
intersects each bounded complex subset in only finitely many
points. We now also certify that Z(T) is COUNTABLE on the ENTIRE
unbounded complex plane: all subsets of ℂ are Lindelof (second
countable), and a discrete Lindelof subset must be countable.

This is structural operator-spectrum information, not a claim
that spectral zeros can be enumerated effectively or that any
particular trace-class operator has a zero.
-/

noncomputable section

namespace Manuscript14Priority3.CountableUniversalSpectralZeros

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.LocallyFiniteFredholmZeroSet

/-- Entire, potentially unbounded spectral zero set of any
genuine nonnormal CFC Schatten-S₁ Fredholm determinant is
COUNTABLE, with no normality, positivity or diagonal assumption. -/
theorem universalFredholmZeroSet_countable
    (T : ProbabilisticTheory.TraceClass H) :
    (universalFredholmZeroSet T).Countable := by
  exact (HereditarilyLindelofSpace.isLindelof
    (universalFredholmZeroSet T)).countable_of_isDiscrete
      (universalFredholmZeroSet_isDiscrete T)

#print axioms Manuscript14Priority3.CountableUniversalSpectralZeros.universalFredholmZeroSet_countable

end Manuscript14Priority3.CountableUniversalSpectralZeros
