import SpecialImaginaryPoint.V14119Priority3UniversalIsolatedSpectralZeros
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.DiscreteSubset

/-!
# Priority 3 — locally finite spectral zero divisor for every true CFC-S₁ Fredholm determinant

For an arbitrary genuine complex CFC Schatten-S₁ Hilbert operator
T, the complete spectral zero set
  Z_T = { z ∈ ℂ | det_F(I + z T) = 0 }
is closed, discrete, and has FINITELY MANY zeros in EVERY bounded
subset of the complex spectral plane.

No selfadjointness, normality, positivity, finite-rank or
invertibility assumptions are used. This is a genuine spectral
finiteness theorem on the *universal* Hilbert compression-limit
Fredholm determinant, not on an auxiliary scalar product.

Proof ingredients:
* entire holomorphy => closed spectral zero set;
* universal isolated-zero theorem => discrete subset;
* metric properness of ℂ => a bounded subset meets any closed
  discrete subset in only finitely many points.

The last step is supplied by Mathlib's general
Metric.finite_isBounded_inter_isClosed theorem, not by an
unverified enumeration of spectral values.
-/

noncomputable section

namespace Manuscript14Priority3.LocallyFiniteFredholmZeroSet

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire
open Manuscript14Priority3.UniversalIsolatedSpectralZeros

/-- Set of complex zeros of the ACTUAL infinite-dimensional
CFC Schatten-S₁ universal Fredholm determinant. -/
def universalFredholmZeroSet
    (T : ProbabilisticTheory.TraceClass H) : Set ℂ :=
  {z : ℂ | fredholmDet T z = 0}

/-- The universal determinant zero set is closed, by actual entire
complex analyticity of the universal operatorial determinant. -/
theorem universalFredholmZeroSet_isClosed
    (T : ProbabilisticTheory.TraceClass H) :
    IsClosed (universalFredholmZeroSet T) := by
  unfold universalFredholmZeroSet
  exact isClosed_eq (universal_fredholmDet_entire T).continuous
    continuous_const

/-- Every universal Fredholm spectral zero is isolated; as a set,
the entire collection of zeros is topologically DISCRETE. -/
theorem universalFredholmZeroSet_isDiscrete
    (T : ProbabilisticTheory.TraceClass H) :
    IsDiscrete (universalFredholmZeroSet T) := by
  rw [isDiscrete_iff_nhdsNE]
  intro z _hz
  apply Filter.inf_principal_eq_bot.mpr
  exact universal_fredholmDet_eventually_ne_zero_punctured T z

/-- Local FINITENESS of the universal CFC Schatten-S₁ spectral
zero divisor: on ANY bounded complex region there are only
finitely many zeros, even for arbitrary nonnormal operators. -/
theorem universalFredholmZeroSet_bounded_inter_finite
    (T : ProbabilisticTheory.TraceClass H)
    (K : Set ℂ) (hK : Bornology.IsBounded K) :
    (K ∩ universalFredholmZeroSet T).Finite := by
  exact Metric.finite_isBounded_inter_isClosed
    (universalFredholmZeroSet_isDiscrete T)
    hK (universalFredholmZeroSet_isClosed T)

#print axioms Manuscript14Priority3.LocallyFiniteFredholmZeroSet.universalFredholmZeroSet_isClosed
#print axioms Manuscript14Priority3.LocallyFiniteFredholmZeroSet.universalFredholmZeroSet_isDiscrete
#print axioms Manuscript14Priority3.LocallyFiniteFredholmZeroSet.universalFredholmZeroSet_bounded_inter_finite

end Manuscript14Priority3.LocallyFiniteFredholmZeroSet
