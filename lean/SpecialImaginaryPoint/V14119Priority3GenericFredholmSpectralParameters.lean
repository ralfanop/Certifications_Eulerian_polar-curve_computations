import SpecialImaginaryPoint.V14119Priority3CountableUniversalSpectralZeros
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Priority 3 — generic nonvanishing of the genuine CFC S₁ Fredholm determinant

For every arbitrary (possibly nonnormal) complex trace-class Hilbert operator T,
the spectral parameters z for which the *actual*, universal Hilbert-compression
Fredholm determinant det_F(I+zT) is nonzero form an OPEN DENSE subset of ℂ.

The argument is a precise corollary of the independently certified universal
entireness and closed/discrete/countable spectral zero set. It does not assume
diagonalizability, normality, selfadjointness, positivity, or invertibility.

No new classification or enumeration of zeros is asserted here.
-/

noncomputable section

namespace Manuscript14Priority3.GenericFredholmSpectralParameters

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.LocallyFiniteFredholmZeroSet
open Manuscript14Priority3.CountableUniversalSpectralZeros

/-- Complex shifts at which the genuine universal Fredholm determinant
does not vanish. -/
def universalFredholmNonzeroSet
    (T : ProbabilisticTheory.TraceClass H) : Set ℂ :=
  (universalFredholmZeroSet T)ᶜ

/-- Exact interpretation of the nonvanishing set in terms of the
actual CFC trace-class Fredholm determinant. -/
theorem mem_universalFredholmNonzeroSet_iff
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    z ∈ universalFredholmNonzeroSet T ↔ fredholmDet T z ≠ 0 := by
  simp [universalFredholmNonzeroSet, universalFredholmZeroSet]

/-- Nonvanishing is an OPEN condition in the spectral parameter. -/
theorem universalFredholmNonzeroSet_isOpen
    (T : ProbabilisticTheory.TraceClass H) :
    IsOpen (universalFredholmNonzeroSet T) := by
  exact (universalFredholmZeroSet_isClosed T).isOpen_compl

/-- For every trace-class operator, nonvanishing complex shifts
are DENSE in the entire complex plane. -/
theorem universalFredholmNonzeroSet_dense
    (T : ProbabilisticTheory.TraceClass H) :
    Dense (universalFredholmNonzeroSet T) := by
  exact (universalFredholmZeroSet_countable T).dense_compl ℂ

/-- The complete spectral zero set has empty complex interior. -/
theorem universalFredholmZeroSet_interior_eq_empty
    (T : ProbabilisticTheory.TraceClass H) :
    interior (universalFredholmZeroSet T) = ∅ := by
  exact interior_eq_empty_iff_dense_compl.mpr
    (universalFredholmNonzeroSet_dense T)

#print axioms Manuscript14Priority3.GenericFredholmSpectralParameters.mem_universalFredholmNonzeroSet_iff
#print axioms Manuscript14Priority3.GenericFredholmSpectralParameters.universalFredholmNonzeroSet_isOpen
#print axioms Manuscript14Priority3.GenericFredholmSpectralParameters.universalFredholmNonzeroSet_dense
#print axioms Manuscript14Priority3.GenericFredholmSpectralParameters.universalFredholmZeroSet_interior_eq_empty

end Manuscript14Priority3.GenericFredholmSpectralParameters
