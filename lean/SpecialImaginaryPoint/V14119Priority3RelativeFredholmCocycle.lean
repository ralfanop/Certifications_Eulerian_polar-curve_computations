import SpecialImaginaryPoint.V14119Priority3RelativeUniversalFredholmScalar

/-!
# Priority 3 — exact relative Fredholm scalar cocycle

For any complex CFC Schatten-S₁ trace-class Hilbert operators
T,S,U (nonnormal operators included), use the ACTUAL universal
Hilbert-compression-limit Fredholm determinants to define
 R_(T,S)(z) = det_F(I+zT)/det_F(I+zS).

On the genuine common nonvanishing spectral domains this ratio is
reflexive and obeys the cocycle and reciprocal identities:
 R_(T,T)(z)=1,
 R_(T,S)(z) R_(S,U)(z)=R_(T,U)(z),
 R_(T,S)(z) R_(S,T)(z)=1.

These are exact identities of infinite-dimensional operatorial
SCALAR Fredholm ratios, NOT an identification with zeta-regularized
relative determinants or with operator-resolvent determinants.
-/

noncomputable section

namespace Manuscript14Priority3.RelativeFredholmCocycle

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.RelativeUniversalFredholmScalar

/-- The true universal relative scalar Fredholm determinant of
any trace-class operator against itself is one on its nonzero domain. -/
theorem universalFredholmRelativeScalar_refl
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : fredholmDet T z ≠ 0) :
    universalFredholmRelativeScalar T T z = 1 := by
  simp only [universalFredholmRelativeScalar]
  exact div_self hz

/-- True infinite-dimensional relative Fredholm determinant scalar
cocycle for arbitrary CFC Schatten-S₁ operators T,S,U. The actual
denominators associated with S and U must not vanish. -/
theorem universalFredholmRelativeScalar_cocycle
    (T S U : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hS : fredholmDet S z ≠ 0) (hU : fredholmDet U z ≠ 0) :
    universalFredholmRelativeScalar T S z *
      universalFredholmRelativeScalar S U z =
        universalFredholmRelativeScalar T U z := by
  simp only [universalFredholmRelativeScalar]
  field_simp [hS, hU] <;> ring

/-- Oppositely oriented genuine Fredholm scalar determinant
ratios multiply to one wherever both real operatorial determinants
are nonzero. -/
theorem universalFredholmRelativeScalar_reciprocal
    (T S : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hT : fredholmDet T z ≠ 0) (hS : fredholmDet S z ≠ 0) :
    universalFredholmRelativeScalar T S z *
      universalFredholmRelativeScalar S T z = 1 := by
  simp only [universalFredholmRelativeScalar]
  field_simp [hT, hS] <;> ring

#print axioms Manuscript14Priority3.RelativeFredholmCocycle.universalFredholmRelativeScalar_refl
#print axioms Manuscript14Priority3.RelativeFredholmCocycle.universalFredholmRelativeScalar_cocycle
#print axioms Manuscript14Priority3.RelativeFredholmCocycle.universalFredholmRelativeScalar_reciprocal

end Manuscript14Priority3.RelativeFredholmCocycle
