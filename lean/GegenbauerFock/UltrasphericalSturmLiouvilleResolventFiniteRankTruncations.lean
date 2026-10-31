import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertResolventCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventMultiplierDecay
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# V007 — genuine finite-rank Gegenbauer Sturm resolvent truncations

Construct the finite spectral truncations from the EXPLICIT normalized
Gegenbauer Hilbert basis in the genuine real ultraspherical weighted L².

Each term is a scalar multiple of a rank-one continuous operator.
It factors through the locally compact scalar field and is compact.
Finite sums are compact without assuming compactness of the full
resolvent. The separate operator-norm convergence step remains to
be proved, using diagonal coordinates and vanishing multipliers.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Rank-one truncation of the actual closed Sturm resolvent to its
first N normalized all-degree Gegenbauer eigenmodes. -/
noncomputable def sturmRealResolventFiniteRankTruncation
    (lam t : ℝ) (hlam : 0 < lam) (N : ℕ) :
    SturmH lam →L[ℝ] SturmH lam :=
  ∑ n ∈ Finset.range N,
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
      rankOne ℝ
        (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
        (sturmMonicEigenCandidate_realL2_normalized lam hlam n)

/-- Each explicit normalized Gegenbauer rank-one projector is compact
because it factors through the real scalar field. -/
theorem sturmRealGegenbauerRankOne_compact
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    IsCompactOperator
      (rankOne ℝ
        (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
        (sturmMonicEigenCandidate_realL2_normalized lam hlam n)) := by
  let e : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam n
  have hspan :
      IsCompactOperator
        (ContinuousLinearMap.toSpanSingleton ℝ e : ℝ →L[ℝ] SturmH lam) :=
    isCompactOperator_of_locallyCompactSpace_rng _
  have hcomp := hspan.comp_clm (innerSL ℝ e)
  simpa only [rankOne_def', e] using hcomp

/-- Every genuine finite spectral truncation is a compact bounded
operator on the actual ultraspherical real L², independently of any
hypothesis about the infinite-dimensional resolvent. -/
theorem sturmRealResolventFiniteRankTruncation_compact
    (lam t : ℝ) (hlam : 0 < lam) (N : ℕ) :
    IsCompactOperator (sturmRealResolventFiniteRankTruncation lam t hlam N) := by
  have hterm (n : ℕ) :
      IsCompactOperator
        ((t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
          (rankOne ℝ
            (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
            (sturmMonicEigenCandidate_realL2_normalized lam hlam n))) :=
    (sturmRealGegenbauerRankOne_compact lam hlam n).smul _
  have hsum (s : Finset ℕ) :
      IsCompactOperator
        (∑ n ∈ s,
          (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
            (rankOne ℝ
              (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
              (sturmMonicEigenCandidate_realL2_normalized lam hlam n)) :
                SturmH lam →L[ℝ] SturmH lam) := by
    classical
    induction s using Finset.induction_on with
    | empty =>
        simpa using (isCompactOperator_zero :
          IsCompactOperator (0 : SturmH lam → SturmH lam))
    | @insert n s hn ih =>
        simpa [Finset.sum_insert hn] using (hterm n).add ih
  simpa only [sturmRealResolventFiniteRankTruncation] using
    hsum (Finset.range N)

#print axioms GegenbauerFock.Ultraspherical.sturmRealGegenbauerRankOne_compact
#print axioms GegenbauerFock.Ultraspherical.sturmRealResolventFiniteRankTruncation_compact

end GegenbauerFock.Ultraspherical
