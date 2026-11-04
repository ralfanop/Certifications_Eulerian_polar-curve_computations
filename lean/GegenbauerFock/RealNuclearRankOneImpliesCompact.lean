import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearClass
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# V007 — arbitrary real nuclear bounded Hilbert operators are compact

This closes the first major outstanding nonpositive real Schatten-S₁
milestone. Rank-one real Hilbert operators factor through the scalar
field, which is locally compact; each is therefore a compact
operator. Absolute nuclear cost summability makes the rank-one
series converge in full operator norm. Compactness then follows
from the closedness of the compact-operator ideal.

No positivity, selfadjointness, normality, injectivity, Hilbert basis,
or CFC singular-value theorem is assumed.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace Filter

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Every real Hilbert rank-one continuous linear endomorphism is
compact, because it factors through the locally compact scalar ℝ. -/
theorem realRankOne_isCompact (u v : H) :
    IsCompactOperator (rankOne ℝ u v : H →L[ℝ] H) := by
  have hf : IsCompactOperator (innerSL ℝ v : H →L[ℝ] ℝ) :=
    isCompactOperator_of_locallyCompactSpace_dom (innerSL ℝ v)
  have hg : Continuous (fun a : ℝ => a • u) :=
    continuous_id.smul continuous_const
  have hcomp := hf.continuous_comp hg
  have hfun :
      (fun x : H => inner ℝ v x • u) =
        (rankOne ℝ u v : H →L[ℝ] H) := by
    funext x
    simp only [InnerProductSpace.rankOne_apply]
  rw [← hfun]
  simpa only [Function.comp_def, innerSL_apply_apply] using hcomp

/-- Arbitrary finite real Hilbert nuclear rank-one sums are compact
operators (not only finite sums with positive coefficients). -/
theorem realFiniteNuclearRankOneSum_isCompact
    (u v : ℕ → H) (beta : ℕ → ℝ) (s : Finset ℕ) :
    IsCompactOperator
      (∑ n ∈ s, beta n • rankOne ℝ (u n) (v n) : H →L[ℝ] H) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (isCompactOperator_zero :
        IsCompactOperator (0 : H →L[ℝ] H))
  | @insert n s hns ih =>
      have hn : IsCompactOperator
          (beta n • rankOne ℝ (u n) (v n) : H →L[ℝ] H) :=
        (realRankOne_isCompact (u n) (v n)).smul (beta n)
      simpa only [Finset.sum_insert hns, ContinuousLinearMap.add_apply]
        using hn.add ih

/-- Every actual real Hilbert 1-nuclear bounded operator is COMPACT:
an operator-norm limit of compact finite-rank approximants. -/
theorem HasRealNuclearRankOneSeries.isCompactOperator
    {T : H →L[ℝ] H}
    (hT : HasRealNuclearRankOneSeries T) :
    IsCompactOperator T := by
  obtain ⟨u, v, beta, hs, hseries⟩ := hT
  have hOp : Summable (fun n : ℕ =>
      beta n • rankOne ℝ (u n) (v n)) := by
    apply Summable.of_norm
    convert hs using 1
    funext n
    rw [norm_smul, norm_rankOne]
    ring
  have hlim : Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N, beta n • rankOne ℝ (u n) (v n))
      atTop (nhds T) := by
    rw [hseries]
    exact hOp.hasSum.tendsto_sum_nat
  exact isCompactOperator_of_tendsto hlim
    (Filter.Eventually.of_forall
      (fun N => realFiniteNuclearRankOneSum_isCompact
        u v beta (Finset.range N)))

#print axioms GegenbauerFock.Ultraspherical.realRankOne_isCompact
#print axioms GegenbauerFock.Ultraspherical.realFiniteNuclearRankOneSum_isCompact
#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.isCompactOperator

end GegenbauerFock.Ultraspherical
