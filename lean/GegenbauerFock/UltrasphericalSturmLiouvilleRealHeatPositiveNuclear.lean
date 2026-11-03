import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatTraceBasisSummable
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealPositiveNuclear
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# V007 — genuine positive-time heat nuclear series and compactness

For every lambda,s>0 the ACTUAL full weighted-real-L² Gegenbauer heat
operator equals an operator-norm absolutely convergent positive rank-one
series with weights exp(-s n(n+2lambda)).

The proof uses a complete kernel-certified Hilbert basis, the genuine heat
eigenmode identity, rank-one orthogonality and uniqueness on the dense
linear span of the modes. Summability controls the operator-norm series.
Consequently the genuine heat operator is compact for EVERY s>0, not
only its compact resolvent or an auxiliary coefficient multiplier.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory InnerProductSpace Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The explicit heat-weighted rank-one operator series is absolutely
summable in genuine real weighted-L² operator norm. -/
theorem sturmRealHeat_positive_nuclear_operator_summable
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    Summable (fun n : ℕ =>
      Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) •
        rankOne ℝ
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)) := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let beta : ℕ → ℝ := fun n =>
    Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))
  have hsum : Summable beta :=
    sturmRealHeat_spectral_multiplier_summable lam s hlam hs
  have hn (n : ℕ) :
      ‖beta n • rankOne ℝ
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖ =
        beta n := by
    rw [norm_smul, norm_rankOne,
      sturmMonicEigenCandidate_realL2_normalized_norm lam hlam n]
    simp only [one_mul, mul_one, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  apply Summable.of_norm
  convert hsum using 1
  funext n
  exact hn n

/-- The genuine full real-L² heat operator coincides with its
operator-norm summable, nonnegative rank-one spectral series. -/
theorem sturmRealHeat_positive_nuclear_operator_tsum_eq
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    sturmRealHeatLimitCLM lam hlam s (le_of_lt hs) =
      ∑' n : ℕ,
        Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) •
          rankOne ℝ
            (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
            (sturmMonicEigenCandidate_realL2_normalized lam hlam n) := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let beta : ℕ → ℝ := fun n =>
    Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))
  let T : SturmH lam →L[ℝ] SturmH lam :=
    sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)
  let F : ℕ → SturmH lam →L[ℝ] SturmH lam := fun n =>
    beta n • rankOne ℝ (b n) (b n)
  let S : SturmH lam →L[ℝ] SturmH lam := ∑' n : ℕ, F n
  have hb (n : ℕ) :
      b n = sturmMonicEigenCandidate_realL2_normalized lam hlam n := by
    simp only [b, sturmMonicEigenCandidate_realL2_hilbertBasis,
      HilbertBasis.coe_mkOfOrthogonalEqBot]
  have hseries : Summable F := by
    simpa only [F, beta, hb] using
      sturmRealHeat_positive_nuclear_operator_summable lam s hlam hs
  have hTb (k : ℕ) : T (b k) = beta k • b k := by
    rw [hb k]
    exact sturmRealHeatLimitCLM_normalized_Gegenbauer_eigen
      lam hlam s (le_of_lt hs) k
  have hSb (k : ℕ) : S (b k) = beta k • b k := by
    have hsingle :
        HasSum (fun n : ℕ => if n = k then beta k • b k else 0)
          (beta k • b k) :=
      hasSum_ite_eq k (beta k • b k)
    have happly :
        HasSum (fun n : ℕ => F n (b k)) (S (b k)) := by
      have h :=
        hseries.hasSum.mapL
          ((ContinuousLinearMap.apply ℝ (SturmH lam)) (b k))
      simpa only [S, ContinuousLinearMap.apply_apply] using h
    have hterms :
        (fun n : ℕ => F n (b k)) =
          (fun n : ℕ => if n = k then beta k • b k else 0) := by
      funext n
      by_cases hnk : n = k
      · subst n
        have hinner : inner ℝ (b k) (b k) = 1 := by
          rw [real_inner_self_eq_norm_sq,
            b.orthonormal.norm_eq_one k]
          norm_num
        change beta k • (inner ℝ (b k) (b k) • b k) =
          if k = k then beta k • b k else 0
        rw [if_pos rfl, hinner, one_smul]
      · have horth : inner ℝ (b n) (b k) = 0 :=
          b.orthonormal.inner_eq_zero hnk
        change beta n • (inner ℝ (b n) (b k) • b n) =
          if n = k then beta k • b k else 0
        rw [if_neg hnk, horth, zero_smul, smul_zero]
    rw [hterms] at happly
    exact happly.unique hsingle
  have hdense : Dense
      ((Submodule.span ℝ (Set.range b)) : Set (SturmH lam)) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    exact b.dense_span
  have hEq : T = S := by
    apply ContinuousLinearMap.ext_on hdense
    rintro _ ⟨k, rfl⟩
    exact (hTb k).trans (hSb k).symm
  change T = _
  simpa only [S, F, beta, hb] using hEq

/-- The actual strictly positive-time Gegenbauer heat operator is
compact on the entire true real weighted L² space. -/
theorem sturmRealHeat_positive_time_isCompactOperator
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    IsCompactOperator (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let beta : ℕ → ℝ := fun n =>
    Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))
  let F : ℕ → SturmH lam →L[ℝ] SturmH lam := fun n =>
    beta n • rankOne ℝ (b n) (b n)
  let S : SturmH lam →L[ℝ] SturmH lam := ∑' n : ℕ, F n
  have hb (n : ℕ) :
      b n = sturmMonicEigenCandidate_realL2_normalized lam hlam n := by
    simp only [b, sturmMonicEigenCandidate_realL2_hilbertBasis,
      HilbertBasis.coe_mkOfOrthogonalEqBot]
  have hseries : Summable F := by
    simpa only [F, beta, hb] using
      sturmRealHeat_positive_nuclear_operator_summable lam s hlam hs
  have hterm (n : ℕ) : IsCompactOperator (F n) := by
    change IsCompactOperator
      (beta n • rankOne ℝ (b n) (b n))
    rw [hb n]
    exact (sturmRealGegenbauerRankOne_compact lam hlam n).smul (beta n)
  have hfinite (u : Finset ℕ) :
      IsCompactOperator
        (∑ n ∈ u, F n : SturmH lam →L[ℝ] SturmH lam) := by
    induction u using Finset.induction_on with
    | empty =>
        simpa using (isCompactOperator_zero :
          IsCompactOperator (0 : SturmH lam → SturmH lam))
    | @insert n u hn ih =>
        simpa [Finset.sum_insert hn] using (hterm n).add ih
  have hlim : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, F n)
      atTop (𝓝 S) := hseries.hasSum.tendsto_sum_nat
  have hcompactS : IsCompactOperator S :=
    isCompactOperator_of_tendsto hlim
      (Eventually.of_forall (fun N => hfinite (Finset.range N)))
  have hEq : sturmRealHeatLimitCLM lam hlam s (le_of_lt hs) = S := by
    simpa only [S, F, beta, hb] using
      sturmRealHeat_positive_nuclear_operator_tsum_eq lam s hlam hs
  rw [hEq]
  exact hcompactS

/-- Positive real nuclear expansion of the true heat operator. -/
theorem sturmRealHeat_has_positive_real_nuclear_expansion
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    HasRealPositiveNuclearExpansion
      (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) := by
  let e : ℕ → SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam
  let beta : ℕ → ℝ := fun n =>
    Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))
  refine ⟨e, beta, ?_, ?_, ?_, ?_⟩
  · exact sturmMonicEigenCandidate_realL2_normalized_orthonormal lam hlam
  · intro n
    exact (Real.exp_pos _).le
  · exact sturmRealHeat_spectral_multiplier_summable lam s hlam hs
  · exact sturmRealHeat_positive_nuclear_operator_tsum_eq lam s hlam hs

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_positive_nuclear_operator_summable
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_positive_nuclear_operator_tsum_eq
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_positive_time_isCompactOperator
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_has_positive_real_nuclear_expansion

end GegenbauerFock.Ultraspherical
