import GegenbauerFock.RealNuclearTwoOrthonormalAllCostsDual

/-!
# V007 — exact real S1 nuclear norm from two incomplete singular families

For arbitrary REAL Hilbert space H and an ACTUAL bounded T, suppose
T has an absolutely operator-norm convergent singular rank-one series
  T = sum sigma_n rankOne(c_n,b_n)
with nonnegative summable sigma and orthonormal source/output families
b,c, NEITHER of which needs to be complete.

Then T is nuclear and its optimal projective cost over ALL real
rank-one representations is exactly sum sigma_n. This includes compact
weighted unilateral shifts and their adjoints, regardless of distinct
kernel/cokernel defect dimensions. No global unitary or equality of
defects is assumed.

This does not prove the existence of such a decomposition for EVERY
nuclear operator; that is a separate compact spectral/partial-isometry
construction.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace Filter

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Evaluate an arbitrary absolutely summable real singular rank-one
series at one source singular vector without completeness assumptions. -/
theorem realTwoOrthonormalSingularSeries_basis_apply
    (b c : ℕ → H) (hb : Orthonormal ℝ b)
    (hc : Orthonormal ℝ c)
    (sigma : ℕ → ℝ) (hs : Summable (fun n => ‖sigma n‖))
    (k : ℕ) :
    (∑' n : ℕ, sigma n • rankOne ℝ (c n) (b n)) (b k) =
      sigma k • c k := by
  have hOp : Summable (fun n : ℕ =>
      sigma n • rankOne ℝ (c n) (b n)) := by
    apply Summable.of_norm
    convert hs using 1
    funext n
    rw [norm_smul, norm_rankOne,
      hb.norm_eq_one n, hc.norm_eq_one n]
    ring
  have hsingle :
      HasSum (fun n : ℕ => if n = k then sigma k • c k else 0)
        (sigma k • c k) :=
    hasSum_ite_eq k (sigma k • c k)
  have happly :
      HasSum
        (fun n : ℕ =>
          (sigma n • rankOne ℝ (c n) (b n)) (b k))
        ((∑' n : ℕ, sigma n • rankOne ℝ (c n) (b n)) (b k)) := by
    have h := hOp.hasSum.mapL
      ((ContinuousLinearMap.apply ℝ H) (b k))
    simpa only [ContinuousLinearMap.apply_apply] using h
  have hterms :
      (fun n : ℕ => (sigma n • rankOne ℝ (c n) (b n)) (b k)) =
        (fun n : ℕ => if n = k then sigma k • c k else 0) := by
    funext n
    by_cases hnk : n = k
    · subst n
      have hinner : inner ℝ (b k) (b k) = 1 := by
        rw [real_inner_self_eq_norm_sq, hb.norm_eq_one k]
        norm_num
      change sigma k • (inner ℝ (b k) (b k) • c k) =
        if k = k then sigma k • c k else 0
      rw [if_pos rfl, hinner, one_smul]
    · have horth : inner ℝ (b n) (b k) = 0 :=
        hb.inner_eq_zero hnk
      change sigma n • (inner ℝ (b n) (b k) • c n) =
        if n = k then sigma k • c k else 0
      rw [if_neg hnk, horth, zero_smul, smul_zero]
  rw [hterms] at happly
  exact happly.unique hsingle

/-- The exact nuclear projective trace norm for an ACTUAL real
operator admitting any summable two-orthonormal-family singular series,
including operators with unequal kernel/cokernel defect dimensions. -/
theorem realTwoPartialSingularFamilies_nuclear_exact_trace
    (T : H →L[ℝ] H) (b c : ℕ → H)
    (hb : Orthonormal ℝ b) (hc : Orthonormal ℝ c)
    (sigma : ℕ → ℝ) (hpos : ∀ n, 0 ≤ sigma n)
    (hs : Summable sigma)
    (hseries : T = ∑' n : ℕ,
      sigma n • rankOne ℝ (c n) (b n)) :
    HasRealNuclearRankOneSeries T ∧
      realNuclearInfimum T = ∑' n : ℕ, sigma n := by
  have hterm (n : ℕ) :
      ‖sigma n‖ * ‖c n‖ * ‖b n‖ = sigma n := by
    rw [hc.norm_eq_one n, hb.norm_eq_one n,
      Real.norm_eq_abs, abs_of_nonneg (hpos n)]
    ring
  have hcost :
      Summable (fun n : ℕ =>
        ‖sigma n‖ * ‖c n‖ * ‖b n‖) :=
    hs.congr (fun n => (hterm n).symm)
  have hclass : HasRealNuclearRankOneSeries T :=
    ⟨c, b, sigma, hcost, hseries⟩
  have hmem : (∑' n : ℕ, sigma n) ∈ RealNuclearCosts T := by
    refine ⟨c, b, sigma, hcost, hseries, ?_⟩
    exact (tsum_congr hterm).symm
  have hupper : realNuclearInfimum T ≤ ∑' n : ℕ, sigma n :=
    realNuclearInfimum_le_cost T hmem
  have hnorm : Summable (fun n : ℕ => ‖sigma n‖) :=
    hs.congr (fun n => ((Real.norm_eq_abs (sigma n)).trans
      (abs_of_nonneg (hpos n))).symm)
  have hdiag (n : ℕ) :
      inner ℝ (c n) (T (b n)) = sigma n := by
    rw [hseries,
      realTwoOrthonormalSingularSeries_basis_apply b c hb hc sigma hnorm n,
      real_inner_smul_right,
      real_inner_self_eq_norm_sq, hc.norm_eq_one n]
    ring
  have hlower (cost : ℝ) (hcst : cost ∈ RealNuclearCosts T) :
      (∑' n : ℕ, sigma n) ≤ cost := by
    have hfinite (N : ℕ) :
        (∑ n ∈ Finset.range N, sigma n) ≤ cost := by
      have hh := realTwoOrthonormalFiniteTrace_abs_le_nuclearCost
        b c hb hc N T hcst
      have hsum :
          (∑ n ∈ Finset.range N, inner ℝ (c n) (T (b n))) =
            ∑ n ∈ Finset.range N, sigma n :=
        Finset.sum_congr rfl (fun n _ => hdiag n)
      rw [hsum] at hh
      have hp : 0 ≤ ∑ n ∈ Finset.range N, sigma n :=
        Finset.sum_nonneg (fun n _ => hpos n)
      simpa only [abs_of_nonneg hp] using hh
    exact le_of_tendsto hs.hasSum.tendsto_sum_nat
      (Filter.Eventually.of_forall hfinite)
  have heq :
      realNuclearInfimum T = ∑' n : ℕ, sigma n :=
    le_antisymm hupper
      (le_csInf ⟨∑' n : ℕ, sigma n, hmem⟩ hlower)
  exact ⟨hclass, heq⟩

#print axioms GegenbauerFock.Ultraspherical.realTwoOrthonormalSingularSeries_basis_apply
#print axioms GegenbauerFock.Ultraspherical.realTwoPartialSingularFamilies_nuclear_exact_trace

end GegenbauerFock.Ultraspherical
