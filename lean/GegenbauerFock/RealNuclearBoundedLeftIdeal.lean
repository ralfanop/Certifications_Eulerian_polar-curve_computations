import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearDualLower

/-!
# V007 — left bounded-operator ideal property of real nuclear rank-one series

For arbitrary bounded real Hilbert operators S and nuclear T,
the left product S ∘ T is nuclear. Moreover every admissible
nuclear representation cost c for T yields an explicit cost c'
for S ∘ T satisfying c' ≤ ‖S‖ c.

No positivity, selfadjointness, spectral basis, injectivity, or
unitary multiplier is assumed. This is a genuine ideal property
of the real rank-one nuclear class, beyond unitary invariance.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Left multiplication by a bounded real Hilbert operator is a
continuous real-linear operator on the bounded-operator Banach space. -/
noncomputable def realNuclearBoundedLeftCLM (S : H →L[ℝ] H) :
    (H →L[ℝ] H) →L[ℝ] (H →L[ℝ] H) :=
  ContinuousLinearMap.compL ℝ H H H S

/-- Bounded left multiplication sends rank-one (u,v) to (Su,v). -/
theorem realNuclearBoundedLeftCLM_rankOne
    (S : H →L[ℝ] H) (u v : H) :
    realNuclearBoundedLeftCLM S (rankOne ℝ u v) =
      rankOne ℝ (S u) v := by
  apply ContinuousLinearMap.ext
  intro x
  change S ((inner ℝ v x) • u) = (inner ℝ v x) • S u
  exact map_smul S _ _

/-- Every admissible real nuclear cost c for T produces a cost for
S ∘ T no greater than ‖S‖ c. Unlike equality under a unitary, this
inequality holds for an arbitrary bounded multiplier S. -/
theorem RealNuclearCosts.bounded_left
    (S T : H →L[ℝ] H) {cost : ℝ}
    (hcost : cost ∈ RealNuclearCosts T) :
    ∃ newCost : ℝ,
      newCost ∈ RealNuclearCosts (realNuclearBoundedLeftCLM S T) ∧
      newCost ≤ ‖S‖ * cost := by
  rcases hcost with ⟨u, v, beta, hs, hT, rfl⟩
  let original : ℕ → ℝ :=
    fun n => ‖beta n‖ * ‖u n‖ * ‖v n‖
  let newCostTerm : ℕ → ℝ :=
    fun n => ‖beta n‖ * ‖S (u n)‖ * ‖v n‖
  have hpoint (n : ℕ) :
      newCostTerm n ≤ ‖S‖ * original n := by
    have hS : ‖S (u n)‖ ≤ ‖S‖ * ‖u n‖ :=
      ContinuousLinearMap.le_opNorm S (u n)
    have hnn : 0 ≤ ‖beta n‖ * ‖v n‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc
      newCostTerm n =
          ‖S (u n)‖ * (‖beta n‖ * ‖v n‖) := by
            dsimp [newCostTerm]
            ring
      _ ≤ (‖S‖ * ‖u n‖) * (‖beta n‖ * ‖v n‖) :=
        mul_le_mul_of_nonneg_right hS hnn
      _ = ‖S‖ * original n := by
        dsimp [original]
        ring
  have hright : Summable (fun n : ℕ => ‖S‖ * original n) := by
    exact hs.mul_left ‖S‖
  have hnew : Summable newCostTerm := by
    apply Summable.of_nonneg_of_le
    · intro n
      dsimp [newCostTerm]
      positivity
    · exact hpoint
    · exact hright
  have hoperators : Summable (fun n : ℕ =>
      beta n • rankOne ℝ (u n) (v n)) := by
    apply Summable.of_norm
    convert hs using 1
    funext n
    rw [norm_smul, norm_rankOne]
    ring
  have hmap (n : ℕ) :
      realNuclearBoundedLeftCLM S
        (beta n • rankOne ℝ (u n) (v n)) =
      beta n • rankOne ℝ (S (u n)) (v n) := by
    rw [map_smul, realNuclearBoundedLeftCLM_rankOne]
  have hseries :
      realNuclearBoundedLeftCLM S T =
      ∑' n : ℕ, beta n • rankOne ℝ (S (u n)) (v n) := by
    rw [hT]
    calc
      realNuclearBoundedLeftCLM S
          (∑' n : ℕ, beta n • rankOne ℝ (u n) (v n)) =
        ∑' n : ℕ,
          realNuclearBoundedLeftCLM S
            (beta n • rankOne ℝ (u n) (v n)) :=
        (realNuclearBoundedLeftCLM S).map_tsum hoperators
      _ = ∑' n : ℕ, beta n • rankOne ℝ (S (u n)) (v n) :=
        tsum_congr hmap
  refine ⟨∑' n : ℕ, newCostTerm n, ?_, ?_⟩
  · refine ⟨(fun n => S (u n)), v, beta, hnew, hseries, ?_⟩
    rfl
  · have hbound := hnew.tsum_le_tsum hpoint hright
    rw [tsum_mul_left] at hbound
    exact hbound

/-- Arbitrary left bounded-operator composition preserves real
rank-one nuclearity, with no normality or unitary assumption. -/
theorem HasRealNuclearRankOneSeries.bounded_left
    (S T : H →L[ℝ] H)
    (hT : HasRealNuclearRankOneSeries T) :
    HasRealNuclearRankOneSeries (realNuclearBoundedLeftCLM S T) := by
  rcases hT with ⟨u, v, beta, hs, hsum⟩
  have hc : (∑' n : ℕ,
      ‖beta n‖ * ‖u n‖ * ‖v n‖) ∈ RealNuclearCosts T :=
    ⟨u, v, beta, hs, hsum, rfl⟩
  obtain ⟨c, hc', _⟩ :=
    RealNuclearCosts.bounded_left S T hc
  rcases hc' with ⟨u', v', beta', hs', hsum', _⟩
  exact ⟨u', v', beta', hs', hsum'⟩

#print axioms GegenbauerFock.Ultraspherical.realNuclearBoundedLeftCLM_rankOne
#print axioms GegenbauerFock.Ultraspherical.RealNuclearCosts.bounded_left
#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.bounded_left

end GegenbauerFock.Ultraspherical
