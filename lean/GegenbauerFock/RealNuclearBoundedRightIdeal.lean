import GegenbauerFock.RealNuclearBoundedLeftIdeal
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# V007 — two-sided bounded-operator ideal estimate for real nuclear S₁

An arbitrary bounded real Hilbert operator S acts on the RIGHT of any
nuclear T and preserves the existence of absolutely summable real
rank-one representations. Every admissible nuclear cost c of T
produces a cost no greater than ‖S‖c for T ∘ S, by passing
the covectors through the genuine Hilbert adjoint S†.

Combining this with the separately kernel-certified bounded LEFT
ideal yields the sharp two-sided cost estimate with coefficient one:
  c' ≤ ‖A‖ ‖B‖ c for A ∘ T ∘ B.

No positivity, selfadjointness, normality, or unitary phase is used.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace
open scoped InnerProduct

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Right composition by an arbitrary bounded real Hilbert map,
as a bounded linear map on the real operator Banach space. -/
noncomputable def realNuclearBoundedRightCLM (S : H →L[ℝ] H) :
    (H →L[ℝ] H) →L[ℝ] (H →L[ℝ] H) :=
  (ContinuousLinearMap.compL ℝ H H H).flip S

/-- Right composition of rank one (u,v) sends its input covector
v to the real Hilbert adjoint S†v, without assuming S unitary. -/
theorem realNuclearBoundedRightCLM_rankOne
    (S : H →L[ℝ] H) (u v : H) :
    realNuclearBoundedRightCLM S (rankOne ℝ u v) =
      rankOne ℝ u ((ContinuousLinearMap.adjoint S) v) := by
  apply ContinuousLinearMap.ext
  intro x
  change (inner ℝ v (S x)) • u =
    (inner ℝ ((ContinuousLinearMap.adjoint S) v) x) • u
  rw [ContinuousLinearMap.adjoint_inner_left S x v]

/-- Every admissible real nuclear representation of T transfers
under right multiplication by an arbitrary bounded S, with cost
bounded by the operator norm of S times the original cost. -/
theorem RealNuclearCosts.bounded_right
    (S T : H →L[ℝ] H) {cost : ℝ}
    (hcost : cost ∈ RealNuclearCosts T) :
    ∃ newCost : ℝ,
      newCost ∈ RealNuclearCosts (realNuclearBoundedRightCLM S T) ∧
      newCost ≤ ‖S‖ * cost := by
  rcases hcost with ⟨u, v, beta, hs, hT, rfl⟩
  let u' : ℕ → H := u
  let v' : ℕ → H := fun n => (ContinuousLinearMap.adjoint S) (v n)
  let original : ℕ → ℝ :=
    fun n => ‖beta n‖ * ‖u n‖ * ‖v n‖
  let newCostTerm : ℕ → ℝ :=
    fun n => ‖beta n‖ * ‖u' n‖ * ‖v' n‖
  have hnormAdj :
      ‖ContinuousLinearMap.adjoint S‖ = ‖S‖ :=
    ContinuousLinearMap.adjoint.norm_map S
  have hpoint (n : ℕ) :
      newCostTerm n ≤ ‖S‖ * original n := by
    have hS : ‖v' n‖ ≤ ‖S‖ * ‖v n‖ := by
      calc
        ‖v' n‖ ≤ ‖ContinuousLinearMap.adjoint S‖ * ‖v n‖ :=
          ContinuousLinearMap.le_opNorm
            (ContinuousLinearMap.adjoint S) (v n)
        _ = ‖S‖ * ‖v n‖ := by rw [hnormAdj]
    have hnn : 0 ≤ ‖beta n‖ * ‖u n‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc
      newCostTerm n =
        (‖beta n‖ * ‖u n‖) * ‖v' n‖ := by
          rfl
      _ ≤ (‖beta n‖ * ‖u n‖) * (‖S‖ * ‖v n‖) :=
        mul_le_mul_of_nonneg_left hS hnn
      _ = ‖S‖ * original n := by
        dsimp [original]
        ring
  have hright : Summable (fun n : ℕ => ‖S‖ * original n) :=
    hs.mul_left ‖S‖
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
      realNuclearBoundedRightCLM S
        (beta n • rankOne ℝ (u n) (v n)) =
      beta n • rankOne ℝ (u n) (v' n) := by
    rw [map_smul, realNuclearBoundedRightCLM_rankOne]
  have hseries :
      realNuclearBoundedRightCLM S T =
      ∑' n : ℕ, beta n • rankOne ℝ (u n) (v' n) := by
    rw [hT]
    calc
      realNuclearBoundedRightCLM S
          (∑' n : ℕ, beta n • rankOne ℝ (u n) (v n)) =
        ∑' n : ℕ,
          realNuclearBoundedRightCLM S
            (beta n • rankOne ℝ (u n) (v n)) :=
        (realNuclearBoundedRightCLM S).map_tsum hoperators
      _ = ∑' n : ℕ, beta n • rankOne ℝ (u n) (v' n) :=
        tsum_congr hmap
  refine ⟨∑' n : ℕ, newCostTerm n, ?_, ?_⟩
  · refine ⟨u, v', beta, hnew, hseries, ?_⟩
    rfl
  · have hbound := hnew.tsum_le_tsum hpoint hright
    rw [tsum_mul_left] at hbound
    exact hbound

/-- Nuclearity is preserved under arbitrary right composition. -/
theorem HasRealNuclearRankOneSeries.bounded_right
    (S T : H →L[ℝ] H)
    (hT : HasRealNuclearRankOneSeries T) :
    HasRealNuclearRankOneSeries (realNuclearBoundedRightCLM S T) := by
  rcases hT with ⟨u, v, beta, hs, hsum⟩
  have hc : (∑' n : ℕ,
      ‖beta n‖ * ‖u n‖ * ‖v n‖) ∈ RealNuclearCosts T :=
    ⟨u, v, beta, hs, hsum, rfl⟩
  obtain ⟨c, hc', _⟩ := RealNuclearCosts.bounded_right S T hc
  rcases hc' with ⟨u', v', beta', hs', hsum', _⟩
  exact ⟨u', v', beta', hs', hsum'⟩

/-- SHARP two-sided bounded real nuclear ideal cost estimate.
For arbitrary A,B,T (not necessarily normal or selfadjoint),
every nuclear cost c of T yields a cost of A ∘ T ∘ B
no greater than ‖A‖ ‖B‖ c. -/
theorem RealNuclearCosts.bounded_two_sided
    (A B T : H →L[ℝ] H) {cost : ℝ}
    (hcost : cost ∈ RealNuclearCosts T) :
    ∃ newCost : ℝ,
      newCost ∈ RealNuclearCosts
        (realNuclearBoundedLeftCLM A
          (realNuclearBoundedRightCLM B T)) ∧
      newCost ≤ (‖A‖ * ‖B‖) * cost := by
  obtain ⟨c1, hc1, h1⟩ :=
    RealNuclearCosts.bounded_right B T hcost
  obtain ⟨c2, hc2, h2⟩ :=
    RealNuclearCosts.bounded_left A
      (realNuclearBoundedRightCLM B T) hc1
  refine ⟨c2, hc2, ?_⟩
  calc
    c2 ≤ ‖A‖ * c1 := h2
    _ ≤ ‖A‖ * (‖B‖ * cost) :=
      mul_le_mul_of_nonneg_left h1 (norm_nonneg A)
    _ = (‖A‖ * ‖B‖) * cost := by ring

/-- Nuclearity is an algebraic two-sided ideal property under
compositions with arbitrary bounded real Hilbert operators. -/
theorem HasRealNuclearRankOneSeries.bounded_two_sided
    (A B T : H →L[ℝ] H)
    (hT : HasRealNuclearRankOneSeries T) :
    HasRealNuclearRankOneSeries
      (realNuclearBoundedLeftCLM A (realNuclearBoundedRightCLM B T)) :=
  (hT.bounded_right B T).bounded_left A (realNuclearBoundedRightCLM B T)

#print axioms GegenbauerFock.Ultraspherical.realNuclearBoundedRightCLM_rankOne
#print axioms GegenbauerFock.Ultraspherical.RealNuclearCosts.bounded_right
#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.bounded_right
#print axioms GegenbauerFock.Ultraspherical.RealNuclearCosts.bounded_two_sided
#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.bounded_two_sided

end GegenbauerFock.Ultraspherical
