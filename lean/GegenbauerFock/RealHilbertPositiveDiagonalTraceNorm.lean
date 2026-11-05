import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearDualLower

/-!
# V007 — universal positive diagonal real-Hilbert S1 nuclear norm theorem

Let H be an arbitrary real Hilbert space with a complete countable
orthonormal basis b. If a bounded operator T has a positive summable
diagonal rank-one expansion with the stated diagonal coefficients, the
infimum of the costs of ALL real nuclear representations of T is exactly
the sum of these coefficients.

The operator is not required to be the Sturm resolvent or a Gram
operator. This proves an abstract real projective nuclear trace-norm
identity; identification with an independently defined complex CFC
trace class is not asserted.

No sorry, new axioms, or toolchain change.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace Filter

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The real projective nuclear infimum of any positive diagonal
operator, in an arbitrary complete countably based real Hilbert space,
equals the sum of its positive summable diagonal coefficients. -/
theorem realHilbert_positiveDiagonal_nuclearInfimum_eq_trace
    (b : HilbertBasis ℕ ℝ H) (T : H →L[ℝ] H)
    (β : ℕ → ℝ) (hs : Summable β)
    (hβ : ∀ n, 0 ≤ β n)
    (hT : T = ∑' n : ℕ, β n • rankOne ℝ (b n) (b n))
    (hdiag : ∀ n, inner ℝ (b n) (T (b n)) = β n) :
    realNuclearInfimum T = ∑' n : ℕ, β n := by
  have hcost_term (n : ℕ) :
      ‖β n‖ * ‖b n‖ * ‖b n‖ = β n := by
    rw [b.orthonormal.norm_eq_one n,
      Real.norm_eq_abs, abs_of_nonneg (hβ n)]
    ring
  have hcost :
      Summable (fun n : ℕ => ‖β n‖ * ‖b n‖ * ‖b n‖) :=
    hs.congr (fun n => (hcost_term n).symm)
  have hcost_eq :
      (∑' n : ℕ, ‖β n‖ * ‖b n‖ * ‖b n‖) =
        ∑' n : ℕ, β n :=
    tsum_congr hcost_term
  have hmem :
      (∑' n : ℕ, ‖β n‖ * ‖b n‖ * ‖b n‖) ∈
        RealNuclearCosts T := by
    exact ⟨b, b, β, hcost, hT, rfl⟩
  apply le_antisymm
  · calc
      realNuclearInfimum T ≤
          ∑' n : ℕ, ‖β n‖ * ‖b n‖ * ‖b n‖ :=
        realNuclearInfimum_le_cost T hmem
      _ = ∑' n : ℕ, β n := hcost_eq
  · unfold realNuclearInfimum
    apply le_csInf ⟨_, hmem⟩
    intro c hc
    have hfinite (N : ℕ) :
        (∑ n ∈ Finset.range N, β n) ≤ c := by
      have hbound :=
        realHilbertFiniteTrace_abs_le_nuclearCost b N T hc
      have hsum :
          (∑ n ∈ Finset.range N,
            inner ℝ (b n) (T (b n))) =
            ∑ n ∈ Finset.range N, β n := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hdiag n
      rw [hsum] at hbound
      have hp : 0 ≤ ∑ n ∈ Finset.range N, β n := by
        apply Finset.sum_nonneg
        intro n hn
        exact hβ n
      simpa only [abs_of_nonneg hp] using hbound
    exact le_of_tendsto hs.hasSum.tendsto_sum_nat
      (Filter.Eventually.of_forall hfinite)

#print axioms GegenbauerFock.Ultraspherical.realHilbert_positiveDiagonal_nuclearInfimum_eq_trace

end GegenbauerFock.Ultraspherical
