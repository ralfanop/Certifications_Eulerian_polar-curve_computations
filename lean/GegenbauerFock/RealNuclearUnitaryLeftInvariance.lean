import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealS1EigenbasisToNuclear

/-!
# V007 — real nuclear projective S₁ norm invariant under left unitary

Unlike the preceding spectral theorem, this applies to EVERY real-Hilbert
nuclear operator, including nonselfadjoint or nonnormal operators.

For a real linear isometric equivalence U, rankOne u v is mapped to
rankOne (U u) v, with no change in nuclear representation cost.
Both U and U⁻¹ are used to establish equality of all admissible
cost sets, hence equality of their infima.

This does NOT introduce an independent CFC singular-value trace norm.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Left composition with a real Hilbert unitary as a continuous
linear map on bounded operators, so it preserves operator-norm
convergent absolutely summable series. -/
noncomputable def realUnitaryLeftCLM
    (U : H ≃ₗᵢ[ℝ] H) :
    (H →L[ℝ] H) →L[ℝ] (H →L[ℝ] H) :=
  ContinuousLinearMap.compL ℝ H H H U.toLinearIsometry.toContinuousLinearMap

/-- Real left-unitary composition preserves the rank-one tensor form. -/
theorem realUnitaryLeftCLM_rankOne
    (U : H ≃ₗᵢ[ℝ] H) (u v : H) :
    realUnitaryLeftCLM U (rankOne ℝ u v) =
      rankOne ℝ (U u) v := by
  apply ContinuousLinearMap.ext
  intro x
  change U (rankOne ℝ u v x) = rankOne ℝ (U u) v x
  simp only [InnerProductSpace.rankOne_apply, map_smul]

/-- Composing a nuclear series on the left by a unitary preserves
the full projective representation cost, with no multiplicative loss. -/
theorem RealNuclearCosts.unitary_left
    (U : H ≃ₗᵢ[ℝ] H) (T : H →L[ℝ] H) {c : ℝ}
    (hc : c ∈ RealNuclearCosts T) :
    c ∈ RealNuclearCosts (realUnitaryLeftCLM U T) := by
  rcases hc with ⟨u, v, β, hs, hT, rfl⟩
  have hterm (n : ℕ) :
      ‖β n‖ * ‖U (u n)‖ * ‖v n‖ =
        ‖β n‖ * ‖u n‖ * ‖v n‖ := by
    rw [U.norm_map]
  have hcost : Summable (fun n : ℕ =>
      ‖β n‖ * ‖U (u n)‖ * ‖v n‖) :=
    hs.congr (fun n => (hterm n).symm)
  have hOp : Summable (fun n : ℕ =>
      β n • rankOne ℝ (u n) (v n)) := by
    apply Summable.of_norm
    convert hs using 1
    funext n
    rw [norm_smul, norm_rankOne]
    ring
  have hmap (n : ℕ) :
      realUnitaryLeftCLM U (β n • rankOne ℝ (u n) (v n)) =
        β n • rankOne ℝ (U (u n)) (v n) := by
    rw [map_smul, realUnitaryLeftCLM_rankOne]
  refine ⟨(fun n => U (u n)), v, β, hcost, ?_, ?_⟩
  · rw [hT]
    calc
      realUnitaryLeftCLM U
          (∑' n : ℕ, β n • rankOne ℝ (u n) (v n)) =
        ∑' n : ℕ,
          realUnitaryLeftCLM U
            (β n • rankOne ℝ (u n) (v n)) :=
        (realUnitaryLeftCLM U).map_tsum hOp
      _ = ∑' n : ℕ, β n • rankOne ℝ (U (u n)) (v n) :=
        tsum_congr hmap
  · exact (tsum_congr hterm).symm

/-- Opposite left-unitaries cancel as maps on bounded real operators. -/
theorem realUnitaryLeftCLM_symm_comp
    (U : H ≃ₗᵢ[ℝ] H) (T : H →L[ℝ] H) :
    realUnitaryLeftCLM U.symm (realUnitaryLeftCLM U T) = T := by
  apply ContinuousLinearMap.ext
  intro x
  change U.symm (U (T x)) = T x
  exact U.symm_apply_apply (T x)

/-- The set of costs of ALL real nuclear rank-one representations
is exactly invariant under left multiplication by a real unitary. -/
theorem RealNuclearCosts.unitary_left_iff
    (U : H ≃ₗᵢ[ℝ] H) (T : H →L[ℝ] H) (c : ℝ) :
    c ∈ RealNuclearCosts (realUnitaryLeftCLM U T) ↔
      c ∈ RealNuclearCosts T := by
  constructor
  · intro hc
    have hback :=
      RealNuclearCosts.unitary_left U.symm
        (realUnitaryLeftCLM U T) hc
    rwa [realUnitaryLeftCLM_symm_comp] at hback
  · exact RealNuclearCosts.unitary_left U T

/-- EXACT invariance of real projective nuclear trace norm
under arbitrary real-Hilbert unitary left multiplication.
No positivity or normality assumption on T is needed. -/
theorem realNuclearInfimum_unitary_left_eq
    (U : H ≃ₗᵢ[ℝ] H) (T : H →L[ℝ] H) :
    realNuclearInfimum (realUnitaryLeftCLM U T) =
      realNuclearInfimum T := by
  unfold realNuclearInfimum
  congr 1
  ext c
  exact RealNuclearCosts.unitary_left_iff U T c

#print axioms GegenbauerFock.Ultraspherical.realUnitaryLeftCLM_rankOne
#print axioms GegenbauerFock.Ultraspherical.RealNuclearCosts.unitary_left
#print axioms GegenbauerFock.Ultraspherical.realUnitaryLeftCLM_symm_comp
#print axioms GegenbauerFock.Ultraspherical.RealNuclearCosts.unitary_left_iff
#print axioms GegenbauerFock.Ultraspherical.realNuclearInfimum_unitary_left_eq

end GegenbauerFock.Ultraspherical
