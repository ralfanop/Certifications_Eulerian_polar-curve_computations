import GegenbauerFock.RealNuclearUnitaryLeftInvariance

/-!
# V007 — two-sided real nuclear trace-norm invariance under unitaries

For any arbitrary real nuclear operator T (not necessarily normal,
selfadjoint, positive, or injective) and real Hilbert unitaries U,V,
the sets of admissible nuclear representation costs are unchanged
under T -> U ∘ T ∘ V. Therefore their projective nuclear infima
are exactly equal.

The right action replaces rankOne u v by rankOne u (V^{-1} v).
This is independent of a positive operator spectral decomposition
and requires no general real CFC/absolute-value class.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Composition on the RIGHT by a Hilbert unitary, as a continuous
real-linear endomorphism of the bounded-operator Banach space. -/
noncomputable def realUnitaryRightCLM (V : H ≃ₗᵢ[ℝ] H) :
    (H →L[ℝ] H) →L[ℝ] (H →L[ℝ] H) :=
  (ContinuousLinearMap.compL ℝ H H H).flip
    V.toLinearIsometry.toContinuousLinearMap

/-- Right multiplication turns the input covector v into V⁻¹v. -/
theorem realUnitaryRightCLM_rankOne
    (V : H ≃ₗᵢ[ℝ] H) (u v : H) :
    realUnitaryRightCLM V (rankOne ℝ u v) =
      rankOne ℝ u (V.symm v) := by
  apply ContinuousLinearMap.ext
  intro x
  have hinner : inner ℝ v (V x) = inner ℝ (V.symm v) x := by
    calc
      inner ℝ v (V x) =
          inner ℝ (V (V.symm v)) (V x) := by rw [V.apply_symm_apply]
      _ = inner ℝ (V.symm v) x := V.inner_map_map _ _
  change (inner ℝ v (V x)) • u = (inner ℝ (V.symm v) x) • u
  rw [hinner]

/-- Right-unitary multiplication maps EVERY rank-one nuclear
representation to another representation of the SAME cost. -/
theorem RealNuclearCosts.unitary_right
    (V : H ≃ₗᵢ[ℝ] H) (T : H →L[ℝ] H) {c : ℝ}
    (hc : c ∈ RealNuclearCosts T) :
    c ∈ RealNuclearCosts (realUnitaryRightCLM V T) := by
  obtain ⟨u, v, beta, hs, hT, rfl⟩ := hc
  have hterm (n : ℕ) :
      ‖beta n‖ * ‖u n‖ * ‖V.symm (v n)‖ =
        ‖beta n‖ * ‖u n‖ * ‖v n‖ := by
    rw [V.symm.norm_map]
  have hcost : Summable (fun n : ℕ =>
      ‖beta n‖ * ‖u n‖ * ‖V.symm (v n)‖) :=
    hs.congr (fun n => (hterm n).symm)
  have hOp : Summable (fun n : ℕ =>
      beta n • rankOne ℝ (u n) (v n)) := by
    apply Summable.of_norm
    convert hs using 1
    funext n
    rw [norm_smul, norm_rankOne]
    ring
  have hmap (n : ℕ) :
      realUnitaryRightCLM V (beta n • rankOne ℝ (u n) (v n)) =
        beta n • rankOne ℝ (u n) (V.symm (v n)) := by
    rw [map_smul, realUnitaryRightCLM_rankOne]
  refine ⟨u, (fun n => V.symm (v n)), beta, hcost, ?_, ?_⟩
  · rw [hT]
    calc
      realUnitaryRightCLM V
          (∑' n : ℕ, beta n • rankOne ℝ (u n) (v n)) =
        ∑' n : ℕ,
          realUnitaryRightCLM V
            (beta n • rankOne ℝ (u n) (v n)) :=
        (realUnitaryRightCLM V).map_tsum hOp
      _ = ∑' n : ℕ, beta n • rankOne ℝ (u n) (V.symm (v n)) :=
        tsum_congr hmap
  · exact (tsum_congr hterm).symm

/-- Right compositions by V and V⁻¹ cancel on every bounded operator. -/
theorem realUnitaryRightCLM_symm_comp
    (V : H ≃ₗᵢ[ℝ] H) (T : H →L[ℝ] H) :
    realUnitaryRightCLM V.symm (realUnitaryRightCLM V T) = T := by
  apply ContinuousLinearMap.ext
  intro x
  change T (V (V.symm x)) = T x
  rw [V.apply_symm_apply]

/-- All nuclear projective representation costs are invariant under
right unitary multiplication (including when the cost set is empty). -/
theorem RealNuclearCosts.unitary_right_iff
    (V : H ≃ₗᵢ[ℝ] H) (T : H →L[ℝ] H) (c : ℝ) :
    c ∈ RealNuclearCosts (realUnitaryRightCLM V T) ↔
      c ∈ RealNuclearCosts T := by
  constructor
  · intro hc
    have hback := RealNuclearCosts.unitary_right V.symm
      (realUnitaryRightCLM V T) hc
    rwa [realUnitaryRightCLM_symm_comp] at hback
  · exact RealNuclearCosts.unitary_right V T

/-- Exact nuclear projective trace norm invariance on the right. -/
theorem realNuclearInfimum_unitary_right_eq
    (V : H ≃ₗᵢ[ℝ] H) (T : H →L[ℝ] H) :
    realNuclearInfimum (realUnitaryRightCLM V T) =
      realNuclearInfimum T := by
  unfold realNuclearInfimum
  congr 1
  ext c
  exact RealNuclearCosts.unitary_right_iff V T c

/-- Two-sided sharp unitary invariance for EVERY real nuclear
operator, regardless of selfadjointness, positivity or normality. -/
theorem realNuclearInfimum_unitary_two_sided_eq
    (U V : H ≃ₗᵢ[ℝ] H) (T : H →L[ℝ] H) :
    realNuclearInfimum
      (realUnitaryLeftCLM U (realUnitaryRightCLM V T)) =
    realNuclearInfimum T := by
  rw [realNuclearInfimum_unitary_left_eq,
    realNuclearInfimum_unitary_right_eq]

#print axioms GegenbauerFock.Ultraspherical.realUnitaryRightCLM_rankOne
#print axioms GegenbauerFock.Ultraspherical.RealNuclearCosts.unitary_right
#print axioms GegenbauerFock.Ultraspherical.realUnitaryRightCLM_symm_comp
#print axioms GegenbauerFock.Ultraspherical.RealNuclearCosts.unitary_right_iff
#print axioms GegenbauerFock.Ultraspherical.realNuclearInfimum_unitary_right_eq
#print axioms GegenbauerFock.Ultraspherical.realNuclearInfimum_unitary_two_sided_eq

end GegenbauerFock.Ultraspherical
