import EulerianGrothendieck.TorusDistance

noncomputable section
namespace EulerianGrothendieck
set_option maxHeartbeats 2000000

def projectionScalarValues (U : Submodule ℂ FourSpace) : Set ℝ :=
  {r | ∃ u : FourSpace, IsTorusPoint u ∧ r=‖U.starProjection u‖^2}
def projectionScalarNorm (U : Submodule ℂ FourSpace) : ℝ := sSup (projectionScalarValues U)
def radialSubspaceInfimum (U : Submodule ℂ FourSpace) : ℝ :=
  sInf (Set.range (fun v : U => radialDistance (v:FourSpace)))

theorem projectionScalarValues_nonempty (U : Submodule ℂ FourSpace) :
    (projectionScalarValues U).Nonempty := by
  let u : FourSpace := WithLp.toLp 2 (fun _ => (1:ℂ))
  exact ⟨_,u,(by intro i; simp [u]),rfl⟩

theorem projectionScalarValues_bddAbove (U : Submodule ℂ FourSpace) :
    BddAbove (projectionScalarValues U) := by
  refine ⟨4, ?_⟩
  rintro r ⟨u,hu,rfl⟩
  have hp := projection_residual_pythagoras U u
  rw [torusPoint_norm_sq u hu] at hp
  nlinarith [sq_nonneg ‖u-U.starProjection u‖]

theorem projectionScalarNorm_ge (U : Submodule ℂ FourSpace) (u : FourSpace)
    (hu : IsTorusPoint u) : ‖U.starProjection u‖^2 ≤ projectionScalarNorm U :=
  le_csSup (projectionScalarValues_bddAbove U) ⟨u,hu,rfl⟩

theorem radialSubspaceInfimum_nonneg (U : Submodule ℂ FourSpace) :
    0 ≤ radialSubspaceInfimum U := by
  apply le_csInf (Set.range_nonempty _)
  rintro d ⟨v,rfl⟩
  exact radialDistance_nonneg v

theorem radialSubspaceInfimum_le (U : Submodule ℂ FourSpace) (v : FourSpace) (hv : v∈U) :
    radialSubspaceInfimum U ≤ radialDistance v := by
  have hb : BddBelow (Set.range (fun v : U => radialDistance (v:FourSpace))) := by
    refine ⟨0, ?_⟩
    rintro d ⟨v,rfl⟩
    exact radialDistance_nonneg v
  exact csInf_le hb ⟨⟨v,hv⟩,rfl⟩

/-- Exact interchange of the two distance infima, proved by inequalities and
coordinatewise nearest phases rather than assuming attainment of either extremum. -/
theorem projection_scalar_distance_identity (U : Submodule ℂ FourSpace) :
    radialSubspaceInfimum U = 4-projectionScalarNorm U := by
  apply le_antisymm
  · have hg : projectionScalarNorm U ≤ 4-radialSubspaceInfimum U := by
      apply csSup_le (projectionScalarValues_nonempty U)
      rintro r ⟨u,hu,rfl⟩
      have h1 := radialSubspaceInfimum_le U (U.starProjection u)
        (U.starProjection_apply_mem u)
      have h2 := radialDistance_le_distance u (U.starProjection u) hu
      have h3 := projection_residual_pythagoras U u
      rw [torusPoint_norm_sq u hu] at h3
      linarith
    linarith
  · apply le_csInf (Set.range_nonempty _)
    rintro d ⟨v,rfl⟩
    obtain ⟨u,hu,hd⟩ := exists_closest_torusPoint (v:FourSpace)
    have h1 := projectionScalarNorm_ge U u hu
    have h2 := projection_residual_minimal U u v v.property
    have h3 := projection_residual_pythagoras U u
    rw [torusPoint_norm_sq u hu] at h3
    rw [hd] at h2
    linarith

theorem projection_quadratic_value (U : Submodule ℂ FourSpace) (u : FourSpace) :
    (inner ℂ u (U.starProjection u)).re = ‖U.starProjection u‖^2 := by
  have h := U.inner_starProjection_left_eq_right u (U.starProjection u)
  have hid : U.starProjection (U.starProjection u)=U.starProjection u :=
    U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem u)
  rw [hid] at h
  rw [← h]
  exact (norm_sq_eq_re_inner (𝕜:=ℂ) (U.starProjection u)).symm

end EulerianGrothendieck
