import EulerianGrothendieck.PhaseCoordinates
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section
namespace EulerianGrothendieck
set_option maxHeartbeats 2000000

abbrev FourSpace := EuclideanSpace ℂ (Fin 4)
def IsTorusPoint (u : FourSpace) : Prop := ∀ i, ‖u i‖=1
def radialDistance (v : FourSpace) : ℝ := ∑ i, (‖v i‖-1)^2

theorem exists_unit_closest (z : ℂ) :
    ∃ u : ℂ, ‖u‖=1 ∧ ‖u-z‖^2=(‖z‖-1)^2 := by
  obtain ⟨u,hu,hz⟩ := Complex.exists_norm_mul_eq_self z
  refine ⟨u,hu,?_⟩
  have he : u-z = u*((1-‖z‖:ℝ):ℂ) := by
    calc
      _ = u-u*(‖z‖:ℂ) := congrArg (fun x : ℂ => u-x) hz.symm
      _ = _ := by push_cast; ring
  rw [he, norm_mul, hu, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem torusPoint_norm_sq (u : FourSpace) (hu : IsTorusPoint u) : ‖u‖^2=4 := by
  rw [EuclideanSpace.norm_sq_eq]
  change ∀ i, ‖u i‖=1 at hu
  simp [hu]

theorem radialDistance_nonneg (v : FourSpace) : 0 ≤ radialDistance v := by
  unfold radialDistance
  positivity

theorem radialDistance_le_distance (u v : FourSpace) (hu : IsTorusPoint u) :
    radialDistance v ≤ ‖u-v‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro i hi
  have h := abs_norm_sub_norm_le (u i) (v i)
  rw [hu i] at h
  have hn := norm_nonneg (u i-v i)
  have ha := abs_nonneg (1-‖v i‖)
  have hs := sq_abs (1-‖v i‖)
  change (‖v i‖-1)^2 ≤ ‖u i-v i‖^2
  nlinarith

theorem exists_closest_torusPoint (v : FourSpace) :
    ∃ u : FourSpace, IsTorusPoint u ∧ ‖u-v‖^2=radialDistance v := by
  choose u hu he using (fun i : Fin 4 => exists_unit_closest (v i))
  refine ⟨WithLp.toLp 2 u, hu, ?_⟩
  rw [EuclideanSpace.norm_sq_eq]
  unfold radialDistance
  apply Finset.sum_congr rfl
  intro i hi
  exact he i

theorem projection_residual_pythagoras (U : Submodule ℂ FourSpace) (u : FourSpace) :
    ‖u-U.starProjection u‖^2+‖U.starProjection u‖^2=‖u‖^2 := by
  have h := U.orthogonalProjectionFn_norm_sq u
  simpa only [Submodule.starProjection_apply, pow_two] using h.symm

theorem projection_residual_minimal (U : Submodule ℂ FourSpace) (u v : FourSpace)
    (hv : v ∈ U) : ‖u-U.starProjection u‖^2 ≤ ‖u-v‖^2 := by
  have h := U.starProjection_minimal u
  have hb : BddBelow (Set.range (fun x : U => ‖u-(x:FourSpace)‖)) :=
    ⟨0, by rintro _ ⟨x,rfl⟩; positivity⟩
  have hl : ‖u-U.starProjection u‖ ≤ ‖u-v‖ := by
    rw [h]
    exact csInf_le hb (Set.mem_range.mpr ⟨⟨v,hv⟩,rfl⟩)
  exact pow_le_pow_left₀ (norm_nonneg _) hl 2

end EulerianGrothendieck
