import EulerianGrothendieck.ProjectionScalarNorm
import EulerianGrothendieck.VariationalCriticalLaw

noncomputable section
namespace EulerianGrothendieck
set_option maxHeartbeats 2000000

def frameVector (e : ℝ) (z a b : ℂ) : FourSpace :=
  WithLp.toLp 2 ![a,b,(e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*b,
    (e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*star z*b]

def frameLinear (e : ℝ) (z : ℂ) : (ℂ × ℂ) →ₗ[ℂ] FourSpace where
  toFun ab := frameVector e z ab.1 ab.2
  map_add' ab cd := by
    ext i
    fin_cases i <;> simp [frameVector] <;> ring
  map_smul' c ab := by
    ext i
    fin_cases i <;> simp [frameVector] <;> ring

def frameSubspace (e : ℝ) (z : ℂ) : Submodule ℂ FourSpace := LinearMap.range (frameLinear e z)

theorem radialDistance_frameVector (e : ℝ) (z a b : ℂ) :
    radialDistance (frameVector e z a b)=frameDistance e z a b := by
  simp [radialDistance, frameVector, Fin.sum_univ_succ, frameDistance]
  <;> ring

theorem frame_radial_infimum (e : ℝ) (z : ℂ) :
    radialSubspaceInfimum (frameSubspace e z)=frameInfimum e z := by
  unfold radialSubspaceInfimum frameInfimum
  congr 1
  ext d
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨⟨a,b⟩,heq⟩ := v.property
    refine ⟨(a,b),?_⟩
    change frameVector e z a b=(v:FourSpace) at heq
    change frameDistance e z a b=d
    change radialDistance (v:FourSpace)=d at hv
    rw [← hv, ← heq, radialDistance_frameVector]
  · rintro ⟨⟨a,b⟩,hd⟩
    have hv : frameVector e z a b ∈ frameSubspace e z := ⟨(a,b),rfl⟩
    refine ⟨⟨frameVector e z a b,hv⟩,?_⟩
    change radialDistance (frameVector e z a b)=d
    rw [radialDistance_frameVector]
    exact hd

/-- Exact projection-distance bridge for the range of the manuscript's four-vector map. -/
theorem frame_projection_distance_identity (e : ℝ) (z : ℂ) :
    frameInfimum e z=4-projectionScalarNorm (frameSubspace e z) := by
  rw [← frame_radial_infimum, projection_scalar_distance_identity]

def frameGrothendieckRatio (p : ℝ) : ℝ :=
  4/projectionScalarNorm (frameSubspace (Real.sqrt p) eulerianPhase)

theorem frameGrothendieckRatio_eq_variational (p : ℝ) :
    frameGrothendieckRatio p=eulerianVariationalRatio p := by
  unfold frameGrothendieckRatio eulerianVariationalRatio eulerianLoss
  rw [frame_projection_distance_identity]
  ring

theorem eulerian_projection_loss_ratio_limit :
    Filter.Tendsto (fun p => (4-projectionScalarNorm (frameSubspace (Real.sqrt p) eulerianPhase))/p)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (2/(Real.pi^2+1))) := by
  simpa only [eulerianLoss, frame_projection_distance_identity] using eulerian_loss_ratio_limit

/-- Critical law for the actual scalar optimum of the orthogonal projector onto
range(V*), not just a selected phase or an assumed variational approximation. -/
theorem eulerian_projection_critical_law :
    Filter.Tendsto (fun h => (frameGrothendieckRatio (criticalVacuum h)-1)/Real.sqrt h)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Real.sqrt 6/(Real.pi^2+1))) := by
  simpa only [frameGrothendieckRatio_eq_variational] using eulerian_variational_critical_law

end EulerianGrothendieck
