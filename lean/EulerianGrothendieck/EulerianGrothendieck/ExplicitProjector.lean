import EulerianGrothendieck.FrameProjection
import EulerianGrothendieck.PhaseIdentification
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section
namespace EulerianGrothendieck
open scoped ComplexOrder
set_option maxHeartbeats 2000000

/-- The conjugate transpose of the manuscript's 2 by 4 matrix V, parametrized by e=sqrt(p). -/
def frameMatrix (e : ℝ) (z : ℂ) : Matrix (Fin 4) (Fin 2) ℂ :=
  !![1,0; 0,1; (e:ℂ),(Real.sqrt (1-e^2):ℂ);
    (e:ℂ),(Real.sqrt (1-e^2):ℂ)*star z]

theorem frameMatrix_apply (e : ℝ) (z : ℂ) (x : EuclideanSpace ℂ (Fin 2)) :
    (frameMatrix e z).toEuclideanLin x=frameVector e z (x 0) (x 1) := by
  ext i
  fin_cases i <;>
    simp [Matrix.toEuclideanLin_apply,frameMatrix,frameVector,Matrix.mulVec,
      dotProduct,Fin.sum_univ_succ]

theorem frameMatrix_injective (e : ℝ) (z : ℂ) :
    Function.Injective (frameMatrix e z).mulVec := by
  intro x y h
  funext i
  fin_cases i
  · simpa [frameMatrix, Matrix.mulVec, dotProduct,Fin.sum_univ_succ] using congrFun h 0
  · simpa [frameMatrix, Matrix.mulVec, dotProduct,Fin.sum_univ_succ] using congrFun h 1

theorem frameMatrix_gram_invertible (e : ℝ) (z : ℂ) :
    IsUnit ((frameMatrix e z).conjTranspose * frameMatrix e z).det := by
  exact isUnit_iff_ne_zero.mpr (ne_of_gt
    (Matrix.PosDef.conjTranspose_mul_self _ (frameMatrix_injective e z)).det_pos)

theorem frameMatrix_range (e : ℝ) (z : ℂ) :
    LinearMap.range (frameMatrix e z).toEuclideanLin=frameSubspace e z := by
  ext v
  constructor
  · rintro ⟨x,rfl⟩
    rw [frameMatrix_apply]
    exact ⟨(x 0,x 1),rfl⟩
  · rintro ⟨⟨a,b⟩,rfl⟩
    refine ⟨WithLp.toLp 2 ![a,b],?_⟩
    change (frameMatrix e z).toEuclideanLin (WithLp.toLp 2 ![a,b])=frameVector e z a b
    rw [frameMatrix_apply]
    rfl

theorem matrixEuclidean_mul_apply {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq m] [DecidableEq n] [DecidableEq k]
    (A : Matrix m n ℂ) (B : Matrix n k ℂ) (x : EuclideanSpace ℂ k) :
    (A*B).toEuclideanLin x=A.toEuclideanLin (B.toEuclideanLin x) := by
  apply WithLp.ofLp_injective
  simp only [Matrix.ofLp_toEuclideanLin_apply, Matrix.mulVec_mulVec]

/-- The precise matrix formula P=V* (V V*)^{-1} V. -/
def explicitFrameProjector (e : ℝ) (z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  frameMatrix e z * ((frameMatrix e z).conjTranspose * frameMatrix e z)⁻¹ *
    (frameMatrix e z).conjTranspose

theorem explicitFrameProjector_eq_projection (e : ℝ) (z : ℂ) (u : FourSpace) :
    (explicitFrameProjector e z).toEuclideanLin u=(frameSubspace e z).starProjection u := by
  let W := frameMatrix e z
  let G := W.conjTranspose*W
  let x := G⁻¹.toEuclideanLin (W.conjTranspose.toEuclideanLin u)
  have hG : IsUnit G.det := frameMatrix_gram_invertible e z
  have hnormal : W.conjTranspose.toEuclideanLin (W.toEuclideanLin x)=
      W.conjTranspose.toEuclideanLin u := by
    rw [← matrixEuclidean_mul_apply]
    change G.toEuclideanLin (G⁻¹.toEuclideanLin (W.conjTranspose.toEuclideanLin u))=_
    rw [← matrixEuclidean_mul_apply, Matrix.mul_nonsing_inv _ hG]
    simp [Matrix.toEuclideanLin_apply]
  have hmem : W.toEuclideanLin x ∈ frameSubspace e z := by
    rw [← frameMatrix_range]
    exact ⟨x,rfl⟩
  have hproj := (frameSubspace e z).eq_starProjection_of_mem_of_inner_eq_zero hmem
    (u:=u) (by
      intro v hv
      rw [← frameMatrix_range] at hv
      obtain ⟨y,rfl⟩ := hv
      change inner ℂ (u-W.toEuclideanLin x) (W.toEuclideanLin y)=0
      rw [← LinearMap.adjoint_inner_left, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
        map_sub, hnormal, sub_self, inner_zero_left])
  rw [explicitFrameProjector, matrixEuclidean_mul_apply, matrixEuclidean_mul_apply]
  exact hproj.symm

def explicitFrameScalarNorm (e : ℝ) (z : ℂ) : ℝ :=
  sSup {r | ∃ u : FourSpace, IsTorusPoint u ∧
    r=(inner ℂ u ((explicitFrameProjector e z).toEuclideanLin u)).re}

theorem explicitFrameScalarNorm_eq (e : ℝ) (z : ℂ) :
    explicitFrameScalarNorm e z=projectionScalarNorm (frameSubspace e z) := by
  unfold explicitFrameScalarNorm projectionScalarNorm projectionScalarValues
  simp only [explicitFrameProjector_eq_projection, projection_quadratic_value]

theorem explicit_projector_critical_law :
    Filter.Tendsto
      (fun h => (4/explicitFrameScalarNorm (Real.sqrt (criticalVacuum h)) eulerianPhase-1)/Real.sqrt h)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Real.sqrt 6/(Real.pi^2+1))) := by
  simpa only [explicitFrameScalarNorm_eq, frameGrothendieckRatio] using
    eulerian_projection_critical_law

end EulerianGrothendieck
