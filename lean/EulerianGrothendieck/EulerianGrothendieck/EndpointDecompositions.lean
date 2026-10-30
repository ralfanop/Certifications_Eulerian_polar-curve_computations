import EulerianGrothendieck.ExposedCorrelation

/-! # Task C2, part 2: the endpoints `p = 0` and `p = 1`

At `p = 0` (`e = 0`) put `u_± = (±1, 1, 1, conj z)`; at `p = 1` (`e = 1`) put
`u_± = (1, ±1, 1, 1)`.  Then `K = (u₊u₊^* + u₋u₋^*)/2`, a convex combination of two
unimodular rank-one correlations, the `u_±` lie in `ran P`, and `g(P) = 4`. -/

noncomputable section
open scoped ComplexConjugate ComplexOrder
open Matrix
namespace EulerianGrothendieck
set_option maxHeartbeats 4000000

def endpointVector0 (z : ℂ) (σ : ℂ) : Fin 4 → ℂ := ![σ, 1, 1, star z]
def endpointVector1 (σ : ℂ) : Fin 4 → ℂ := ![1, σ, 1, 1]

/-- A unimodular rank-one correlation `u u^*`. -/
def rankOneCorrelation (u : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ := vecMulVec u (star u)

theorem rankOneCorrelation_mem (u : Fin 4 → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    rankOneCorrelation u ∈ correlationElliptope := by
  refine ⟨posSemidef_vecMulVec_self_star u, fun i => ?_⟩
  simp only [rankOneCorrelation, vecMulVec_apply, Pi.star_apply, Complex.star_def]
  rw [Complex.mul_conj', hu i]; norm_num

theorem frameGram_endpoint_zero (z : ℂ) :
    frameGram 0 z = (1/2 : ℂ) • (rankOneCorrelation (endpointVector0 z 1) +
      rankOneCorrelation (endpointVector0 z (-1))) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frameGram, frameMatrix, rankOneCorrelation, endpointVector0,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem frameGram_endpoint_one (z : ℂ) :
    frameGram 1 z = (1/2 : ℂ) • (rankOneCorrelation (endpointVector1 1) +
      rankOneCorrelation (endpointVector1 (-1))) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frameGram, frameMatrix, rankOneCorrelation, endpointVector1,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem endpointVector0_unimodular (z : ℂ) (hz : ‖z‖ = 1) (σ : ℂ) (hσ : ‖σ‖ = 1) :
    ∀ i, ‖endpointVector0 z σ i‖ = 1 := by
  intro i; fin_cases i <;> simp [endpointVector0, hσ, hz]

theorem endpointVector1_unimodular (σ : ℂ) (hσ : ‖σ‖ = 1) :
    ∀ i, ‖endpointVector1 σ i‖ = 1 := by
  intro i; fin_cases i <;> simp [endpointVector1, hσ]

/-- A torus point in the range of the projection gives the value `4`. -/
theorem projectionScalarNorm_eq_four_of_mem (U : Submodule ℂ FourSpace) (u : FourSpace)
    (hu : IsTorusPoint u) (hmem : u ∈ U) : projectionScalarNorm U = 4 := by
  apply le_antisymm
  · obtain ⟨v, hv, hmax⟩ := projectionScalarNorm_attained U
    rw [hmax]
    have hp := projection_residual_pythagoras U v
    rw [torusPoint_norm_sq v hv] at hp
    nlinarith [sq_nonneg ‖v - U.starProjection v‖]
  · have h := projectionScalarNorm_ge U u hu
    rw [U.starProjection_eq_self_iff.mpr hmem, torusPoint_norm_sq u hu] at h
    exact h

/-- `g(P) = 4` at `p = 0`. -/
theorem explicitFrameScalarNorm_endpoint_zero (z : ℂ) (hz : ‖z‖ = 1) :
    explicitFrameScalarNorm 0 z = 4 := by
  rw [explicitFrameScalarNorm_eq]
  have hmem : frameVector 0 z 1 1 ∈ frameSubspace 0 z := ⟨(1, 1), rfl⟩
  apply projectionScalarNorm_eq_four_of_mem _ _ _ hmem
  intro i; fin_cases i <;> simp [frameVector, hz]

/-- `g(P) = 4` at `p = 1`. -/
theorem explicitFrameScalarNorm_endpoint_one (z : ℂ) :
    explicitFrameScalarNorm 1 z = 4 := by
  rw [explicitFrameScalarNorm_eq]
  have hmem : frameVector 1 z 1 1 ∈ frameSubspace 1 z := ⟨(1, 1), rfl⟩
  apply projectionScalarNorm_eq_four_of_mem _ _ _ hmem
  intro i; fin_cases i <;> simp [frameVector]

/-- The phase vectors of the endpoint decompositions lie in `ran P`. -/
theorem endpoint_vectors_in_range (z : ℂ) (σ : ℂ) :
    (WithLp.toLp 2 (endpointVector0 z σ) : FourSpace) ∈ frameSubspace 0 z ∧
    (WithLp.toLp 2 (endpointVector1 σ) : FourSpace) ∈ frameSubspace 1 z := by
  constructor
  · refine ⟨(σ, 1), ?_⟩
    change frameVector 0 z σ 1 = _
    ext i; fin_cases i <;> simp [frameVector, endpointVector0]
  · refine ⟨(1, σ), ?_⟩
    change frameVector 1 z 1 σ = _
    ext i; fin_cases i <;> simp [frameVector, endpointVector1]

end EulerianGrothendieck
