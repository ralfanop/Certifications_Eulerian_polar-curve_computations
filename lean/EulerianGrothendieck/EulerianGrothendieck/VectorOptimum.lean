import EulerianGrothendieck.BilinearScalarBridge

/-! # Task C1, part 2: the bilinear vector optimum and the Grothendieck witness

`bilinearVectorNorm P` is the manuscript's
`q_ℂ(P) = sup |Tr(B^* P A)|` over all numbers of columns `n` and all `4 × n` complex
matrices `A, B` whose rows have Euclidean norm at most one.

Main results:
* `bilinearVectorNorm_explicit`: `q_ℂ(P) = 4` for `0 ≤ p ≤ 1`, `|z| = 1`
  (upper bound by the projection/Frobenius estimate, attained at `A = B = V^*`,
  which in the code is the 4×2 matrix `frameMatrix e z`);
* `bilinearRatio_explicit`: `q_ℂ(P)/g_ℂ(P) = 4/g(P)`;
* `bilinearRatio_le_of_grothendieck`: the ratio is at most every constant `K` satisfying the
  finite complex Grothendieck inequality, defined independently of the ratio;
* `bilinear_ratio_critical_law`: the certified critical law, now for the bilinear ratio. -/

noncomputable section
open scoped ComplexConjugate
namespace EulerianGrothendieck
set_option maxHeartbeats 2000000

/-- Every row has Euclidean norm at most one. -/
def RowNormalized {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  ∀ i, ∑ k, ‖A i k‖ ^ 2 ≤ 1

def bilinearVectorValues {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) : Set ℝ :=
  {r | ∃ (n : ℕ) (A B : Matrix (Fin m) (Fin n) ℂ), RowNormalized A ∧ RowNormalized B ∧
    r = ‖(B.conjTranspose * P * A).trace‖}

/-- `q_ℂ(P) = sup_{n, A, B row-normalised} |Tr(B^* P A)|`. -/
def bilinearVectorNorm {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) : ℝ := sSup (bilinearVectorValues P)

/-- The `k`-th column of a `4 × n` matrix as a vector of `ℂ^4`. -/
def matrixColumn {n : ℕ} (A : Matrix (Fin 4) (Fin n) ℂ) (k : Fin n) : FourSpace :=
  WithLp.toLp 2 (fun i => A i k)

theorem trace_eq_sum_inner {n : ℕ} (P : Matrix (Fin 4) (Fin 4) ℂ) (A B : Matrix (Fin 4) (Fin n) ℂ) :
    (B.conjTranspose * P * A).trace =
      ∑ k, inner ℂ (matrixColumn B k) (P.toEuclideanLin (matrixColumn A k)) := by
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro k _
  rw [PiLp.inner_apply]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, matrixColumn,
    Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, PiLp.toLp_apply, RCLike.inner_apply,
    Matrix.mulVec, dotProduct, Complex.star_def, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

theorem norm_starProjection_le' (U : Submodule ℂ FourSpace) (u : FourSpace) :
    ‖U.starProjection u‖ ≤ ‖u‖ := by
  have h := projection_residual_pythagoras U u
  have h2 : ‖U.starProjection u‖ ^ 2 ≤ ‖u‖ ^ 2 := by nlinarith [sq_nonneg ‖u - U.starProjection u‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp h2

theorem matrixColumn_norm_sq_sum {n : ℕ} (A : Matrix (Fin 4) (Fin n) ℂ) :
    ∑ k, ‖matrixColumn A k‖ ^ 2 = ∑ i, ∑ k, ‖A i k‖ ^ 2 := by
  simp only [matrixColumn, EuclideanSpace.norm_sq_eq, PiLp.toLp_apply]
  rw [Finset.sum_comm]

theorem rowNormalized_sum_le {n : ℕ} {A : Matrix (Fin 4) (Fin n) ℂ} (hA : RowNormalized A) :
    ∑ i, ∑ k, ‖A i k‖ ^ 2 ≤ 4 := by
  calc ∑ i, ∑ k, ‖A i k‖ ^ 2 ≤ ∑ _i : Fin 4, (1:ℝ) := Finset.sum_le_sum (fun i _ => hA i)
    _ = 4 := by simp

/-- `|Tr(B^* P A)| ≤ 4` for row-normalised `A, B`, since `P` is an orthogonal projection. -/
theorem explicit_vector_value_le (e : ℝ) (z : ℂ) {n : ℕ} (A B : Matrix (Fin 4) (Fin n) ℂ)
    (hA : RowNormalized A) (hB : RowNormalized B) :
    ‖(B.conjTranspose * explicitFrameProjector e z * A).trace‖ ≤ 4 := by
  set U := frameSubspace e z
  rw [trace_eq_sum_inner]
  simp_rw [explicitFrameProjector_eq_projection]
  have hterm : ∀ k, ‖inner ℂ (matrixColumn B k) (U.starProjection (matrixColumn A k))‖ ≤
      (‖matrixColumn A k‖ ^ 2 + ‖matrixColumn B k‖ ^ 2) / 2 := by
    intro k
    set a := matrixColumn A k
    set b := matrixColumn B k
    have hid : U.starProjection a = U.starProjection (U.starProjection a) :=
      (U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem a)).symm
    rw [hid, ← U.inner_starProjection_left_eq_right]
    have h1 := norm_starProjection_le' U a
    have h2 := norm_starProjection_le' U b
    calc ‖inner ℂ (U.starProjection b) (U.starProjection a)‖
        ≤ ‖U.starProjection b‖ * ‖U.starProjection a‖ := norm_inner_le_norm _ _
      _ ≤ ‖b‖ * ‖a‖ := mul_le_mul h2 h1 (norm_nonneg _) (norm_nonneg _)
      _ ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  calc ‖∑ k, inner ℂ (matrixColumn B k) (U.starProjection (matrixColumn A k))‖
      ≤ ∑ k, ‖inner ℂ (matrixColumn B k) (U.starProjection (matrixColumn A k))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k, (‖matrixColumn A k‖ ^ 2 + ‖matrixColumn B k‖ ^ 2) / 2 :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = ((∑ k, ‖matrixColumn A k‖ ^ 2) + ∑ k, ‖matrixColumn B k‖ ^ 2) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ (4 + 4) / 2 := by
        rw [matrixColumn_norm_sq_sum, matrixColumn_norm_sq_sum]
        linarith [rowNormalized_sum_le hA, rowNormalized_sum_le hB]
    _ = 4 := by norm_num

/-- `P V^* = V^*` for `P = V^*(VV^*)^{-1}V`; in the code `V^*` is `frameMatrix e z`. -/
theorem explicitFrameProjector_mul_frameMatrix (e : ℝ) (z : ℂ) :
    explicitFrameProjector e z * frameMatrix e z = frameMatrix e z := by
  unfold explicitFrameProjector
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (frameMatrix_gram_invertible e z),
    Matrix.mul_one]

theorem frameMatrix_row_norm_sq (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) (hz : ‖z‖ = 1) (i : Fin 4) :
    ∑ k, ‖frameMatrix e z i k‖ ^ 2 = 1 := by
  have hs : Real.sqrt (1 - e ^ 2) ^ 2 = 1 - e ^ 2 := Real.sq_sqrt (by linarith)
  fin_cases i <;>
    simp [frameMatrix, Fin.sum_univ_succ, Complex.norm_real, Real.norm_eq_abs, sq_abs, hs, hz,
      norm_mul, mul_pow]

theorem frameMatrix_rowNormalized (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) (hz : ‖z‖ = 1) :
    RowNormalized (frameMatrix e z) :=
  fun i => (frameMatrix_row_norm_sq e z he hz i).le

/-- `Tr(V P V^*) = Tr K = 4`. -/
theorem frameMatrix_trace_value (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) (hz : ‖z‖ = 1) :
    ((frameMatrix e z).conjTranspose * explicitFrameProjector e z * frameMatrix e z).trace = 4 := by
  rw [Matrix.mul_assoc, explicitFrameProjector_mul_frameMatrix]
  have h : ((frameMatrix e z).conjTranspose * frameMatrix e z).trace =
      ∑ i, ∑ k, ((‖frameMatrix e z i k‖ ^ 2 : ℝ) : ℂ) := by
    unfold Matrix.trace
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [Complex.conj_mul']
    norm_cast
  rw [h]
  simp_rw [← Complex.ofReal_sum]
  rw [Finset.sum_congr rfl (fun i _ => frameMatrix_row_norm_sq e z he hz i)]
  norm_num

/-- **`q_ℂ(P) = 4`**. -/
theorem bilinearVectorNorm_explicit (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) (hz : ‖z‖ = 1) :
    bilinearVectorNorm (explicitFrameProjector e z) = 4 := by
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨2, frameMatrix e z, frameMatrix e z, frameMatrix_rowNormalized e z he hz,
      frameMatrix_rowNormalized e z he hz, ?_⟩
    rw [frameMatrix_trace_value e z he hz]; norm_num
  · rintro r ⟨n, A, B, hA, hB, rfl⟩
    exact explicit_vector_value_le e z A B hA hB

/-- A crude lower bound `g(P) ≥ 1`, from the range vector `(1,0,e,e)`. -/
theorem one_le_explicitFrameScalarNorm (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) :
    1 ≤ explicitFrameScalarNorm e z := by
  rw [explicitFrameScalarNorm_eq]
  have hid := projection_scalar_distance_identity (frameSubspace e z)
  have hmem : frameVector e z 1 0 ∈ frameSubspace e z := ⟨(1, 0), rfl⟩
  have hle := radialSubspaceInfimum_le (frameSubspace e z) _ hmem
  have hval : radialDistance (frameVector e z 1 0) = 1 + 2 * (|e| - 1) ^ 2 := by
    rw [radialDistance_frameVector]
    simp only [frameDistance, mul_one, mul_zero, add_zero, norm_one, norm_zero, Complex.norm_real,
      Real.norm_eq_abs]
    ring
  have habs : |e| ≤ 1 := by
    have : |e| ^ 2 ≤ 1 := by rw [sq_abs]; exact he
    nlinarith [abs_nonneg e]
  have hsq : (|e| - 1) ^ 2 ≤ 1 := by nlinarith [abs_nonneg e]
  rw [hval] at hle
  linarith

theorem explicitFrameScalarNorm_pos (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) :
    0 < explicitFrameScalarNorm e z :=
  lt_of_lt_of_le one_pos (one_le_explicitFrameScalarNorm e z he)

/-- The optimal ratio `𝒬 = q_ℂ(P)/g_ℂ(P)` for the specified coefficient matrix. -/
def bilinearRatio (e : ℝ) (z : ℂ) : ℝ :=
  bilinearVectorNorm (explicitFrameProjector e z) / bilinearScalarNorm (explicitFrameProjector e z)

/-- **`q_ℂ(P)/g_ℂ(P) = 4/g(P)`**. -/
theorem bilinearRatio_explicit (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) (hz : ‖z‖ = 1) :
    bilinearRatio e z = 4 / explicitFrameScalarNorm e z := by
  rw [bilinearRatio, bilinearVectorNorm_explicit e z he hz, bilinearScalarNorm_explicit]

/-- At the Eulerian phase the bilinear ratio is the certified `frameGrothendieckRatio`. -/
theorem bilinearRatio_eulerian (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bilinearRatio (Real.sqrt p) eulerianPhase = frameGrothendieckRatio p := by
  have he : Real.sqrt p ^ 2 ≤ 1 := by rw [Real.sq_sqrt hp0]; exact hp1
  rw [bilinearRatio_explicit _ _ he eulerianPhase_unit, explicitFrameScalarNorm_eq,
    frameGrothendieckRatio]

theorem criticalVacuum_mem (h : ℝ) (hh : 0 < h) : 0 ≤ criticalVacuum h ∧ criticalVacuum h ≤ 1 := by
  unfold criticalVacuum
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  have : 0 ≤ 1 / (144 * ((1/12 : ℝ) + h) ^ 2) := by positivity
  calc Real.sqrt (1 - 1 / (144 * ((1/12 : ℝ) + h) ^ 2)) ≤ Real.sqrt 1 :=
        Real.sqrt_le_sqrt (by linarith)
    _ = 1 := Real.sqrt_one

/-- The certified critical law, for the bilinear ratio `q_ℂ(P)/g_ℂ(P)` itself. -/
theorem bilinear_ratio_critical_law :
    Filter.Tendsto
      (fun h => (bilinearRatio (Real.sqrt (criticalVacuum h)) eulerianPhase - 1) / Real.sqrt h)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Real.sqrt 6 / (Real.pi ^ 2 + 1))) := by
  apply eulerian_projection_critical_law.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hm := criticalVacuum_mem h hh
  rw [bilinearRatio_eulerian _ hm.1 hm.2]

/-- The finite complex Grothendieck inequality with constant `K`, for matrices of every size.
This is an independent definition: it does not mention the matrix `P` or its ratio. -/
def SatisfiesComplexGrothendieck (K : ℝ) : Prop :=
  ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), bilinearVectorNorm A ≤ K * bilinearScalarNorm A

/-- `K_G^ℂ`, the infimum of the admissible constants.  (Grothendieck's theorem, i.e. that
admissible constants exist, is classical and is not formalised here.) -/
def complexGrothendieckConstant : ℝ := sInf {K | SatisfiesComplexGrothendieck K}

/-- `𝒬(p) ≤ K` for every admissible Grothendieck constant `K`. -/
theorem bilinearRatio_le_of_grothendieck (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1) (hz : ‖z‖ = 1)
    {K : ℝ} (hK : SatisfiesComplexGrothendieck K) : bilinearRatio e z ≤ K := by
  have h := hK 4 (explicitFrameProjector e z)
  have hg := explicitFrameScalarNorm_pos e z he
  rw [bilinearVectorNorm_explicit e z he hz, bilinearScalarNorm_explicit] at h
  rw [bilinearRatio_explicit e z he hz, div_le_iff₀ hg]
  linarith

/-- `𝒬(p) ≤ K_G^ℂ`, under the (classical, unformalised) existence of an admissible constant. -/
theorem bilinearRatio_le_complexGrothendieckConstant (e : ℝ) (z : ℂ) (he : e ^ 2 ≤ 1)
    (hz : ‖z‖ = 1) (hex : ∃ K, SatisfiesComplexGrothendieck K) :
    bilinearRatio e z ≤ complexGrothendieckConstant := by
  apply le_csInf hex
  intro K hK
  exact bilinearRatio_le_of_grothendieck e z he hz hK

end EulerianGrothendieck
