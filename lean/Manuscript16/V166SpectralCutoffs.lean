import Manuscript16.V166L2SpectralInverse

noncomputable section
open scoped ENNReal
namespace Manuscript16.V166SpectralCutoffs
open Manuscript16.V166L2SpectralInverse

variable {ι : Type*}

/-- Coordinate analysis into an actual n-dimensional normed space. -/
def analysisMap {n : ℕ} (e : Fin n ↪ ι) : L2 ι →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi (fun j => lp.evalCLM ℂ (fun _ : ι => ℂ) 2 (e j))

/-- Weighted synthesis from that finite-dimensional space. -/
def synthesisMap {n : ℕ} (d : ι → ℂ) (e : Fin n ↪ ι) :
    (Fin n → ℂ) →L[ℂ] L2 ι := by
  classical
  exact ∑ j : Fin n, d (e j) •
    ((lp.singleContinuousLinearMap ℂ (fun _ : ι => ℂ) 2 (e j)).comp
      (ContinuousLinearMap.proj j))

def cutoff {n : ℕ} (d : ι → ℂ) (e : Fin n ↪ ι) : L2 ι →L[ℂ] L2 ι :=
  (synthesisMap d e).comp (analysisMap e)

theorem cutoff_factor {n : ℕ} (d : ι → ℂ) (e : Fin n ↪ ι) :
    ∃ (F : L2 ι →L[ℂ] (Fin n → ℂ)) (G : (Fin n → ℂ) →L[ℂ] L2 ι),
      cutoff d e = G.comp F :=
  ⟨analysisMap e, synthesisMap d e, rfl⟩

theorem cutoff_apply_sum {n : ℕ} (d : ι → ℂ) (e : Fin n ↪ ι)
    (x : L2 ι) (i : ι) :
    cutoff d e x i = ∑ j : Fin n, d (e j) * lp.single 2 (e j) (x (e j)) i := by
  classical
  unfold cutoff synthesisMap
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, lp.coeFn_sum, Finset.sum_apply,
    lp.singleContinuousLinearMap_apply]
  rfl

theorem cutoff_apply_mem {n : ℕ} (d : ι → ℂ) (e : Fin n ↪ ι)
    (x : L2 ι) (j : Fin n) :
    cutoff d e x (e j) = d (e j) * x (e j) := by
  classical
  rw [cutoff_apply_sum, Finset.sum_eq_single j]
  · rw [lp.single_apply_self]
  · intro k _ hk
    rw [lp.single_apply_ne _ _ _ (fun h => hk (e.injective h).symm), mul_zero]
  · simp

theorem cutoff_apply_not_mem {n : ℕ} (d : ι → ℂ) (e : Fin n ↪ ι)
    (x : L2 ι) (i : ι) (hi : i ∉ Set.range e) :
    cutoff d e x i = 0 := by
  classical
  rw [cutoff_apply_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [lp.single_apply_ne _ _ _ (fun h => hi ⟨j,h.symm⟩), mul_zero]

/-- The actual operator-norm error is bounded by the supremum of the omitted weights. -/
theorem diagonal_cutoff_error {n : ℕ} (d : ι → ℂ) (e : Fin n ↪ ι)
    (M ε : ℝ) (hM : 0 ≤ M) (hd : ∀ i, ‖d i‖ ≤ M)
    (hε : 0 ≤ ε) (htail : ∀ i ∉ Set.range e, ‖d i‖ ≤ ε) :
    ‖diagonal d M hM hd - cutoff d e‖ ≤ ε := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro x
  calc
    ‖(diagonal d M hM hd - cutoff d e) x‖ ≤ ‖(ε : ℂ) • x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      change ‖d i * x i - cutoff d e x i‖ ≤ ‖(ε : ℂ) * x i‖
      by_cases hi : i ∈ Set.range e
      · obtain ⟨j, rfl⟩ := hi
        rw [cutoff_apply_mem, sub_self, norm_zero]
        exact norm_nonneg _
      · rw [cutoff_apply_not_mem d e x i hi, sub_zero, norm_mul, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg hε]
        exact mul_le_mul_of_nonneg_right (htail i hi) (norm_nonneg _)
    _ = ε * ‖x‖ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hε]

theorem diagonal_cutoff_error_ge_omitted {n : ℕ} (d : ι → ℂ) (e : Fin n ↪ ι)
    (M : ℝ) (hM : 0 ≤ M) (hd : ∀ i, ‖d i‖ ≤ M)
    (i : ι) (hi : i ∉ Set.range e) :
    ‖d i‖ ≤ ‖diagonal d M hM hd - cutoff d e‖ := by
  classical
  let x : L2 ι := lp.single 2 i 1
  have hx : ‖x‖ = 1 := by
    simp [x, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  let A := diagonal d M hM hd - cutoff d e
  calc
    ‖d i‖ = ‖A x i‖ := by
      change ‖d i‖ = ‖d i * x i - cutoff d e x i‖
      rw [cutoff_apply_not_mem d e x i hi, sub_zero]
      simp [x, lp.single_apply_self]
    _ ≤ ‖A x‖ := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) _ i
    _ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
    _ = ‖A‖ := by rw [hx, mul_one]

theorem diagonal_cutoff_error_exact {n : ℕ} (d : ι → ℂ) (e : Fin n ↪ ι)
    (M ε : ℝ) (hM : 0 ≤ M) (hd : ∀ i, ‖d i‖ ≤ M)
    (hε : 0 ≤ ε) (htail : ∀ i ∉ Set.range e, ‖d i‖ ≤ ε)
    (i : ι) (hi : i ∉ Set.range e) (he : ‖d i‖ = ε) :
    ‖diagonal d M hM hd - cutoff d e‖ = ε := by
  apply le_antisymm (diagonal_cutoff_error d e M ε hM hd hε htail)
  rw [← he]
  exact diagonal_cutoff_error_ge_omitted d e M hM hd i hi

#print axioms cutoff_factor
#print axioms cutoff_apply_sum
#print axioms cutoff_apply_mem
#print axioms cutoff_apply_not_mem
#print axioms diagonal_cutoff_error
#print axioms diagonal_cutoff_error_ge_omitted
#print axioms diagonal_cutoff_error_exact
end Manuscript16.V166SpectralCutoffs
