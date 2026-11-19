import Mathlib

noncomputable section
open scoped ENNReal

/-! M16 §13: actual bounded diagonal spectral inverse on the Hilbert space
of square-summable coefficients. No geometric equivalence to the differential
operator on S³ is assumed; this is the coefficient-space realization of its
stated spectral list. Both signs and multiplicities are retained. -/
namespace Manuscript16.V166L2SpectralInverse

abbrev L2 (ι : Type*) := lp (fun _ : ι => ℂ) 2

variable {ι : Type*}

noncomputable def diagonalVector (d : ι → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hd : ∀ i, ‖d i‖ ≤ M) (x : L2 ι) : L2 ι :=
  ⟨fun i => d i * x i, by
    apply (lp.memℓp ((M : ℂ) • x)).mono'
    intro i
    change ‖d i * x i‖ ≤ ‖(M : ℂ) * x i‖
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hM]
    exact mul_le_mul_of_nonneg_right (hd i) (norm_nonneg _)⟩

theorem diagonalVector_norm (d : ι → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hd : ∀ i, ‖d i‖ ≤ M) (x : L2 ι) :
    ‖diagonalVector d M hM hd x‖ ≤ M * ‖x‖ := by
  calc
    ‖diagonalVector d M hM hd x‖ ≤ ‖(M : ℂ) • x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      change ‖d i * x i‖ ≤ ‖(M : ℂ) * x i‖
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hM]
      exact mul_le_mul_of_nonneg_right (hd i) (norm_nonneg _)
    _ = M * ‖x‖ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hM]

noncomputable def diagonal (d : ι → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hd : ∀ i, ‖d i‖ ≤ M) : L2 ι →L[ℂ] L2 ι :=
  (show L2 ι →ₗ[ℂ] L2 ι from
    { toFun := diagonalVector d M hM hd
      map_add' := by
        intro x y
        apply lp.ext
        funext i
        change d i * (x i + y i) = d i * x i + d i * y i
        ring
      map_smul' := by
        intro c x
        apply lp.ext
        funext i
        change d i * (c * x i) = c * (d i * x i)
        ring }).mkContinuous M (diagonalVector_norm d M hM hd)

@[simp] theorem diagonal_apply (d : ι → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hd : ∀ i, ‖d i‖ ≤ M) (x : L2 ι) (i : ι) :
    diagonal d M hM hd x i = d i * x i := rfl

theorem diagonal_norm_le (d : ι → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hd : ∀ i, ‖d i‖ ≤ M) :
    ‖diagonal d M hM hd‖ ≤ M :=
  ContinuousLinearMap.opNorm_le_bound _ hM (diagonalVector_norm d M hM hd)

theorem diagonal_norm_ge_entry (d : ι → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hd : ∀ i, ‖d i‖ ≤ M) (i : ι) :
    ‖d i‖ ≤ ‖diagonal d M hM hd‖ := by
  classical
  let x : L2 ι := lp.single 2 i 1
  have hx : ‖x‖ = 1 := by
    simp [x, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  calc
    ‖d i‖ = ‖diagonal d M hM hd x i‖ := by
      rw [diagonal_apply]
      simp [x, lp.single_apply_self]
    _ ≤ ‖diagonal d M hM hd x‖ :=
      lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) _ i
    _ ≤ ‖diagonal d M hM hd‖ * ‖x‖ := (diagonal d M hM hd).le_opNorm x
    _ = ‖diagonal d M hM hd‖ := by rw [hx, mul_one]

/-- Mode l+2, temporal m=l+2+2k, both resonances excluded. -/
def MaxwellIndex := Σ l : ℕ, {k : ℤ // k ≠ 0 ∧ k ≠ -((l : ℤ)+2)} ×
  Fin (2 * ((l+2)^2-1))

/-- Both signed spatial Dirac eigenvalues, each with its own multiplicity. -/
def DiracIndex := Σ n : ℕ, Bool × Fin ((n+1)*(n+2))

abbrev MixedIndex := MaxwellIndex ⊕ DiracIndex

noncomputable def maxwellWeight (i : MaxwellIndex) : ℝ :=
  ((-4 : ℝ) * (i.2.1.1 : ℝ) * (((i.1 : ℤ)+2+i.2.1.1 : ℤ) : ℝ))⁻¹

noncomputable def diracWeight (i : DiracIndex) : ℝ :=
  if i.2.1 then ((i.1 : ℝ)+3/2)⁻¹ else -((i.1 : ℝ)+3/2)⁻¹

theorem maxwellWeight_bound (i : MaxwellIndex) : |maxwellWeight i| ≤ 1/4 := by
  have ha : (1 : ℝ) ≤ |(i.2.1.1 : ℝ)| := by
    exact_mod_cast Int.one_le_abs i.2.1.2.1
  have hz : (i.1 : ℤ)+2+i.2.1.1 ≠ 0 := by
    intro h
    apply i.2.1.2.2
    omega
  have hb : (1 : ℝ) ≤ |(((i.1 : ℤ)+2+i.2.1.1 : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hz
  have hc : (1 : ℝ) ≤ |(i.2.1.1 : ℝ)| * |(((i.1 : ℤ)+2+i.2.1.1 : ℤ) : ℝ)| := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ _ := mul_le_mul ha hb (by norm_num) (by positivity)
  unfold maxwellWeight
  rw [abs_inv, abs_mul, abs_mul]
  have h4 : |(-4 : ℝ)| = 4 := by norm_num
  rw [h4, ← one_div, div_le_iff₀ (by positivity)]
  nlinarith

theorem diracWeight_bound (i : DiracIndex) : |diracWeight i| ≤ 2/3 := by
  have h : (0 : ℝ) < (i.1 : ℝ)+3/2 := by positivity
  unfold diracWeight
  split <;> simp only [abs_neg, abs_inv, abs_of_pos h]
  all_goals
    rw [← one_div, div_le_iff₀ h]
    nlinarith [Nat.cast_nonneg (α := ℝ) i.1]

noncomputable def mixedWeight : MixedIndex → ℂ :=
  Sum.elim (fun i => (maxwellWeight i : ℂ)) (fun i => (diracWeight i : ℂ))

theorem mixedWeight_bound (i : MixedIndex) : ‖mixedWeight i‖ ≤ (2 : ℝ)/3 := by
  cases i with
  | inl x =>
    change ‖(maxwellWeight x : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (maxwellWeight_bound x).trans (by norm_num)
  | inr x =>
    change ‖(diracWeight x : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact diracWeight_bound x

noncomputable def mixedInverse : L2 MixedIndex →L[ℂ] L2 MixedIndex :=
  diagonal mixedWeight (2/3) (by norm_num) mixedWeight_bound

theorem mixedInverse_norm : ‖mixedInverse‖ = (2 : ℝ)/3 := by
  apply le_antisymm
  · exact diagonal_norm_le _ _ _ _
  · let i : MixedIndex := Sum.inr ⟨0, true, ⟨0, by decide⟩⟩
    have h := diagonal_norm_ge_entry mixedWeight (2/3) (by norm_num) mixedWeight_bound i
    have hi : ‖mixedWeight i‖ = (2 : ℝ)/3 := by
      change ‖(diracWeight ⟨0,true,⟨0,by decide⟩⟩ : ℂ)‖ = _
      rw [Complex.norm_real, Real.norm_eq_abs]
      norm_num [diracWeight]
    rw [hi] at h
    exact h

#print axioms diagonalVector_norm
#print axioms diagonal_apply
#print axioms diagonal_norm_le
#print axioms diagonal_norm_ge_entry
#print axioms maxwellWeight_bound
#print axioms diracWeight_bound
#print axioms mixedWeight_bound
#print axioms mixedInverse_norm
end Manuscript16.V166L2SpectralInverse
