import Mathlib

/-! # Manuscript 12, Lemma 5.12: symmetry and positivity of the kernel, and the averaged
matrix `B̄` of the proof of Theorem 5.14

For a compression of the Jacobi operator, the Daleckii–Krein formula (157) (Higham,
Theorem 3.11, a published result cited) writes twice the quadratic form of the kernel as
`Σ_{r,s} f^{[1]}(λ_r, λ_s) c_{rs}²`. If `f` is nondecreasing on `[-1, 1]` and the eigenvalues
lie there, every divided difference is nonnegative (`divDiff_nonneg`), so the form is
nonnegative (`compressed_form_nonneg`); nonnegativity and symmetry pass to the limit of the
compressions (`kernel_psd_of_limit`, `kernel_symm_of_limit`). Integrating the kernel along
the segment `b̃ + τ d`, `0 ≤ τ ≤ 1`, gives the matrix `B̄` of the proof of Theorem 5.14,
again symmetric, positive semidefinite and with the decay `C (1+|k-m|)^{-5}`
(`average_psd`, `average_symm`, `average_decay`). -/

namespace UniformLanczos.Lemma512Kernel

open Finset Filter Topology Set

/-- `f^{[1]}(x,y) = (f(x)-f(y))/(x-y)` for `x ≠ y`, and `f'(x)` on the diagonal. -/
noncomputable def divDiff (f df : ℝ → ℝ) (x y : ℝ) : ℝ :=
  if x = y then df x else (f x - f y) / (x - y)

theorem divDiff_nonneg {f df : ℝ → ℝ} (hf : MonotoneOn f (Icc (-1 : ℝ) 1))
    (hdf : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ df x) {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1)
    (hy : y ∈ Icc (-1 : ℝ) 1) : 0 ≤ divDiff f df x y := by
  unfold divDiff
  split_ifs with h
  · exact hdf x hx
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · rw [div_eq_mul_inv]
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf hx hy hlt.le))
        (inv_nonpos.mpr (sub_nonpos.mpr hlt.le))
    · exact div_nonneg (sub_nonneg.mpr (hf hy hx hgt.le)) (sub_nonneg.mpr hgt.le)

/-- **Positivity of a compressed form.** If `2Q = Σ_{r,s} f^{[1]}(λ_r, λ_s) c_{rs}²` (the
Daleckii–Krein formula (157), cited) with eigenvalues in `[-1, 1]`, then `Q ≥ 0`. -/
theorem compressed_form_nonneg {f df : ℝ → ℝ} (hf : MonotoneOn f (Icc (-1 : ℝ) 1))
    (hdf : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ df x) {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ r, lam r ∈ Icc (-1 : ℝ) 1) (c : Fin n → Fin n → ℝ) (Q : ℝ)
    (hDK : 2 * Q = ∑ r, ∑ s, divDiff f df (lam r) (lam s) * c r s ^ 2) : 0 ≤ Q := by
  have h : 0 ≤ ∑ r, ∑ s, divDiff f df (lam r) (lam s) * c r s ^ 2 :=
    Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun s _ =>
      mul_nonneg (divDiff_nonneg hf hdf (hlam r) (hlam s)) (sq_nonneg _)
  linarith

/-- Nonnegativity of every finite quadratic form passes to the entrywise limit of the
compressions. -/
theorem kernel_psd_of_limit (W : Finset ℤ) (B : ℤ → ℤ → ℝ) (Bn : ℕ → ℤ → ℤ → ℝ)
    (hlim : ∀ k m, Tendsto (fun n => Bn n k m) atTop (𝓝 (B k m)))
    (hpsd : ∀ n, ∀ h : ℤ → ℝ, 0 ≤ ∑ k ∈ W, ∑ m ∈ W, Bn n k m * h k * h m) :
    ∀ h : ℤ → ℝ, 0 ≤ ∑ k ∈ W, ∑ m ∈ W, B k m * h k * h m := by
  intro h
  have ht : Tendsto (fun n => ∑ k ∈ W, ∑ m ∈ W, Bn n k m * h k * h m) atTop
      (𝓝 (∑ k ∈ W, ∑ m ∈ W, B k m * h k * h m)) :=
    tendsto_finset_sum _ fun k _ => tendsto_finset_sum _ fun m _ =>
      ((hlim k m).mul_const _).mul_const _
  exact ge_of_tendsto' ht fun n => hpsd n h

/-- Symmetry passes to the entrywise limit. -/
theorem kernel_symm_of_limit (B : ℤ → ℤ → ℝ) (Bn : ℕ → ℤ → ℤ → ℝ)
    (hlim : ∀ k m, Tendsto (fun n => Bn n k m) atTop (𝓝 (B k m)))
    (hsym : ∀ n k m, Bn n k m = Bn n m k) (k m : ℤ) : B k m = B m k := by
  have h1 := hlim k m
  have h2 := hlim m k
  simp_rw [hsym _ m k] at h2
  exact tendsto_nhds_unique h1 h2

/-- The averaged matrix `B̄_{km} = ∫_0^1 B_{km}(b̃ + τ d) dτ`. -/
noncomputable def average (Bτ : ℝ → ℤ → ℤ → ℝ) (k m : ℤ) : ℝ :=
  ∫ τ in (0:ℝ)..1, Bτ τ k m

theorem average_psd (W : Finset ℤ) (Bτ : ℝ → ℤ → ℤ → ℝ)
    (hint : ∀ k m, IntervalIntegrable (fun τ => Bτ τ k m) MeasureTheory.volume 0 1)
    (hpsd : ∀ τ ∈ Icc (0:ℝ) 1, ∀ h : ℤ → ℝ, 0 ≤ ∑ k ∈ W, ∑ m ∈ W, Bτ τ k m * h k * h m) :
    ∀ h : ℤ → ℝ, 0 ≤ ∑ k ∈ W, ∑ m ∈ W, average Bτ k m * h k * h m := by
  intro h
  have heq : ∑ k ∈ W, ∑ m ∈ W, average Bτ k m * h k * h m =
      ∫ τ in (0:ℝ)..1, ∑ k ∈ W, ∑ m ∈ W, Bτ τ k m * h k * h m := by
    simp only [average]
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_finset_sum]
      · refine Finset.sum_congr rfl fun m _ => ?_
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
      · intro m _; exact ((hint k m).mul_const _).mul_const _
    · intro k _
      have hfun : (fun τ => ∑ m ∈ W, Bτ τ k m * h k * h m) =
          ∑ m ∈ W, fun τ => Bτ τ k m * h k * h m := by
        funext τ; simp [Finset.sum_apply]
      rw [hfun]
      exact IntervalIntegrable.sum _ fun m _ => ((hint k m).mul_const _).mul_const _
  rw [heq]
  exact intervalIntegral.integral_nonneg zero_le_one fun τ hτ => hpsd τ hτ h

theorem average_symm (Bτ : ℝ → ℤ → ℤ → ℝ) (hsym : ∀ τ k m, Bτ τ k m = Bτ τ m k) (k m : ℤ) :
    average Bτ k m = average Bτ m k := by
  simp only [average, hsym _ k m]

theorem average_decay (Bτ : ℝ → ℤ → ℤ → ℝ) {C : ℝ}
    (hdecay : ∀ τ ∈ Icc (0:ℝ) 1, ∀ k m : ℤ, |Bτ τ k m| ≤ C * ((1 + |(k:ℝ) - m|) ^ 5)⁻¹)
    (k m : ℤ) : |average Bτ k m| ≤ C * ((1 + |(k:ℝ) - m|) ^ 5)⁻¹ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun τ => Bτ τ k m) (C := C * ((1 + |(k:ℝ) - m|) ^ 5)⁻¹) (fun τ hτ => by
      rw [uIoc_of_le zero_le_one] at hτ
      rw [Real.norm_eq_abs]; exact hdecay τ ⟨hτ.1.le, hτ.2⟩ k m)
  simp only [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at h
  exact h

end UniformLanczos.Lemma512Kernel

#print axioms UniformLanczos.Lemma512Kernel.divDiff_nonneg
#print axioms UniformLanczos.Lemma512Kernel.compressed_form_nonneg
#print axioms UniformLanczos.Lemma512Kernel.kernel_psd_of_limit
#print axioms UniformLanczos.Lemma512Kernel.kernel_symm_of_limit
#print axioms UniformLanczos.Lemma512Kernel.average_psd
#print axioms UniformLanczos.Lemma512Kernel.average_symm
#print axioms UniformLanczos.Lemma512Kernel.average_decay
