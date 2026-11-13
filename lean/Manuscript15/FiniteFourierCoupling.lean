import Mathlib

/-!
# Manuscript 15: finite coupling Fourier transport

Finite-sample integration precursor to the measure-theoretic W₁ theorem.
This proves estimates for arbitrary finite couplings, with no claim
about arbitrary probability measures, optimal transport, or W₁.
-/

noncomputable section
namespace Manuscript15

/-- Finite unweighted cosine phase coupling estimate. -/
theorem finite_cosine_phase_transport {ι : Type*} (S : Finset ι)
    (s : ℝ) (x y : ι → ℝ) :
    |∑ i ∈ S, (Real.cos (s * x i) - Real.cos (s * y i))| ≤
      |s| * ∑ i ∈ S, |x i - y i| := by
  calc
    |∑ i ∈ S, (Real.cos (s * x i) - Real.cos (s * y i))| ≤
        ∑ i ∈ S, |Real.cos (s * x i) - Real.cos (s * y i)| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, |s| * |x i - y i| := by
          apply Finset.sum_le_sum
          intro i hi
          calc
            _ ≤ |s * x i - s * y i| := Real.abs_cos_sub_cos_le _ _
            _ = |s| * |x i - y i| := by rw [← mul_sub, abs_mul]
    _ = |s| * ∑ i ∈ S, |x i - y i| := by
          rw [Finset.mul_sum]

/-- Finite unweighted sine phase coupling estimate. -/
theorem finite_sine_phase_transport {ι : Type*} (S : Finset ι)
    (s : ℝ) (x y : ι → ℝ) :
    |∑ i ∈ S, (Real.sin (s * x i) - Real.sin (s * y i))| ≤
      |s| * ∑ i ∈ S, |x i - y i| := by
  calc
    |∑ i ∈ S, (Real.sin (s * x i) - Real.sin (s * y i))| ≤
        ∑ i ∈ S, |Real.sin (s * x i) - Real.sin (s * y i)| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, |s| * |x i - y i| := by
          apply Finset.sum_le_sum
          intro i hi
          calc
            _ ≤ |s * x i - s * y i| := Real.abs_sin_sub_sin_le _ _
            _ = |s| * |x i - y i| := by rw [← mul_sub, abs_mul]
    _ = |s| * ∑ i ∈ S, |x i - y i| := by
          rw [Finset.mul_sum]

#print axioms Manuscript15.finite_cosine_phase_transport
#print axioms Manuscript15.finite_sine_phase_transport

end Manuscript15
