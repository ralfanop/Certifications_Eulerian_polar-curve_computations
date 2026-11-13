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


/-- Weighted finite cosine phase transport for nonnegative coupling masses.
    This does not assert a general coupling integral or Wasserstein bound. -/
theorem finite_weighted_cosine_phase_transport {ι : Type*} (S : Finset ι)
    (s : ℝ) (w x y : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) :
    |∑ i ∈ S, w i * (Real.cos (s * x i) - Real.cos (s * y i))| ≤
      |s| * ∑ i ∈ S, w i * |x i - y i| := by
  calc
    |∑ i ∈ S, w i * (Real.cos (s * x i) - Real.cos (s * y i))| ≤
        ∑ i ∈ S, |w i * (Real.cos (s * x i) - Real.cos (s * y i))| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, |s| * (w i * |x i - y i|) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul, abs_of_nonneg (hw i hi)]
          calc
            w i * |Real.cos (s * x i) - Real.cos (s * y i)| ≤
                w i * |s * x i - s * y i| :=
                  mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le _ _) (hw i hi)
            _ = |s| * (w i * |x i - y i|) := by
                  rw [← mul_sub, abs_mul]
                  ring
    _ = |s| * ∑ i ∈ S, w i * |x i - y i| := by rw [Finset.mul_sum]

/-- Weighted finite sine phase transport for nonnegative coupling masses. -/
theorem finite_weighted_sine_phase_transport {ι : Type*} (S : Finset ι)
    (s : ℝ) (w x y : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) :
    |∑ i ∈ S, w i * (Real.sin (s * x i) - Real.sin (s * y i))| ≤
      |s| * ∑ i ∈ S, w i * |x i - y i| := by
  calc
    |∑ i ∈ S, w i * (Real.sin (s * x i) - Real.sin (s * y i))| ≤
        ∑ i ∈ S, |w i * (Real.sin (s * x i) - Real.sin (s * y i))| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, |s| * (w i * |x i - y i|) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul, abs_of_nonneg (hw i hi)]
          calc
            w i * |Real.sin (s * x i) - Real.sin (s * y i)| ≤
                w i * |s * x i - s * y i| :=
                  mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le _ _) (hw i hi)
            _ = |s| * (w i * |x i - y i|) := by
                  rw [← mul_sub, abs_mul]
                  ring
    _ = |s| * ∑ i ∈ S, w i * |x i - y i| := by rw [Finset.mul_sum]

#print axioms Manuscript15.finite_weighted_cosine_phase_transport
#print axioms Manuscript15.finite_weighted_sine_phase_transport


/-- Finite weighted cosine marginal difference bound, in the form used by
    two discrete probability measures sharing an explicit coupling. -/
theorem finite_weighted_cosine_marginal_transport {ι : Type*} (S : Finset ι)
    (s : ℝ) (w x y : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) :
    |(∑ i ∈ S, w i * Real.cos (s * x i)) -
      (∑ i ∈ S, w i * Real.cos (s * y i))| ≤
      |s| * ∑ i ∈ S, w i * |x i - y i| := by
  calc
    |(∑ i ∈ S, w i * Real.cos (s * x i)) -
      (∑ i ∈ S, w i * Real.cos (s * y i))| =
        |∑ i ∈ S, w i * (Real.cos (s * x i) - Real.cos (s * y i))| := by
          congr 1
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ ≤ |s| * ∑ i ∈ S, w i * |x i - y i| :=
      finite_weighted_cosine_phase_transport S s w x y hw

/-- Finite weighted sine marginal difference bound for a discrete coupling. -/
theorem finite_weighted_sine_marginal_transport {ι : Type*} (S : Finset ι)
    (s : ℝ) (w x y : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) :
    |(∑ i ∈ S, w i * Real.sin (s * x i)) -
      (∑ i ∈ S, w i * Real.sin (s * y i))| ≤
      |s| * ∑ i ∈ S, w i * |x i - y i| := by
  calc
    |(∑ i ∈ S, w i * Real.sin (s * x i)) -
      (∑ i ∈ S, w i * Real.sin (s * y i))| =
        |∑ i ∈ S, w i * (Real.sin (s * x i) - Real.sin (s * y i))| := by
          congr 1
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ ≤ |s| * ∑ i ∈ S, w i * |x i - y i| :=
      finite_weighted_sine_phase_transport S s w x y hw

#print axioms Manuscript15.finite_weighted_cosine_marginal_transport
#print axioms Manuscript15.finite_weighted_sine_marginal_transport

end Manuscript15
