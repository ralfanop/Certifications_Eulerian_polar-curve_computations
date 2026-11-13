import Mathlib

/-!
# Manuscript 15 — finite Kantorovich test-function coupling bound

A general finite-coupling estimate for an arbitrary real-valued Lipschitz
test function. This is a discrete precursor, not a theorem about the
integral of a general coupling or the Wasserstein-1 infimum.
-/

noncomputable section
namespace Manuscript15

/-- For a finite nonnegative coupling, the difference of test-function
marginals is bounded by its weighted transport cost, provided the test
function satisfies a Lipschitz bound on the paired support. -/
theorem finite_lipschitz_test_marginal_transport
    {ι : Type*} (S : Finset ι) (w x y : ι → ℝ)
    (φ : ℝ → ℝ) (L : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hLip : ∀ i ∈ S, |φ (x i) - φ (y i)| ≤ L * |x i - y i|) :
    |(∑ i ∈ S, w i * φ (x i)) -
      (∑ i ∈ S, w i * φ (y i))| ≤
      L * ∑ i ∈ S, w i * |x i - y i| := by
  calc
    |(∑ i ∈ S, w i * φ (x i)) -
      (∑ i ∈ S, w i * φ (y i))| =
        |∑ i ∈ S, w i * (φ (x i) - φ (y i))| := by
          congr 1
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ ≤ ∑ i ∈ S, |w i * (φ (x i) - φ (y i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, L * (w i * |x i - y i|) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i hi)]
      calc
        w i * |φ (x i) - φ (y i)| ≤
            w i * (L * |x i - y i|) :=
          mul_le_mul_of_nonneg_left (hLip i hi) (hw i hi)
        _ = L * (w i * |x i - y i|) := by ring
    _ = L * ∑ i ∈ S, w i * |x i - y i| := by
      rw [Finset.mul_sum]

/-- The unit-Lipschitz specialization is the discrete dual
Kantorovich test inequality. No optimal transport is assumed. -/
theorem finite_unit_lipschitz_test_marginal_transport
    {ι : Type*} (S : Finset ι) (w x y : ι → ℝ)
    (φ : ℝ → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hLip : ∀ i ∈ S, |φ (x i) - φ (y i)| ≤ |x i - y i|) :
    |(∑ i ∈ S, w i * φ (x i)) -
      (∑ i ∈ S, w i * φ (y i))| ≤
      ∑ i ∈ S, w i * |x i - y i| := by
  simpa using
    (finite_lipschitz_test_marginal_transport S w x y φ 1 hw
      (by
        intro i hi
        simpa using hLip i hi))

#print axioms Manuscript15.finite_lipschitz_test_marginal_transport
#print axioms Manuscript15.finite_unit_lipschitz_test_marginal_transport

end Manuscript15
