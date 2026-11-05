import GegenbauerFock.GaussianAreaIntrinsicRieszExponentialGram
import GegenbauerFock.GaussianAreaIntrinsicRieszSeparates

/-!
# V007 — finite exponential coherent sums: exact global uniqueness

A finite linear combination of genuine intrinsic Gaussian Fock Riesz
vectors has pointwise entire representative equal to a finite
exponential sum. The positive semidefinite Gaussian exponential
Gram quadratic form vanishes exactly when this finite exponential
sum vanishes at *every* complex point.

This is a global uniqueness criterion; it does not assume
pairwise distinct evaluation points or independent coefficients.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Pointwise reproducing of a finite intrinsic coherent
superposition, with the *actual* Gaussian exponential kernel. -/
theorem intrinsicRieszKernel_finite_coherent_pairing_exp
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) (w : ℂ) :
    inner ℂ (intrinsicRieszKernel alpha ha w)
      (∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)) =
    ∑ i ∈ s, c i * Complex.exp ((alpha : ℂ) * w * star (z i)) := by
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    inner ℂ (intrinsicRieszKernel alpha ha w)
        (c i • intrinsicRieszKernel alpha ha (z i)) =
      c i * inner ℂ (intrinsicRieszKernel alpha ha w)
        (intrinsicRieszKernel alpha ha (z i)) :=
          inner_smul_right
            (intrinsicRieszKernel alpha ha w)
            (intrinsicRieszKernel alpha ha (z i)) (c i)
    _ = c i * Complex.exp ((alpha : ℂ) * w * star (z i)) := by
      rw [intrinsicRieszKernel_pairing_exp]

/-- A finite coherent combination is the zero Hilbert vector exactly
when its associated exponential sum vanishes at every complex point. -/
theorem intrinsicRieszKernel_finite_coherent_eq_zero_iff_exp_sum
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    (∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)) = 0 ↔
    ∀ w : ℂ, (∑ i ∈ s,
      c i * Complex.exp ((alpha : ℂ) * w * star (z i))) = 0 := by
  rw [← intrinsicRieszKernel_pairings_zero_iff alpha ha
      (∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i))]
  simp_rw [intrinsicRieszKernel_finite_coherent_pairing_exp s z c alpha ha]

/-- Exact global uniqueness theorem for finite exponential kernel
quadratic forms: Gram degeneracy iff the entire finite exponential
interpolant vanishes identically. -/
theorem intrinsicRieszKernel_exp_gram_eq_zero_iff_exp_sum
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    (∑ i ∈ s, ∑ j ∈ s,
      star (c i) * c j *
        Complex.exp ((alpha : ℂ) * z i * star (z j))) = 0 ↔
    ∀ w : ℂ, (∑ i ∈ s,
      c i * Complex.exp ((alpha : ℂ) * w * star (z i))) = 0 := by
  rw [intrinsicRieszKernel_exp_gram_eq_zero_iff s z c alpha ha,
    intrinsicRieszKernel_finite_coherent_eq_zero_iff_exp_sum s z c alpha ha]

#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_finite_coherent_pairing_exp
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_finite_coherent_eq_zero_iff_exp_sum
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_gram_eq_zero_iff_exp_sum

end GegenbauerFock.GaussianArea
