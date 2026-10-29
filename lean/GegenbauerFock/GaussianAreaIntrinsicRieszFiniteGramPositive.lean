import GegenbauerFock.GaussianAreaIntrinsicKernelHermitian
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# V007 — actual finite positive semidefiniteness of intrinsic Fock Riesz Gram kernels

For every finite collection of complex evaluation points and arbitrary
complex coefficients, the Hermitian quadratic form of the TRUE
holomorphic Gaussian L² Riesz kernel is nonnegative. The proof reduces
the double kernel sum to the squared Hilbert norm of the actual finite
linear combination of the intrinsic reproducing vectors, without
assuming abstract kernel positivity.

This is a genuine kernel statement on the intrinsic Gaussian L²
holomorphic Hilbert space rather than an auxiliary coefficient model.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The finite quadratic form of the true intrinsic Fock reproducing
kernel is the norm square of its corresponding finite coherent
superposition, regarded as a complex scalar. -/
theorem intrinsicRieszKernel_finite_gram_eq_inner
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    (∑ i ∈ s, ∑ j ∈ s,
      star (c i) * c j *
        entireRepresentative alpha (intrinsicRieszKernel alpha ha (z j)) (z i)) =
    inner ℂ
      (∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i))
      (∑ j ∈ s, c j • intrinsicRieszKernel alpha ha (z j)) := by
  rw [sum_inner]
  simp_rw [inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [inner_smul_left, inner_smul_right,
    intrinsicRieszKernel_pairing]
  ring

/-- Every finite Hermitian Gram matrix formed by intrinsic Gaussian
Fock reproducing vectors is positive semidefinite, even for arbitrary
repeated evaluation points. -/
theorem intrinsicRieszKernel_finite_gram_nonneg
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    0 ≤ Complex.re
      (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          entireRepresentative alpha
            (intrinsicRieszKernel alpha ha (z j)) (z i)) := by
  rw [intrinsicRieszKernel_finite_gram_eq_inner s z c alpha ha]
  exact inner_self_nonneg

/-- The real part of every finite coherent Gram quadratic form is
exactly the squared intrinsic Gaussian-L² norm of the finite Riesz
superposition. This sharpens abstract nonnegativity to an equality. -/
theorem intrinsicRieszKernel_finite_gram_re_eq_norm_sq
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    Complex.re
      (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          entireRepresentative alpha
            (intrinsicRieszKernel alpha ha (z j)) (z i)) =
    ‖∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)‖ ^ 2 := by
  rw [intrinsicRieszKernel_finite_gram_eq_inner s z c alpha ha]
  exact inner_self_eq_norm_sq (𝕜 := ℂ)
    (∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i))

/-- Exact cancellation criterion for the intrinsic Gaussian Riesz Gram
form: it vanishes if and only if the corresponding finite coherent
Hilbert-space superposition is the zero vector. -/
theorem intrinsicRieszKernel_finite_gram_eq_zero_iff
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    (∑ i ∈ s, ∑ j ∈ s,
      star (c i) * c j *
        entireRepresentative alpha
          (intrinsicRieszKernel alpha ha (z j)) (z i)) = 0 ↔
    (∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)) = 0 := by
  rw [intrinsicRieszKernel_finite_gram_eq_inner s z c alpha ha]
  exact (inner_self_eq_zero (𝕜 := ℂ)
    (x := ∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)))


#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_finite_gram_eq_inner
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_finite_gram_nonneg
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_finite_gram_re_eq_norm_sq
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_finite_gram_eq_zero_iff

end GegenbauerFock.GaussianArea
