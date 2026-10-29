import GegenbauerFock.GaussianAreaIntrinsicRieszExponentialGram
import GegenbauerFock.GaussianAreaIntrinsicExponentialTwoPoint

/-!
# V007 — exact complex scalar Gaussian exponential Gram positivity

For arbitrary finite coherent superpositions in the *genuine*
intrinsic Gaussian-L² holomorphic Hilbert space, the exponential
Gram quadratic form is not only of nonnegative real part: its full
complex value equals the real squared Hilbert norm. In particular,
its imaginary part vanishes identically. We also record the
nonnegative two-point Gram determinant.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The entire complex exponential Gram quadratic form, not merely
its real part, is the real squared Gaussian-Hilbert norm. -/
theorem intrinsicRieszKernel_exp_gram_eq_complex_norm_sq
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) =
      (‖∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)‖ ^ 2 : ℂ) := by
  calc
    (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) =
      inner ℂ
        (∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i))
        (∑ j ∈ s, c j • intrinsicRieszKernel alpha ha (z j)) := by
          simpa only [intrinsicRieszKernel_closed_form alpha ha] using
            (intrinsicRieszKernel_finite_gram_eq_inner s z c alpha ha)
    _ = (‖∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)‖ ^ 2 : ℂ) := by
      apply Complex.ext
      · simpa using (inner_self_eq_norm_sq (𝕜 := ℂ)
          (∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)))
      · simpa using (inner_self_im (𝕜 := ℂ)
          (∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)))

/-- The imaginary part of every finite Gaussian exponential Gram
quadratic form is exactly zero. -/
theorem intrinsicRieszKernel_exp_gram_im_zero
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    Complex.im
      (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) = 0 := by
  rw [intrinsicRieszKernel_exp_gram_eq_complex_norm_sq s z c alpha ha]
  simp

/-- Every finite Gaussian exponential Gram energy is a genuinely
nonnegative real number embedded in the complex scalars. -/
theorem intrinsicRieszKernel_exp_gram_is_nonnegative_real
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    ∃ r : ℝ, 0 ≤ r ∧
      (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) = (r : ℂ) := by
  refine ⟨‖∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)‖ ^ 2,
    sq_nonneg _, ?_⟩
  exact intrinsicRieszKernel_exp_gram_eq_complex_norm_sq s z c alpha ha

/-- The exact 2-by-2 exponential Gram determinant is nonnegative
for arbitrary evaluation points in the intrinsic Gaussian Fock space. -/
theorem intrinsicRieszKernel_exp_twoPoint_determinant_nonneg
    (alpha : ℝ) (ha : 0 < alpha) (z w : ℂ) :
    0 ≤ Real.exp (alpha * ‖z‖ ^ 2) *
        Real.exp (alpha * ‖w‖ ^ 2) -
        ‖Complex.exp ((alpha : ℂ) * z * star w)‖ ^ 2 := by
  exact sub_nonneg.mpr
    (intrinsicRiesz_exponential_twoPoint_norm_sq_le alpha ha z w)

#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_gram_eq_complex_norm_sq
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_gram_im_zero
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_gram_is_nonnegative_real
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_twoPoint_determinant_nonneg

end GegenbauerFock.GaussianArea
