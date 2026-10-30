import GegenbauerFock.GaussianAreaIntrinsicRieszExactGramScalar

/-!
# V007 — strict positivity and exact degeneracy of finite Gaussian Fock Gram energies

For the actual intrinsic Gaussian-L² Bargmann–Fock Riesz kernel, the
already certified identity of the full complex exponential Gram quadratic
form with the Hilbert norm squared permits an exact strict-positivity
criterion. This criterion is expressed in terms of the *actual* finite
coherent superposition and does not assume linear independence of
reproducing vectors at arbitrary repeated evaluation points.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The real part of the exact finite Gaussian exponential Gram energy
is strictly positive precisely when its intrinsic Hilbert-space coherent
superposition is nonzero. This also handles repeated evaluation points. -/
theorem intrinsicRieszKernel_exp_gram_re_pos_iff
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    0 < Complex.re
      (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) ↔
    (∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)) ≠ 0 := by
  rw [intrinsicRieszKernel_exp_gram_re_eq_norm_sq s z c alpha ha]
  constructor
  · intro h hx
    rw [hx] at h
    simp at h
  · intro hx
    exact sq_pos_of_pos (norm_pos_iff.mpr hx)

/-- Vanishing of the real part of a finite Gaussian exponential
Gram form is equivalent to vanishing of its entire complex value. -/
theorem intrinsicRieszKernel_exp_gram_re_eq_zero_iff
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    Complex.re
      (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) = 0 ↔
    (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) = 0 := by
  rw [intrinsicRieszKernel_exp_gram_eq_complex_norm_sq s z c alpha ha]
  simp

/-- A nonzero finite exponential Gram scalar has strictly positive
real part: it cannot be purely imaginary or negative. -/
theorem intrinsicRieszKernel_exp_gram_re_pos_iff_ne_zero
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    0 < Complex.re
      (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) ↔
    (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) ≠ 0 := by
  rw [intrinsicRieszKernel_exp_gram_re_pos_iff s z c alpha ha]
  exact (not_congr (intrinsicRieszKernel_exp_gram_eq_zero_iff s z c alpha ha)).symm

#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_gram_re_pos_iff
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_gram_re_eq_zero_iff
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_gram_re_pos_iff_ne_zero

end GegenbauerFock.GaussianArea
