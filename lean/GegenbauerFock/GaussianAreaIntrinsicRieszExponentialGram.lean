import GegenbauerFock.GaussianAreaIntrinsicRieszClosedForm
import GegenbauerFock.GaussianAreaIntrinsicRieszFiniteGramPositive
import GegenbauerFock.GaussianAreaIntrinsicRieszDiagonal

/-!
# V007 — actual intrinsic Fock exponential Gram identities

The certified Riesz representative kernel equals the complex Gaussian
exponential. Combining this exact identity with the already certified
finite intrinsic Hilbert-space Gram formula gives positivity, the
sharp quadratic norm identity and the exact zero criterion directly
for finite matrices of exponential values. No abstract kernel
positivity, new density hypothesis or numerical approximation is used.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The exponential kernel itself is the genuine Hilbert inner
product of the intrinsic Gaussian L² reproducing vectors. -/
theorem intrinsicRieszKernel_pairing_exp
    (alpha : ℝ) (ha : 0 < alpha) (z w : ℂ) :
    inner ℂ (intrinsicRieszKernel alpha ha z)
      (intrinsicRieszKernel alpha ha w) =
      Complex.exp ((alpha : ℂ) * z * star w) :=
  (intrinsicRieszKernel_pairing alpha ha z w).trans
    (intrinsicRieszKernel_closed_form alpha ha z w)

/-- Every finite complex Gaussian exponential Gram matrix is
positive semidefinite on arbitrary complex coefficient vectors. -/
theorem intrinsicRieszKernel_exp_gram_nonneg
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    0 ≤ Complex.re
      (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) := by
  simpa only [intrinsicRieszKernel_closed_form alpha ha] using
    (intrinsicRieszKernel_finite_gram_nonneg s z c alpha ha)

/-- Exact finite coherent Gram energy as the squared norm of
the corresponding superposition of intrinsic Riesz vectors. -/
theorem intrinsicRieszKernel_exp_gram_re_eq_norm_sq
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    Complex.re
      (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) =
    ‖∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)‖ ^ 2 := by
  simpa only [intrinsicRieszKernel_closed_form alpha ha] using
    (intrinsicRieszKernel_finite_gram_re_eq_norm_sq s z c alpha ha)

/-- An exponential Gram quadratic form is zero precisely when
its finite intrinsic coherent superposition is the zero vector. -/
theorem intrinsicRieszKernel_exp_gram_eq_zero_iff
    {ι : Type*} (s : Finset ι) (z c : ι → ℂ)
    (alpha : ℝ) (ha : 0 < alpha) :
    (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * c j *
          Complex.exp ((alpha : ℂ) * z i * star (z j))) = 0 ↔
    (∑ i ∈ s, c i • intrinsicRieszKernel alpha ha (z i)) = 0 := by
  simpa only [intrinsicRieszKernel_closed_form alpha ha] using
    (intrinsicRieszKernel_finite_gram_eq_zero_iff s z c alpha ha)

/-- The full two-point exponential formula agrees exactly with
the independently certified sharp positive real diagonal. -/
theorem intrinsicRieszKernel_exp_diagonal
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    Complex.exp ((alpha : ℂ) * z * star z) =
      (Real.exp (alpha * ‖z‖ ^ 2) : ℂ) := by
  calc
    Complex.exp ((alpha : ℂ) * z * star z) =
        entireRepresentative alpha (intrinsicRieszKernel alpha ha z) z :=
      (intrinsicRieszKernel_closed_form alpha ha z z).symm
    _ = (Real.exp (alpha * ‖z‖ ^ 2) : ℂ) :=
      intrinsicRieszKernel_diagonal_value alpha ha z

#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_pairing_exp
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_gram_nonneg
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_gram_re_eq_norm_sq
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_gram_eq_zero_iff
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_exp_diagonal

end GegenbauerFock.GaussianArea
