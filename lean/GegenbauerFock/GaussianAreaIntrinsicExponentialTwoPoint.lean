import GegenbauerFock.GaussianAreaIntrinsicRieszClosedForm
import GegenbauerFock.GaussianAreaIntrinsicRieszKernelTwoPoint
import GegenbauerFock.GaussianAreaIntrinsicKernelHermitian

/-!
# V007 — exact exponential two-point kernel and Hilbert bounds

These statements transport previously certified Hilbert-space facts for
the genuine Gaussian-L² reproducing vectors to the explicit complex
exponential kernel. No additional abstract positivity hypothesis,
density assumption or choice of basis is required.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The exact complex exponential kernel is Hermitian for every two
complex points. -/
theorem intrinsicRiesz_exponential_hermitian
    (alpha : ℝ) (ha : 0 < alpha) (z w : ℂ) :
    star (Complex.exp ((alpha : ℂ) * z * star w)) =
      Complex.exp ((alpha : ℂ) * w * star z) := by
  rw [← intrinsicRieszKernel_closed_form alpha ha z w,
    ← intrinsicRieszKernel_closed_form alpha ha w z]
  exact intrinsicRieszKernel_hermitian alpha ha z w

/-- Sharp two-point Cauchy–Schwarz inequality for the exact Gaussian
exponential reproducing kernel of the intrinsic Fock Hilbert space. -/
theorem intrinsicRiesz_exponential_twoPoint_norm_sq_le
    (alpha : ℝ) (ha : 0 < alpha) (z w : ℂ) :
    ‖Complex.exp ((alpha : ℂ) * z * star w)‖ ^ 2 ≤
      Real.exp (alpha * ‖z‖ ^ 2) *
        Real.exp (alpha * ‖w‖ ^ 2) := by
  rw [← intrinsicRieszKernel_closed_form alpha ha z w]
  exact intrinsicRieszKernel_twoPoint_norm_sq_le alpha ha z w

#print axioms GegenbauerFock.GaussianArea.intrinsicRiesz_exponential_hermitian
#print axioms GegenbauerFock.GaussianArea.intrinsicRiesz_exponential_twoPoint_norm_sq_le

end GegenbauerFock.GaussianArea
