import GegenbauerFock.GaussianAreaIntrinsicRieszOffDiagonalSeries
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# V007 — closed exponential formula of the intrinsic Fock reproducing kernel

The actual pointwise values of the intrinsic Gaussian-L² Riesz vectors
are compared with the *complex exponential*, not merely a formal
coefficient series. The kernel is the full-plane Bargmann–Fock kernel
with the convention of conjugate linearity in the first inner-product
variable.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Each pair of coherent coefficients has the exact exponential
Taylor-series scalar form. -/
theorem intrinsicFock_coherent_coordinate_inner
    (alpha : ℝ) (ha : 0 < alpha) (z w : ℂ) (n : ℕ) :
    inner ℂ (FockEvaluation.kernelCoordinate alpha z n)
      (FockEvaluation.kernelCoordinate alpha w n) =
        ((alpha : ℂ) * z * star w) ^ n / (Nat.factorial n : ℂ) := by
  have hp : 0 ≤ alpha ^ n / (Nat.factorial n : ℝ) := by
    positivity
  have hsqrt :
      (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) ^ 2 =
        ((alpha ^ n / (Nat.factorial n : ℝ) : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt hp
  change
    ((Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) * (star w) ^ n) *
      star ((Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) *
        (star z) ^ n) =
      ((alpha : ℂ) * z * star w) ^ n / (Nat.factorial n : ℂ)
  simp only [star_mul, star_pow, star_star,
    Complex.star_def, Complex.conj_ofReal, mul_pow]
  -- Both sides have the same normalized real coefficient.
  calc
    ((Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) * (star w) ^ n) *
        ((Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) * z ^ n) =
      (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) ^ 2 *
        (z ^ n * (star w) ^ n) := by ring
    _ = ((alpha ^ n / (Nat.factorial n : ℝ) : ℝ) : ℂ) *
          (z ^ n * (star w) ^ n) := by rw [hsqrt]
    _ = ((alpha : ℂ) ^ n * z ^ n * (star w) ^ n) /
        (Nat.factorial n : ℂ) := by
      push_cast
      ring

/-- The genuine off-diagonal Bargmann–Fock reproducing kernel is
the entire complex exponential for all complex evaluation points. -/
theorem intrinsicRieszKernel_closed_form
    (alpha : ℝ) (ha : 0 < alpha) (z w : ℂ) :
    entireRepresentative alpha (intrinsicRieszKernel alpha ha w) z =
      Complex.exp ((alpha : ℂ) * z * star w) := by
  rw [intrinsicRieszKernel_offDiagonal_tsum alpha ha z w]
  simp_rw [intrinsicFock_coherent_coordinate_inner alpha ha z w]
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

#print axioms GegenbauerFock.GaussianArea.intrinsicFock_coherent_coordinate_inner
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_closed_form

end GegenbauerFock.GaussianArea
