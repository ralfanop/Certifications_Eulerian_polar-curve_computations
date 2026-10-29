import GegenbauerFock.GaussianAreaIntrinsicRieszKernel
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# V007 — sharp diagonal value of the genuine Gaussian Fock Riesz kernel

The preceding Lean-verified Riesz reproducing vectors are elements of
the intrinsic entire Gaussian L² Hilbert space. Their reproducing
identity and squared Hilbert norm give the exact *complex value*
of the diagonal reproducing kernel, not merely its norm bound.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The true intrinsic Riesz kernel evaluated on the diagonal is
the positive real Gaussian exponential, regarded as a complex number. -/
theorem intrinsicRieszKernel_diagonal_value
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    entireRepresentative alpha (intrinsicRieszKernel alpha ha z) z =
      (Real.exp (alpha * ‖z‖ ^ 2) : ℂ) := by
  calc
    entireRepresentative alpha (intrinsicRieszKernel alpha ha z) z =
      inner ℂ (intrinsicRieszKernel alpha ha z)
        (intrinsicRieszKernel alpha ha z) :=
        (intrinsicRieszKernel_inner alpha ha z
          (intrinsicRieszKernel alpha ha z)).symm
    _ = (‖intrinsicRieszKernel alpha ha z‖ : ℂ) ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    _ = (Real.exp (alpha * ‖z‖ ^ 2) : ℂ) := by
      exact_mod_cast intrinsicRieszKernel_norm_sq alpha ha z

/-- The exact diagonal of the intrinsic reproducing kernel never vanishes. -/
theorem intrinsicRieszKernel_diagonal_ne_zero
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    entireRepresentative alpha (intrinsicRieszKernel alpha ha z) z ≠ 0 := by
  rw [intrinsicRieszKernel_diagonal_value alpha ha z]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos (alpha * ‖z‖ ^ 2)))

#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_diagonal_value
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_diagonal_ne_zero

end GegenbauerFock.GaussianArea
