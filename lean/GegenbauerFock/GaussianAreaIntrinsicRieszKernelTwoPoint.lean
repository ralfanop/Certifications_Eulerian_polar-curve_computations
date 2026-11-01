import GegenbauerFock.GaussianAreaIntrinsicKernelHermitian
import GegenbauerFock.GaussianAreaIntrinsicPointwiseExpansion

/-!
# V007 — two-point Gaussian reproducing-kernel bound and nondegeneracy

The intrinsic entire Gaussian-L² space is now proven to be the full
Bargmann–Fock Hilbert space, and its reproducing vector is an actual
Gaussian-L² class. The two-point Gaussian estimate follows from the
certified pointwise growth bound evaluated on a genuine Riesz vector.

All theorems below concern the actual intrinsic holomorphic Hilbert
space, not the unrelated ambient Gaussian-L² space.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The true reproducing kernel is controlled at two arbitrary
complex points by the exact diagonal Gaussian weights. -/
theorem intrinsicRieszKernel_twoPoint_norm_sq_le
    (alpha : ℝ) (ha : 0 < alpha) (z w : ℂ) :
    ‖entireRepresentative alpha (intrinsicRieszKernel alpha ha w) z‖ ^ 2 ≤
      Real.exp (alpha * ‖z‖ ^ 2) *
        Real.exp (alpha * ‖w‖ ^ 2) := by
  have h := intrinsicEntire_evaluation_sq_le_exp_norm
    alpha ha (intrinsicRieszKernel alpha ha w) z
  change
    ‖entireRepresentative alpha (intrinsicRieszKernel alpha ha w) z‖ ^ 2 ≤
      Real.exp (alpha * ‖z‖ ^ 2) *
        ‖intrinsicRieszKernel alpha ha w‖ ^ 2 at h
  rwa [intrinsicRieszKernel_norm_sq alpha ha w] at h

/-- In Hilbert-product form the intrinsic Gaussian kernel obeys the
optimal diagonal Cauchy–Schwarz bound. -/
theorem intrinsicRieszKernel_pairing_norm_sq_le
    (alpha : ℝ) (ha : 0 < alpha) (z w : ℂ) :
    ‖inner ℂ (intrinsicRieszKernel alpha ha z)
      (intrinsicRieszKernel alpha ha w)‖ ^ 2 ≤
      Real.exp (alpha * ‖z‖ ^ 2) *
        Real.exp (alpha * ‖w‖ ^ 2) := by
  rw [intrinsicRieszKernel_pairing alpha ha z w]
  exact intrinsicRieszKernel_twoPoint_norm_sq_le alpha ha z w

/-- No point-evaluation reproducing vector vanishes, including at
the origin: its actual Gaussian-L² squared norm is strictly positive. -/
theorem intrinsicRieszKernel_ne_zero
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    intrinsicRieszKernel alpha ha z ≠ 0 := by
  intro hzero
  have hnorm : ‖intrinsicRieszKernel alpha ha z‖ ^ 2 = 0 := by
    rw [hzero]
    simp
  rw [intrinsicRieszKernel_norm_sq alpha ha z] at hnorm
  have hpos := Real.exp_pos (alpha * ‖z‖ ^ 2)
  linarith

#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_twoPoint_norm_sq_le
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_pairing_norm_sq_le
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_ne_zero

end GegenbauerFock.GaussianArea
