import GegenbauerFock.GramIntegralComplete
import GegenbauerFock.GramKernelSeries

/-!
# V007: genuine kernel of compact positive Gram operator

This basic spectral theorem establishes the kernel correspondence
for the actual infinite-dimensional ultraspherical operators. It
does not assert a full spectral decomposition, eigenvalue enumeration,
trace-class membership, or an unproved injectivity assumption.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Kernel of the actual Gram C†C equals the kernel of C,
expressed as a pointwise iff in the concrete source Hilbert space. -/
theorem gram_apply_eq_zero_iff_C_eq_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    gram lam alpha hlam ha f = 0 ↔
      C lam alpha hlam ha f = 0 := by
  constructor
  · intro h
    have hs : ‖C lam alpha hlam ha f‖ ^ 2 =
        RCLike.re (inner ℂ (gram lam alpha hlam ha f) f) :=
      HilbertGram.gram_norm_sq (C lam alpha hlam ha) f
    have hn : ‖C lam alpha hlam ha f‖ ^ 2 = 0 := by
      rw [h] at hs
      simpa using hs
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  · intro h
    change C_adjoint lam alpha hlam ha
      (C lam alpha hlam ha f) = 0
    rw [h]
    simp

/-- Equality of the actual closed linear kernels, not just an implication
for individual L² vectors: ker(C†C) = ker(C). -/
theorem gram_ker_eq_C_ker
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    LinearMap.ker (gram lam alpha hlam ha).toLinearMap =
      LinearMap.ker (C lam alpha hlam ha).toLinearMap := by
  ext f
  simpa only [LinearMap.mem_ker] using
    (gram_apply_eq_zero_iff_C_eq_zero lam alpha hlam ha f)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_ker_eq_C_ker

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_apply_eq_zero_iff_C_eq_zero

end GegenbauerFock.GeneralUltrasphericalFock
