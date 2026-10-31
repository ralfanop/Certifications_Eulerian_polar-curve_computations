import GegenbauerFock.GaussianAreaIntrinsicRieszKernel
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# V007 — Hermitian symmetry of the actual intrinsic Gaussian Fock kernel

The reproducing vectors live in the independently defined entire
Gaussian-L² Hilbert space, not merely in the coefficient model.
Hermitian symmetry follows from the genuine Hilbert inner product.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The genuine intrinsic Gaussian Fock reproducing kernel is Hermitian:
evaluation of the w-kernel at z is the conjugate of evaluation of the
z-kernel at w. -/
theorem intrinsicRieszKernel_hermitian
    (alpha : ℝ) (ha : 0 < alpha) (z w : ℂ) :
    star (entireRepresentative alpha (intrinsicRieszKernel alpha ha w) z) =
      entireRepresentative alpha (intrinsicRieszKernel alpha ha z) w := by
  rw [← intrinsicRieszKernel_inner alpha ha z (intrinsicRieszKernel alpha ha w),
      ← intrinsicRieszKernel_inner alpha ha w (intrinsicRieszKernel alpha ha z)]
  exact inner_conj_symm
    (intrinsicRieszKernel alpha ha w)
    (intrinsicRieszKernel alpha ha z)

/-- The Riesz vectors reproduce themselves under the intrinsic
Gaussian L² inner product at both complex evaluation points. -/
theorem intrinsicRieszKernel_pairing
    (alpha : ℝ) (ha : 0 < alpha) (z w : ℂ) :
    inner ℂ (intrinsicRieszKernel alpha ha z)
      (intrinsicRieszKernel alpha ha w) =
    entireRepresentative alpha (intrinsicRieszKernel alpha ha w) z :=
  intrinsicRieszKernel_inner alpha ha z (intrinsicRieszKernel alpha ha w)

#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_hermitian
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_pairing

end GegenbauerFock.GaussianArea
