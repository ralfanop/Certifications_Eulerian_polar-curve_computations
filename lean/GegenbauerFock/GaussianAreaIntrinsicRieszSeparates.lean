import GegenbauerFock.GaussianAreaIntrinsicRieszKernel
import GegenbauerFock.GaussianAreaIntrinsicEntireEvaluation

/-!
# V007 — reproducing vectors separate intrinsic Bargmann–Fock Hilbert classes

The previously verified pointwise Riesz formula and injectivity of the
canonical entire representative imply that the *full complex family*
of intrinsic reproducing vectors separates vectors of the genuine
holomorphic Gaussian-L² Hilbert space. No polynomial-density hypothesis
or identification with all ambient Gaussian L² classes is used.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Pairing against all genuine Gaussian coherent Riesz vectors
distinguishes every two intrinsic holomorphic-L² classes. -/
theorem intrinsicRieszKernel_pairings_separate
    (alpha : ℝ) (ha : 0 < alpha)
    (x y : entireGaussianL2Submodule alpha)
    (h : ∀ z : ℂ,
      inner ℂ (intrinsicRieszKernel alpha ha z) x =
      inner ℂ (intrinsicRieszKernel alpha ha z) y) :
    x = y := by
  apply entireRepresentative_injective alpha
  funext z
  calc
    entireRepresentative alpha x z =
        inner ℂ (intrinsicRieszKernel alpha ha z) x :=
      (intrinsicRieszKernel_inner alpha ha z x).symm
    _ = inner ℂ (intrinsicRieszKernel alpha ha z) y := h z
    _ = entireRepresentative alpha y z :=
      intrinsicRieszKernel_inner alpha ha z y

/-- A holomorphic Gaussian-L² class orthogonal to every intrinsic
reproducing vector vanishes identically. -/
theorem intrinsicRieszKernel_pairings_zero_iff
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    (∀ z : ℂ, inner ℂ (intrinsicRieszKernel alpha ha z) x = 0) ↔
      x = 0 := by
  constructor
  · intro h
    apply intrinsicRieszKernel_pairings_separate alpha ha x 0
    intro z
    simpa using h z
  · intro hx
    subst x
    intro z
    simp

#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_pairings_separate
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_pairings_zero_iff

end GegenbauerFock.GaussianArea
