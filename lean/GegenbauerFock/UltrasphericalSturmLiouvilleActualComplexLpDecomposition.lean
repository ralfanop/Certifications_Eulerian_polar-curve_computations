import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatComplexCFCS1Bridge
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# V007 — concrete complexification of the original weighted real L² space

All maps act on the ACTUAL Gegenbauer probability measure, not on a
surrogate Fourier sequence model. The canonical real-to-complex
inclusion and its real/imaginary projections are bounded REAL-linear
maps, constructed using Mathlib's pointwise compLpL operation.

Every COMPLEX weighted-L² vector is the sum of the complex images of
its real and imaginary parts, with the imaginary summand multiplied by I.
The maps can therefore be used for the honest complex extension of
the closed real Sturm heat semigroup, without identifying the semigroup
with the unrelated complex Gegenbauer--Fock Gram.

No new spectral/eigenvalue equivalence is postulated.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev HR (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev HC (lam : ℝ) := Lp ℂ 2 (measure lam)

/-- Canonical bounded real-linear inclusion of actual weighted real L²
into its complex-valued counterpart, represented pointwise by r ↦ (r:ℂ). -/
noncomputable def realToComplexLp (lam : ℝ) : HR lam →L[ℝ] HC lam :=
  Complex.ofRealCLM.compLpL 2 (measure lam)

/-- Actual real part on complex-valued weighted L². -/
noncomputable def complexLpRe (lam : ℝ) : HC lam →L[ℝ] HR lam :=
  Complex.reCLM.compLpL 2 (measure lam)

/-- Actual imaginary part on complex-valued weighted L². -/
noncomputable def complexLpIm (lam : ℝ) : HC lam →L[ℝ] HR lam :=
  Complex.imCLM.compLpL 2 (measure lam)

/-- Taking the real part after real-to-complex inclusion is exactly
the identity on all of the genuine weighted real L². -/
theorem complexLpRe_realToComplexLp (lam : ℝ) (f : HR lam) :
    complexLpRe lam (realToComplexLp lam f) = f := by
  ext1
  filter_upwards [
    Complex.reCLM.coeFn_compLpL (realToComplexLp lam f),
    Complex.ofRealCLM.coeFn_compLpL f
  ] with x hre hinc
  have h := hre.trans (congrArg Complex.reCLM hinc)
  simpa only [complexLpRe, realToComplexLp,
    Complex.reCLM_apply, Complex.ofRealCLM_apply,
    Complex.ofReal_re] using h

/-- The imaginary component of a real L² function is zero after
canonical inclusion into complex weighted L². -/
theorem complexLpIm_realToComplexLp (lam : ℝ) (f : HR lam) :
    complexLpIm lam (realToComplexLp lam f) = 0 := by
  ext1
  filter_upwards [
    Complex.imCLM.coeFn_compLpL (realToComplexLp lam f),
    Complex.ofRealCLM.coeFn_compLpL f,
    (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := measure lam))
  ] with x him hinc hz
  have h := him.trans (congrArg Complex.imCLM hinc)
  have hzero : (complexLpIm lam (realToComplexLp lam f)) x = (0 : ℝ) := by
    simpa only [complexLpIm, realToComplexLp,
      Complex.imCLM_apply, Complex.ofRealCLM_apply,
      Complex.ofReal_im] using h
  exact hzero.trans hz.symm

/-- Every complex-valued weighted L² function is recovered exactly
from the actual real-valued L² functions formed by its two parts. -/
theorem complexLp_eq_realToComplex_re_add_I_im
    (lam : ℝ) (f : HC lam) :
    realToComplexLp lam (complexLpRe lam f) +
      Complex.I • realToComplexLp lam (complexLpIm lam f) = f := by
  ext1
  filter_upwards [
    Lp.coeFn_add
      (realToComplexLp lam (complexLpRe lam f))
      (Complex.I • realToComplexLp lam (complexLpIm lam f)),
    Lp.coeFn_smul Complex.I (realToComplexLp lam (complexLpIm lam f)),
    Complex.ofRealCLM.coeFn_compLpL (complexLpRe lam f),
    Complex.ofRealCLM.coeFn_compLpL (complexLpIm lam f),
    Complex.reCLM.coeFn_compLpL f,
    Complex.imCLM.coeFn_compLpL f
  ] with x hadd hsm hincRe hincIm hre him
  have hadd' :
      (realToComplexLp lam (complexLpRe lam f) +
        Complex.I • realToComplexLp lam (complexLpIm lam f)) x =
      (realToComplexLp lam (complexLpRe lam f)) x +
        (Complex.I • realToComplexLp lam (complexLpIm lam f)) x := by
    simpa only [Pi.add_apply] using hadd
  have hincRe' :
      (realToComplexLp lam (complexLpRe lam f)) x =
        ((complexLpRe lam f) x : ℂ) := by
    simpa only [realToComplexLp, Complex.ofRealCLM_apply] using hincRe
  have hincIm' :
      (realToComplexLp lam (complexLpIm lam f)) x =
        ((complexLpIm lam f) x : ℂ) := by
    simpa only [realToComplexLp, Complex.ofRealCLM_apply] using hincIm
  have hre' : (complexLpRe lam f) x = (f x).re := by
    simpa only [complexLpRe, Complex.reCLM_apply] using hre
  have him' : (complexLpIm lam f) x = (f x).im := by
    simpa only [complexLpIm, Complex.imCLM_apply] using him
  calc
    (realToComplexLp lam (complexLpRe lam f) +
      Complex.I • realToComplexLp lam (complexLpIm lam f)) x =
        (realToComplexLp lam (complexLpRe lam f)) x +
          Complex.I * (realToComplexLp lam (complexLpIm lam f)) x := by
            rw [hadd', hsm]
            rfl
    _ = ((complexLpRe lam f) x : ℂ) +
          Complex.I * ((complexLpIm lam f) x : ℂ) := by
            rw [hincRe', hincIm']
    _ = ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ) := by
            rw [hre', him']
    _ = f x := by
            simpa only [mul_comm] using (Complex.re_add_im (f x))

#print axioms GegenbauerFock.Ultraspherical.complexLpRe_realToComplexLp
#print axioms GegenbauerFock.Ultraspherical.complexLpIm_realToComplexLp
#print axioms GegenbauerFock.Ultraspherical.complexLp_eq_realToComplex_re_add_I_im

end GegenbauerFock.Ultraspherical
