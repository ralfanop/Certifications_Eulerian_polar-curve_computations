import GegenbauerFock.UltrasphericalSturmLiouvilleActualComplexHeatRealExtension

/-!
# V007 — genuine COMPLEX-linear Gegenbauer Sturm heat on actual complex weighted L2

Start with the kernel-checkable real-linear extension on ACTUAL complex
L2, obtained by applying the canonical real Sturm heat separately to
real and imaginary components. We prove it COMMUTES with multiplication
by I using the genuine L2 projection maps; this upgrades it to an
honest bounded COMPLEX-linear operator on the full complex weighted L2.

The final operator agrees with the original real heat after real-to-
complex inclusion on every real L2 function. This is the actual
complexification of the real Sturm semigroup (at each nonnegative time),
and is NOT the Gegenbauer--Fock Gram C^*C.

No complex spectrum or CFC class membership is asserted by this module:
these are separate consequences to be certified using the diagonal
Gegenbauer spectral theory if required.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev HR (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev HC (lam : ℝ) := Lp ℂ 2 (measure lam)

/-- Actual real part under multiplication by I. -/
theorem complexLpRe_I_smul (lam : ℝ) (f : HC lam) :
    complexLpRe lam (Complex.I • f) = -complexLpIm lam f := by
  ext1
  filter_upwards [
    Complex.reCLM.coeFn_compLpL (Complex.I • f),
    Lp.coeFn_smul Complex.I f,
    Complex.imCLM.coeFn_compLpL f,
    Lp.coeFn_neg (complexLpIm lam f)
  ] with x hre hmul him hneg
  calc
    (complexLpRe lam (Complex.I • f)) x =
        Complex.reCLM ((Complex.I • f) x) := hre
    _ = (Complex.I * f x).re := by rw [hmul]; rfl
    _ = -(f x).im := Complex.I_mul_re (f x)
    _ = -(complexLpIm lam f) x := by rw [him]; rfl
    _ = (-complexLpIm lam f) x := hneg.symm

/-- Actual imaginary part under multiplication by I. -/
theorem complexLpIm_I_smul (lam : ℝ) (f : HC lam) :
    complexLpIm lam (Complex.I • f) = complexLpRe lam f := by
  ext1
  filter_upwards [
    Complex.imCLM.coeFn_compLpL (Complex.I • f),
    Lp.coeFn_smul Complex.I f,
    Complex.reCLM.coeFn_compLpL f
  ] with x him hmul hre
  calc
    (complexLpIm lam (Complex.I • f)) x =
        Complex.imCLM ((Complex.I • f) x) := him
    _ = (Complex.I * f x).im := by rw [hmul]; rfl
    _ = (f x).re := Complex.I_mul_im (f x)
    _ = (complexLpRe lam f) x := hre.symm

/-- The genuine real-linear heat extension COMMUTES with I on every
complex weighted-L2 vector, not merely on embedded real vectors. -/
theorem sturmActualComplexHeatRealCLM_I_smul
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s)
    (f : HC lam) :
    sturmActualComplexHeatRealCLM lam hlam s hs (Complex.I • f) =
      Complex.I • sturmActualComplexHeatRealCLM lam hlam s hs f := by
  simp only [sturmActualComplexHeatRealCLM,
    ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,
    complexLpRe_I_smul, complexLpIm_I_smul,
    map_neg, smul_add, smul_smul, Complex.I_mul_I,
    neg_one_smul] <;> abel

/-- The actual COMPLEX-linear Sturm heat endomorphism on genuine
L²(nu_lambda;C), obtained from the real operator by exact complexification.
The boundedness is inherited from the actual bounded real extension. -/
noncomputable def sturmActualComplexHeatCLM
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s) :
    HC lam →L[ℂ] HC lam where
  toFun := sturmActualComplexHeatRealCLM lam hlam s hs
  map_add' f g := (sturmActualComplexHeatRealCLM lam hlam s hs).map_add f g
  map_smul' z f := by
    let T := sturmActualComplexHeatRealCLM lam hlam s hs
    have hI (x : HC lam) : T (Complex.I • x) = Complex.I • T x :=
      sturmActualComplexHeatRealCLM_I_smul lam hlam s hs x
    have hreal (r : ℝ) (x : HC lam) :
        T ((r : ℂ) • x) = (r : ℂ) • T x := by
      calc
        T ((r : ℂ) • x) = T (r • x) := by
          rw [IsScalarTower.algebraMap_smul ℂ r x]
        _ = r • T x := T.map_smul r x
        _ = (r : ℂ) • T x :=
          (IsScalarTower.algebraMap_smul ℂ r (T x)).symm
    change T (z • f) = z • T f
    calc
      T (z • f) =
          T (((z.re : ℂ) + (z.im : ℂ) * Complex.I) • f) := by
            rw [Complex.re_add_im]
      _ = T ((z.re : ℂ) • f + (z.im : ℂ) • (Complex.I • f)) := by
            rw [add_smul, mul_smul]
      _ = T ((z.re : ℂ) • f) +
            T ((z.im : ℂ) • (Complex.I • f)) := by rw [map_add]
      _ = (z.re : ℂ) • T f +
            (z.im : ℂ) • T (Complex.I • f) := by
              rw [hreal, hreal]
      _ = (z.re : ℂ) • T f +
            (z.im : ℂ) • (Complex.I • T f) := by rw [hI]
      _ = (((z.re : ℂ) + (z.im : ℂ) * Complex.I) • T f) := by
            rw [add_smul, mul_smul]
      _ = z • T f := by rw [Complex.re_add_im]
  cont := (sturmActualComplexHeatRealCLM lam hlam s hs).continuous

/-- The COMPLEX-linear actual Sturm semigroup commutes exactly with
the canonical real inclusion for every positive Sturm parameter and
every nonnegative heat time. -/
theorem sturmActualComplexHeatCLM_embedded_real
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s)
    (f : HR lam) :
    sturmActualComplexHeatCLM lam hlam s hs
        (realToComplexLp lam f) =
      realToComplexLp lam
        (sturmRealHeatLimitCLM lam hlam s hs f) :=
  sturmActualComplexHeatRealCLM_embedded_real lam hlam s hs f

#print axioms GegenbauerFock.Ultraspherical.complexLpRe_I_smul
#print axioms GegenbauerFock.Ultraspherical.complexLpIm_I_smul
#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeatRealCLM_I_smul
#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeatCLM_embedded_real

end GegenbauerFock.Ultraspherical
