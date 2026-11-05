import GegenbauerFock.UltrasphericalSturmLiouvilleActualComplexLpDecomposition

/-!
# V007 — actual complex-valued L² extension of the real Gegenbauer heat

This constructs a bounded real-linear operator on the GENUINE complex
weighted L² as an explicit action on real and imaginary parts of each
vector, and proves the original real heat embeds equivariantly.

The operator is currently typed as REAL-linear. To call it the
canonical COMPLEX-linear heat semigroup, a further proof of
commutation with multiplication by I and full complex linearity is
required. This intermediate certificate does not silently assume
complex linearity or equate the semigroup with the Fock Gram.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev HR (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev HC (lam : ℝ) := Lp ℂ 2 (measure lam)

/-- Bounded real-linear extension to actual complex L² obtained by
applying the original real heat separately to real and imaginary parts. -/
noncomputable def sturmActualComplexHeatRealCLM
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s) :
    HC lam →L[ℝ] HC lam :=
  ((realToComplexLp lam).comp
     ((sturmRealHeatLimitCLM lam hlam s hs).comp (complexLpRe lam))) +
  Complex.I •
    ((realToComplexLp lam).comp
      ((sturmRealHeatLimitCLM lam hlam s hs).comp (complexLpIm lam)))

/-- On the canonical embedded real weighted L², the constructed
complex-valued heat action is EXACTLY the original real heat.
The equality is in the genuine complex L², not merely a formula
for formal Fourier coefficients. -/
theorem sturmActualComplexHeatRealCLM_embedded_real
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s)
    (f : HR lam) :
    sturmActualComplexHeatRealCLM lam hlam s hs
        (realToComplexLp lam f) =
      realToComplexLp lam
        (sturmRealHeatLimitCLM lam hlam s hs f) := by
  simp only [sturmActualComplexHeatRealCLM,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,
    complexLpRe_realToComplexLp, complexLpIm_realToComplexLp,
    map_zero, smul_zero, add_zero]

/-- The real component of the extended heat on an embedded real vector
is exactly the genuine original heat. -/
theorem sturmActualComplexHeatRealCLM_embedded_real_part
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s)
    (f : HR lam) :
    complexLpRe lam
      (sturmActualComplexHeatRealCLM lam hlam s hs
        (realToComplexLp lam f)) =
      sturmRealHeatLimitCLM lam hlam s hs f := by
  rw [sturmActualComplexHeatRealCLM_embedded_real]
  exact complexLpRe_realToComplexLp lam _

#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeatRealCLM_embedded_real
#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeatRealCLM_embedded_real_part

end GegenbauerFock.Ultraspherical
