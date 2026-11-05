import GegenbauerFock.UltrasphericalSturmLiouvilleActualComplexHeatCLM
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitSemigroupLaw

/-!
# V007 — canonical complex Gegenbauer heat satisfies the exact C₀-semigroup algebra

This module upgrades the already kernel-certified complex-linear
extension of the genuine real weighted L² Sturm heat to exact
operator-level identities:

  complex H_0 = 1,
  complex H_(s+t) = complex H_s * complex H_t,  s,t ≥ 0.

The proof works on the whole ACTUAL complex weighted L²: every
complex vector is the sum of its embedded real and imaginary parts,
and the genuine COMPLEX-linear heat acts on both via the original
real Gegenbauer semigroup. No auxiliary diagonal model is used.

This module proves the SEMIGROUP LAWS. It does not, by itself, assert
the strongly continuous C₀ property, complex-domain generator
identity, CFC trace class or relation to the distinct Fock Gram.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev HR (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev HC (lam : ℝ) := Lp ℂ 2 (measure lam)

/-- Exact formula on each vector of the genuine COMPLEX weighted L²:
the complex semigroup acts on the actual real and imaginary L²
components by the real heat semigroup, then recombines them. -/
theorem sturmActualComplexHeatCLM_apply_re_im
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s)
    (f : HC lam) :
    sturmActualComplexHeatCLM lam hlam s hs f =
      realToComplexLp lam
        (sturmRealHeatLimitCLM lam hlam s hs (complexLpRe lam f)) +
      Complex.I • realToComplexLp lam
        (sturmRealHeatLimitCLM lam hlam s hs (complexLpIm lam f)) := by
  calc
    sturmActualComplexHeatCLM lam hlam s hs f =
        sturmActualComplexHeatCLM lam hlam s hs
          (realToComplexLp lam (complexLpRe lam f) +
            Complex.I • realToComplexLp lam (complexLpIm lam f)) := by
              rw [complexLp_eq_realToComplex_re_add_I_im]
    _ = realToComplexLp lam
          (sturmRealHeatLimitCLM lam hlam s hs (complexLpRe lam f)) +
        Complex.I • realToComplexLp lam
          (sturmRealHeatLimitCLM lam hlam s hs (complexLpIm lam f)) := by
            rw [map_add, map_smul,
              sturmActualComplexHeatCLM_embedded_real,
              sturmActualComplexHeatCLM_embedded_real]

/-- At time zero, the genuine complex Sturm heat is the identity
on ALL complex-valued Gegenbauer-weighted L² vectors. -/
theorem sturmActualComplexHeatCLM_zero
    (lam : ℝ) (hlam : 0 < lam) :
    sturmActualComplexHeatCLM lam hlam 0 le_rfl =
      (1 : HC lam →L[ℂ] HC lam) := by
  apply ContinuousLinearMap.ext
  intro f
  calc
    sturmActualComplexHeatCLM lam hlam 0 le_rfl f =
        realToComplexLp lam
          (sturmRealHeatLimitCLM lam hlam 0 le_rfl (complexLpRe lam f)) +
        Complex.I • realToComplexLp lam
          (sturmRealHeatLimitCLM lam hlam 0 le_rfl (complexLpIm lam f)) :=
      sturmActualComplexHeatCLM_apply_re_im lam hlam 0 le_rfl f
    _ = realToComplexLp lam (complexLpRe lam f) +
          Complex.I • realToComplexLp lam (complexLpIm lam f) := by
            rw [sturmRealHeatLimitCLM_zero lam hlam]
            simp
    _ = f := complexLp_eq_realToComplex_re_add_I_im lam f
    _ = (1 : HC lam →L[ℂ] HC lam) f := by simp

/-- Exact semigroup law of the GENUINE complex-linear Sturm heat CLM:
H_(s+t) = H_s H_t on ALL of the actual complex weighted L².
This transports the previously certified REAL semigroup identity
using the exact actual-L² re/im decomposition and true complex
linearity; there is no assumed complex Gram correspondence. -/
theorem sturmActualComplexHeatCLM_add
    (lam : ℝ) (hlam : 0 < lam)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    sturmActualComplexHeatCLM lam hlam (s + t) (add_nonneg hs ht) =
      sturmActualComplexHeatCLM lam hlam s hs *
        sturmActualComplexHeatCLM lam hlam t ht := by
  apply ContinuousLinearMap.ext
  intro f
  have htAction :=
    sturmActualComplexHeatCLM_apply_re_im lam hlam t ht f
  calc
    sturmActualComplexHeatCLM lam hlam (s + t) (add_nonneg hs ht) f =
        realToComplexLp lam
          (sturmRealHeatLimitCLM lam hlam (s + t) (add_nonneg hs ht)
            (complexLpRe lam f)) +
        Complex.I • realToComplexLp lam
          (sturmRealHeatLimitCLM lam hlam (s + t) (add_nonneg hs ht)
            (complexLpIm lam f)) :=
      sturmActualComplexHeatCLM_apply_re_im lam hlam
        (s + t) (add_nonneg hs ht) f
    _ = realToComplexLp lam
          (sturmRealHeatLimitCLM lam hlam s hs
            (sturmRealHeatLimitCLM lam hlam t ht (complexLpRe lam f))) +
        Complex.I • realToComplexLp lam
          (sturmRealHeatLimitCLM lam hlam s hs
            (sturmRealHeatLimitCLM lam hlam t ht (complexLpIm lam f))) := by
              rw [sturmRealHeatLimitCLM_add lam hlam s t hs ht]
              simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    _ = sturmActualComplexHeatCLM lam hlam s hs
          (realToComplexLp lam
            (sturmRealHeatLimitCLM lam hlam t ht (complexLpRe lam f)) +
            Complex.I • realToComplexLp lam
              (sturmRealHeatLimitCLM lam hlam t ht (complexLpIm lam f))) := by
              rw [map_add, map_smul,
                sturmActualComplexHeatCLM_embedded_real,
                sturmActualComplexHeatCLM_embedded_real]
    _ = sturmActualComplexHeatCLM lam hlam s hs
          (sturmActualComplexHeatCLM lam hlam t ht f) :=
        congrArg (sturmActualComplexHeatCLM lam hlam s hs) htAction.symm
    _ = (sturmActualComplexHeatCLM lam hlam s hs *
          sturmActualComplexHeatCLM lam hlam t ht) f := rfl

#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeatCLM_apply_re_im
#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeatCLM_zero
#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeatCLM_add

end GegenbauerFock.Ultraspherical
