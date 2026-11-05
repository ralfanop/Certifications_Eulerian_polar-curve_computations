import GegenbauerFock.UltrasphericalSturmLiouvilleActualComplexHeatFullC0

/-!
# V007 — complex heat commutes with actual real/imaginary L² projections

For the GENUINE COMPLEX-linear weighted-L² Gegenbauer heat semigroup,
the bounded REAL-linear projections Re and Im send its action to
the corresponding action of the GENUINE REAL Sturm heat.

These identities are on ALL complex weighted-L² vectors. By bounded
real linearity of both projections, they also hold on the entire
right-difference quotient. They prepare the converse inclusion in
the exact complex generator domain graph, without using a surrogate
diagonal model or the unrelated complex Fock Gram.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev HR (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev HC (lam : ℝ) := Lp ℂ 2 (measure lam)

/-- Actual real-part projection commutes with the genuine complex
Gegenbauer heat semigroup for all nonnegative times. -/
theorem sturmActualComplexHeatCLM_re
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s) (f : HC lam) :
    complexLpRe lam (sturmActualComplexHeatCLM lam hlam s hs f) =
      sturmRealHeatLimitCLM lam hlam s hs (complexLpRe lam f) := by
  rw [sturmActualComplexHeatCLM_apply_re_im,
    map_add, complexLpRe_realToComplexLp,
    complexLpRe_I_smul, complexLpIm_realToComplexLp]
  simp

/-- Actual imaginary-part projection commutes with the genuine
complex Gegenbauer heat semigroup for nonnegative times. -/
theorem sturmActualComplexHeatCLM_im
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s) (f : HC lam) :
    complexLpIm lam (sturmActualComplexHeatCLM lam hlam s hs f) =
      sturmRealHeatLimitCLM lam hlam s hs (complexLpIm lam f) := by
  rw [sturmActualComplexHeatCLM_apply_re_im,
    map_add, complexLpIm_realToComplexLp,
    complexLpIm_I_smul, complexLpRe_realToComplexLp]
  simp

/-- Real-part projection intertwines actual-complex and actual-real
heat on the full real-time nonnegative extension. -/
theorem sturmActualComplexHeatNonnegativeExtended_re
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (f : HC lam) :
    complexLpRe lam
        (sturmActualComplexHeatNonnegativeExtended lam hlam s f) =
      sturmRealHeatLimitNonnegativeExtended lam hlam s
        (complexLpRe lam f) := by
  exact sturmActualComplexHeatCLM_re lam hlam
    (max (0 : ℝ) s) (le_max_left (0 : ℝ) s) f

/-- Imaginary-part projection intertwines actual-complex and actual-real
heat on the full real-time nonnegative extension. -/
theorem sturmActualComplexHeatNonnegativeExtended_im
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (f : HC lam) :
    complexLpIm lam
        (sturmActualComplexHeatNonnegativeExtended lam hlam s f) =
      sturmRealHeatLimitNonnegativeExtended lam hlam s
        (complexLpIm lam f) := by
  exact sturmActualComplexHeatCLM_im lam hlam
    (max (0 : ℝ) s) (le_max_left (0 : ℝ) s) f

/-- Real projection of a genuine complex Sturm heat right difference
quotient equals the corresponding genuine real difference quotient. -/
theorem sturmActualComplexHeat_differenceQuotient_re
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (f : HC lam) :
    complexLpRe lam
      (s⁻¹ •
        (sturmActualComplexHeatNonnegativeExtended lam hlam s f - f)) =
      s⁻¹ •
        (sturmRealHeatLimitNonnegativeExtended lam hlam s
            (complexLpRe lam f) - complexLpRe lam f) := by
  rw [map_smul, map_sub,
    sturmActualComplexHeatNonnegativeExtended_re]

/-- Imaginary projection of a genuine complex Sturm heat right
difference quotient equals its actual real counterpart. -/
theorem sturmActualComplexHeat_differenceQuotient_im
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (f : HC lam) :
    complexLpIm lam
      (s⁻¹ •
        (sturmActualComplexHeatNonnegativeExtended lam hlam s f - f)) =
      s⁻¹ •
        (sturmRealHeatLimitNonnegativeExtended lam hlam s
            (complexLpIm lam f) - complexLpIm lam f) := by
  rw [map_smul, map_sub,
    sturmActualComplexHeatNonnegativeExtended_im]

#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeatCLM_re
#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeatCLM_im
#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeat_differenceQuotient_re
#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeat_differenceQuotient_im

end GegenbauerFock.Ultraspherical
