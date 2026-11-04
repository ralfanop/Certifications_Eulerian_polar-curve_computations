import GegenbauerFock.UltrasphericalSturmLiouvilleActualComplexHeatFullC0
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatGeneratorClosedDomainForward

/-!
# V007 — generator of actual complex Sturm heat on the embedded closed REAL domain

For every vector in the canonical closed-domain of the REAL
Gegenbauer Sturm differential operator, Lean already proves that the
true real heat right difference quotient converges to A x in actual
real weighted L² (not merely on eigenpolynomials).

The present module transfers this differentiation through the
actual bounded isometric real-to-complex inclusion J, using the
already verified genuine complex semigroup relation H^C_s J=J H^R_s.

This gives the concrete generator equation on the EMBEDDED REAL
CLOSED DOMAIN, and is the first graph inclusion needed to identify
the full generator of the complexified Sturm heat.

It explicitly does NOT assert the converse/full complex generator
domain equality or identification with the unrelated Fock Gram.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev HR (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev HC (lam : ℝ) := Lp ℂ 2 (measure lam)

/-- The ACTUAL complex heat semigroup generator differentiates exactly
to the real Sturm closure embedded into complex weighted L², for
every real L² vector in the genuine canonical closed Sturm domain. -/
theorem sturmActualComplexHeat_embedded_closedSturm_right_derivative
    (lam : ℝ) (hlam : 0 < lam)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    Tendsto
      (fun s : ℝ =>
        s⁻¹ •
          (sturmActualComplexHeatNonnegativeExtended lam hlam s
              (realToComplexLp lam (x : HR lam)) -
            realToComplexLp lam (x : HR lam)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (realToComplexLp lam
        ((sturmRealPartialOperator lam hlam).closure x))) := by
  let A := (sturmRealPartialOperator lam hlam).closure
  have hReal :
      Tendsto
        (fun s : ℝ =>
          s⁻¹ • (sturmRealHeatLimitNonnegativeExtended lam hlam s
            (x : HR lam) - (x : HR lam)))
        (𝓝[>] (0 : ℝ)) (𝓝 (A x)) :=
    sturmRealHeatLimit_closed_sturm_right_derivative lam hlam x
  have hMapped :
      Tendsto
        (fun s : ℝ =>
          realToComplexLp lam
            (s⁻¹ • (sturmRealHeatLimitNonnegativeExtended lam hlam s
              (x : HR lam) - (x : HR lam))))
        (𝓝[>] (0 : ℝ))
        (𝓝 (realToComplexLp lam (A x))) :=
    ((realToComplexLp lam).continuous.tendsto (A x)).comp hReal
  have hAction (s : ℝ) :
      sturmActualComplexHeatNonnegativeExtended lam hlam s
          (realToComplexLp lam (x : HR lam)) =
        realToComplexLp lam
          (sturmRealHeatLimitNonnegativeExtended lam hlam s
            (x : HR lam)) := by
    simpa only [sturmActualComplexHeatNonnegativeExtended,
      sturmRealHeatLimitNonnegativeExtended] using
        sturmActualComplexHeatCLM_embedded_real
          lam hlam (max (0 : ℝ) s)
          (le_max_left (0 : ℝ) s) (x : HR lam)
  have hfun :
      (fun s : ℝ =>
        s⁻¹ •
          (sturmActualComplexHeatNonnegativeExtended lam hlam s
              (realToComplexLp lam (x : HR lam)) -
            realToComplexLp lam (x : HR lam))) =
      (fun s : ℝ =>
        realToComplexLp lam
          (s⁻¹ • (sturmRealHeatLimitNonnegativeExtended lam hlam s
            (x : HR lam) - (x : HR lam)))) := by
    funext s
    calc
      s⁻¹ •
          (sturmActualComplexHeatNonnegativeExtended lam hlam s
              (realToComplexLp lam (x : HR lam)) -
            realToComplexLp lam (x : HR lam)) =
        s⁻¹ •
          (realToComplexLp lam
            (sturmRealHeatLimitNonnegativeExtended lam hlam s
              (x : HR lam)) -
          realToComplexLp lam (x : HR lam)) := by
            rw [hAction s]
      _ = s⁻¹ • realToComplexLp lam
          (sturmRealHeatLimitNonnegativeExtended lam hlam s
            (x : HR lam) - (x : HR lam)) := by
            rw [map_sub]
      _ = realToComplexLp lam
          (s⁻¹ • (sturmRealHeatLimitNonnegativeExtended lam hlam s
            (x : HR lam) - (x : HR lam))) := by
            rw [map_smul]
  rw [hfun]
  exact hMapped

#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeat_embedded_closedSturm_right_derivative

end GegenbauerFock.Ultraspherical
