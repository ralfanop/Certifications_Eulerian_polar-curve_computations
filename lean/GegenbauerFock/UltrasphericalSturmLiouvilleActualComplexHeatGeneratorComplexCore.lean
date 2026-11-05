import GegenbauerFock.UltrasphericalSturmLiouvilleActualComplexHeatGeneratorRealCore

/-!
# V007 — generator of the actual complex Sturm heat on its natural complexified closed core

The true complex-valued Gegenbauer C₀ heat semigroup H^C_s is a
bounded COMPLEX-linear operator on the GENUINE L²(nu_lambda;C).
Its generator on the image J of the canonical real closed Sturm domain
has a separately checked real-core right-derivative formula.

By genuine complex linearity, the derivative formula extends to
every complex combination J(x)+I J(y), where x and y belong to
the actual canonical closed real Sturm domain. It equals
J(Ax)+I J(Ay) with A the true closed Sturm differential operator.

This is a full COMPLEX-LINEAR CLOSED-CORE graph inclusion, but NOT YET
a proof of the converse or of the complete complex generator domain.
The Fock Gram is independent and is not identified with H^C.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev HR (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev HC (lam : ℝ) := Lp ℂ 2 (measure lam)

/-- On EVERY complexified pair from the ACTUAL real closed Sturm
domain, the true complex semigroup has the strong right derivative
J(Ax)+I J(Ay) at time zero. -/
theorem sturmActualComplexHeat_complexified_closedSturm_right_derivative
    (lam : ℝ) (hlam : 0 < lam)
    (x y : (sturmRealPartialOperator lam hlam).closure.domain) :
    Tendsto
      (fun s : ℝ =>
        s⁻¹ •
          (sturmActualComplexHeatNonnegativeExtended lam hlam s
              (realToComplexLp lam (x : HR lam) +
                Complex.I • realToComplexLp lam (y : HR lam)) -
            (realToComplexLp lam (x : HR lam) +
              Complex.I • realToComplexLp lam (y : HR lam))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (realToComplexLp lam
          ((sturmRealPartialOperator lam hlam).closure x) +
        Complex.I • realToComplexLp lam
          ((sturmRealPartialOperator lam hlam).closure y))) := by
  have hx :=
    sturmActualComplexHeat_embedded_closedSturm_right_derivative
      lam hlam x
  have hy :=
    sturmActualComplexHeat_embedded_closedSturm_right_derivative
      lam hlam y
  have hSum := hx.add (hy.const_smul Complex.I)
  have hfun :
      (fun s : ℝ =>
        s⁻¹ •
          (sturmActualComplexHeatNonnegativeExtended lam hlam s
              (realToComplexLp lam (x : HR lam) +
                Complex.I • realToComplexLp lam (y : HR lam)) -
            (realToComplexLp lam (x : HR lam) +
              Complex.I • realToComplexLp lam (y : HR lam)))) =
      (fun s : ℝ =>
        s⁻¹ •
          (sturmActualComplexHeatNonnegativeExtended lam hlam s
            (realToComplexLp lam (x : HR lam)) -
            realToComplexLp lam (x : HR lam)) +
        Complex.I •
          (s⁻¹ •
            (sturmActualComplexHeatNonnegativeExtended lam hlam s
                (realToComplexLp lam (y : HR lam)) -
              realToComplexLp lam (y : HR lam)))) := by
    funext s
    let T := sturmActualComplexHeatNonnegativeExtended lam hlam s
    let a := realToComplexLp lam (x : HR lam)
    let b := realToComplexLp lam (y : HR lam)
    change
      s⁻¹ • (T (a + Complex.I • b) - (a + Complex.I • b)) =
        s⁻¹ • (T a - a) + Complex.I • (s⁻¹ • (T b - b))
    calc
      s⁻¹ • (T (a + Complex.I • b) - (a + Complex.I • b)) =
          s⁻¹ • ((T a - a) + Complex.I • (T b - b)) := by
            rw [map_add, map_smul, smul_sub]
            congr 1
            abel
      _ = s⁻¹ • (T a - a) +
          Complex.I • (s⁻¹ • (T b - b)) := by
            rw [smul_add]
            congr 1
            exact smul_comm (s⁻¹) Complex.I (T b - b)
  rw [hfun]
  exact hSum

#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeat_complexified_closedSturm_right_derivative

end GegenbauerFock.Ultraspherical
