import GegenbauerFock.UltrasphericalSturmLiouvilleActualComplexHeatGeneratorComplexCore
import GegenbauerFock.UltrasphericalSturmLiouvilleActualComplexHeatGeneratorProjection
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatGeneratorExactGraph

/-!
# V007 — COMPLETE complex heat generator = complexification of true closed Sturm

For lambda>0, let H^C_s be the GENUINE complex-linear strongly continuous
Sturm heat semigroup on actual L²(nu_lambda;C). Let A^R be the canonical
closure of the original REAL Gegenbauer polynomial differential operator
in the actual real weighted L²(nu_lambda;R).

The real-to-complex inclusion J and real/imaginary projections have
already been kernel checked on actual L² spaces. They split each complex
vector as J(Re f)+I J(Im f), and the actual complex heat and its right
difference quotient commute with both projections.

This module proves the FULL graph identity, INCLUDING THE DOMAIN:

   generator(H^C)
      = { (Jx+I Jy, J(A^R x)+I J(A^R y)) :
           x,y in Dom(A^R) }.

Forward direction: real/imaginary projection of any genuine complex
strong right derivative, followed by the previously verified REAL
exact graph equality, reconstructs BOTH closed Sturm domain vectors.

Reverse direction: certified complex heat strong right derivative on
the entire complexified real closed Sturm core.

No auxiliary diagonal realization, fictitious Gram identification or
unjustified equivalence of complex and real Schatten classes is used.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev HR (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev HC (lam : ℝ) := Lp ℂ 2 (measure lam)

/-- The generator of the ACTUAL complex Sturm heat semigroup has
EXACTLY the natural complexified domain of the canonical closed
real Gegenbauer Sturm differential operator, including the complete
right-derivative graph, not merely a graph inclusion or eigenmode core. -/
theorem sturmActualComplexHeat_generator_exact_closedComplexSturm_graph
    (lam : ℝ) (hlam : 0 < lam) (f g : HC lam) :
    Tendsto
      (fun s : ℝ =>
        s⁻¹ •
          (sturmActualComplexHeatNonnegativeExtended lam hlam s f - f))
      (𝓝[>] (0 : ℝ)) (𝓝 g) ↔
    ∃ x y : (sturmRealPartialOperator lam hlam).closure.domain,
      f = realToComplexLp lam (x : HR lam) +
            Complex.I • realToComplexLp lam (y : HR lam) ∧
      g = realToComplexLp lam
            ((sturmRealPartialOperator lam hlam).closure x) +
          Complex.I • realToComplexLp lam
            ((sturmRealPartialOperator lam hlam).closure y) := by
  constructor
  · intro h
    have hReProjection :
        Tendsto
          (fun s : ℝ =>
            complexLpRe lam
              (s⁻¹ •
                (sturmActualComplexHeatNonnegativeExtended lam hlam s f - f)))
          (𝓝[>] (0 : ℝ)) (𝓝 (complexLpRe lam g)) :=
      ((complexLpRe lam).continuous.tendsto g).comp h
    have hImProjection :
        Tendsto
          (fun s : ℝ =>
            complexLpIm lam
              (s⁻¹ •
                (sturmActualComplexHeatNonnegativeExtended lam hlam s f - f)))
          (𝓝[>] (0 : ℝ)) (𝓝 (complexLpIm lam g)) :=
      ((complexLpIm lam).continuous.tendsto g).comp h
    have hReFunction :
        (fun s : ℝ =>
          complexLpRe lam
            (s⁻¹ •
              (sturmActualComplexHeatNonnegativeExtended lam hlam s f - f))) =
        (fun s : ℝ =>
          s⁻¹ •
            (sturmRealHeatLimitNonnegativeExtended lam hlam s
              (complexLpRe lam f) - complexLpRe lam f)) := by
      funext s
      exact sturmActualComplexHeat_differenceQuotient_re lam hlam s f
    have hImFunction :
        (fun s : ℝ =>
          complexLpIm lam
            (s⁻¹ •
              (sturmActualComplexHeatNonnegativeExtended lam hlam s f - f))) =
        (fun s : ℝ =>
          s⁻¹ •
            (sturmRealHeatLimitNonnegativeExtended lam hlam s
              (complexLpIm lam f) - complexLpIm lam f)) := by
      funext s
      exact sturmActualComplexHeat_differenceQuotient_im lam hlam s f
    rw [hReFunction] at hReProjection
    rw [hImFunction] at hImProjection
    obtain ⟨x, hx, hAx⟩ :=
      (sturmRealHeatLimit_generator_exact_closedSturm_graph
        lam hlam (complexLpRe lam f) (complexLpRe lam g)).mp
        hReProjection
    obtain ⟨y, hy, hAy⟩ :=
      (sturmRealHeatLimit_generator_exact_closedSturm_graph
        lam hlam (complexLpIm lam f) (complexLpIm lam g)).mp
        hImProjection
    refine ⟨x, y, ?_, ?_⟩
    · calc
        f = realToComplexLp lam (complexLpRe lam f) +
              Complex.I • realToComplexLp lam (complexLpIm lam f) :=
          (complexLp_eq_realToComplex_re_add_I_im lam f).symm
        _ = realToComplexLp lam (x : HR lam) +
              Complex.I • realToComplexLp lam (y : HR lam) := by
            rw [← hx, ← hy]
    · calc
        g = realToComplexLp lam (complexLpRe lam g) +
              Complex.I • realToComplexLp lam (complexLpIm lam g) :=
          (complexLp_eq_realToComplex_re_add_I_im lam g).symm
        _ = realToComplexLp lam
              ((sturmRealPartialOperator lam hlam).closure x) +
            Complex.I • realToComplexLp lam
              ((sturmRealPartialOperator lam hlam).closure y) := by
            rw [← hAx, ← hAy]
  · rintro ⟨x, y, hf, hg⟩
    subst f
    subst g
    exact sturmActualComplexHeat_complexified_closedSturm_right_derivative
      lam hlam x y

/-- Equality of the COMPLETE generator graphs as explicit SETS of
complex weighted-L² input/output pairs. Includes equality of the
domains; the real closure is the original actual polynomial
Gegenbauer Sturm operator's graph closure. -/
theorem sturmActualComplexHeat_generator_graph_set_eq_closedComplexSturm
    (lam : ℝ) (hlam : 0 < lam) :
    { p : HC lam × HC lam |
      Tendsto
        (fun s : ℝ =>
          s⁻¹ •
            (sturmActualComplexHeatNonnegativeExtended lam hlam s p.1 - p.1))
        (𝓝[>] (0 : ℝ)) (𝓝 p.2) } =
    { p : HC lam × HC lam |
      ∃ x y : (sturmRealPartialOperator lam hlam).closure.domain,
        p.1 = realToComplexLp lam (x : HR lam) +
          Complex.I • realToComplexLp lam (y : HR lam) ∧
        p.2 = realToComplexLp lam
          ((sturmRealPartialOperator lam hlam).closure x) +
          Complex.I • realToComplexLp lam
            ((sturmRealPartialOperator lam hlam).closure y) } := by
  ext p
  exact sturmActualComplexHeat_generator_exact_closedComplexSturm_graph
    lam hlam p.1 p.2

#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeat_generator_exact_closedComplexSturm_graph
#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeat_generator_graph_set_eq_closedComplexSturm

end GegenbauerFock.Ultraspherical
