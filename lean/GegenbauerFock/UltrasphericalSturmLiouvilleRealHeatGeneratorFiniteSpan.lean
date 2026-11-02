import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatFiniteSpanDerivative

/-!
# V007 — infinitesimal heat generator on the finite Gegenbauer core

Compatibility theorem with the independently formalized finite
spectral-span derivative. Both spectral-sum vectors and their full-L²
right-slope limits are constructed in the imported certified module;
this statement retains the original theorem name for downstream use.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Right infinitesimal generator action of the actual heat contraction
semigroup on every finite normalized Gegenbauer combination. -/
theorem sturmRealHeatLimit_generator_on_finite_Gegenbauer
    (lam : ℝ) (hlam : 0 < lam) (F : Finset ℕ) (a : ℕ → ℝ) :
    Tendsto
      (fun h : ℝ => h⁻¹ •
        (sturmRealHeatLimitNonnegativeExtended lam hlam h
          (sturmRealGegenbauerFiniteVector lam hlam F a) -
         sturmRealGegenbauerFiniteVector lam hlam F a))
      (𝓝[>] (0 : ℝ))
      (𝓝 (sturmRealGegenbauerFiniteGeneratorVector lam hlam F a)) := by
  exact sturmRealHeatLimit_finiteGegenbauer_right_slope lam hlam F a

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimit_generator_on_finite_Gegenbauer

end GegenbauerFock.Ultraspherical
