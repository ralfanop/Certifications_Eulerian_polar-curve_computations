import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaEuler
import Mathlib.Analysis.Normed.Ring.Basic

/-!
# V007 — uniformly contractive finite Euler products for ultraspherical Sturm

The bounded Yosida generator of the actual closed Sturm differential
operator admits Euler steps I+h A_t that are contractions for 0 ≤ ht ≤ 1.
Every finite Euler product of those steps is therefore contractive in
the operator norm on the genuine real weighted L² Hilbert space.

This proves stable finite approximants for subsequent semigroup
construction, without identifying them with an already existing C₀
semigroup or asserting convergence of the Euler products.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Finite Euler product of the bounded Yosida generator. -/
noncomputable def sturmRealYosidaEulerIterate
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (h : ℝ) (n : ℕ) :
    SturmH lam →L[ℝ] SturmH lam :=
  (sturmRealYosidaEulerStep lam t hlam ht h) ^ n

/-- Every finite Euler product has operator norm at most one
under the explicit CFL stability restriction h*t ≤ 1. -/
theorem sturmRealYosidaEulerIterate_opNorm_le
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (h : ℝ) (hh : 0 ≤ h) (hsmall : h * t ≤ 1)
    (n : ℕ) :
    ‖sturmRealYosidaEulerIterate lam t hlam ht h n‖ ≤ 1 := by
  change ‖(sturmRealYosidaEulerStep lam t hlam ht h) ^ n‖ ≤ 1
  calc
    ‖(sturmRealYosidaEulerStep lam t hlam ht h) ^ n‖ ≤
        ‖sturmRealYosidaEulerStep lam t hlam ht h‖ ^ n :=
      norm_pow_le _ n
    _ ≤ 1 := pow_le_one₀ (norm_nonneg _)
      (sturmRealYosidaEulerStep_opNorm_le lam t hlam ht h hh hsmall)

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaEulerIterate_opNorm_le

end GegenbauerFock.Ultraspherical
