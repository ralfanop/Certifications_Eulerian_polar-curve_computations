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
  cases n with
  | zero =>
      simpa only [pow_zero, ContinuousLinearMap.one_def] using
        (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := SturmH lam))
  | succ n =>
      calc
        ‖(sturmRealYosidaEulerStep lam t hlam ht h) ^ (n + 1)‖ ≤
            ‖sturmRealYosidaEulerStep lam t hlam ht h‖ ^ (n + 1) :=
          norm_pow_le' _ (Nat.succ_pos n)
        _ ≤ 1 := pow_le_one₀ (norm_nonneg _)
          (sturmRealYosidaEulerStep_opNorm_le lam t hlam ht h hh hsmall)

/-- Pointwise contraction of every Euler product on the true weighted L². -/
theorem sturmRealYosidaEulerIterate_norm_le
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (h : ℝ) (hh : 0 ≤ h) (hsmall : h * t ≤ 1)
    (n : ℕ) (f : SturmH lam) :
    ‖sturmRealYosidaEulerIterate lam t hlam ht h n f‖ ≤ ‖f‖ := by
  have hnorm :=
    sturmRealYosidaEulerIterate_opNorm_le lam t hlam ht h hh hsmall n
  calc
    ‖sturmRealYosidaEulerIterate lam t hlam ht h n f‖ ≤
        ‖sturmRealYosidaEulerIterate lam t hlam ht h n‖ * ‖f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = ‖f‖ := one_mul _

/-- Exact discrete semigroup law for finite Yosida Euler products. -/
theorem sturmRealYosidaEulerIterate_add
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (h : ℝ) (n m : ℕ) :
    sturmRealYosidaEulerIterate lam t hlam ht h (n + m) =
      sturmRealYosidaEulerIterate lam t hlam ht h n *
        sturmRealYosidaEulerIterate lam t hlam ht h m := by
  change (sturmRealYosidaEulerStep lam t hlam ht h) ^ (n + m) =
    (sturmRealYosidaEulerStep lam t hlam ht h) ^ n *
      (sturmRealYosidaEulerStep lam t hlam ht h) ^ m
  exact pow_add _ _ _

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaEulerIterate_opNorm_le
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaEulerIterate_norm_le
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaEulerIterate_add

end GegenbauerFock.Ultraspherical
