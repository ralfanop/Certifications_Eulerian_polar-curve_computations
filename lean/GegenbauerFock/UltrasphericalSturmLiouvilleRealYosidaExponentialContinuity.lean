import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaExponential
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# V007 — norm-continuity of the bounded ultraspherical Sturm Yosida semigroups

For each fixed positive Yosida parameter t, the bounded operator family
S_t(s) = exp(s A_t) acts on the genuine real ultraspherical weighted L².
It is continuous in the operator norm for every real time s. Therefore,
for every actual L² vector f, the orbit s ↦ S_t(s) f is strongly continuous.

Together with the separately proved exact exponential semigroup law,
this gives a genuine norm-continuous semigroup for each bounded Yosida
approximation. It is NOT yet a certified strong t→∞ limit of these
semigroups, nor a generator identification for the unbounded closure.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Norm continuity of the actual bounded Yosida exponential family. -/
theorem sturmRealYosidaExponential_continuous
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Continuous (fun s : ℝ =>
      sturmRealYosidaExponential lam t hlam ht s) := by
  let A := sturmRealYosidaGenerator lam t hlam ht
  letI : NormedAlgebra ℚ (SturmH lam →L[ℝ] SturmH lam) :=
    .restrictScalars ℚ ℝ _
  change Continuous (fun s : ℝ => NormedSpace.exp (s • A))
  exact NormedSpace.exp_continuous.comp
    (continuous_id.smul continuous_const)

/-- Strong continuity of every actual real weighted-L² orbit of
the bounded Yosida exponential semigroup. -/
theorem sturmRealYosidaExponential_orbit_continuous
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) :
    Continuous (fun s : ℝ =>
      sturmRealYosidaExponential lam t hlam ht s f) := by
  exact Continuous.clm_apply
    (sturmRealYosidaExponential_continuous lam t hlam ht)
    continuous_const

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaExponential_continuous
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaExponential_orbit_continuous

end GegenbauerFock.Ultraspherical
