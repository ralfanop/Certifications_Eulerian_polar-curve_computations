import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaAllL2StrongLimit
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# V007 — bounded heat-limit operator from the genuine full-L² Yosida limit

The previous full-L² theorem gives a strong limit of S_{k+1}(s) f for
every f in genuine weighted real L² and every s≥0.
The limit is unique and thus defines a real-linear operator H_s.

Linearity follows directly by passing to the limit in the finite-time
bounded operators, and ‖H_s f‖≤‖f‖ follows by closedness of norm
inequalities under limits. Hence H_s is an actual continuous linear
operator of norm at most one. No semigroup law or generator identity
for these limiting operators is asserted here.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Strong limit of the bounded Yosida semigroups on a real-L² vector. -/
noncomputable def sturmRealHeatLimitVector
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s)
    (f : SturmH lam) : SturmH lam :=
  Classical.choose
    (sturmRealYosidaExponential_allL2_strong_limit_exists
      lam hlam s hs f)

/-- The chosen heat limit is actually the strong limit in weighted L². -/
theorem sturmRealHeatLimitVector_tendsto
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s)
    (f : SturmH lam) :
    Tendsto
      (fun k : ℕ =>
        sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
          (by positivity : 0 < (k : ℝ) + 1) s f)
      atTop (𝓝 (sturmRealHeatLimitVector lam hlam s hs f)) :=
  Classical.choose_spec
    (sturmRealYosidaExponential_allL2_strong_limit_exists
      lam hlam s hs f)

/-- Additivity of the limit on all of the genuine real weighted L². -/
theorem sturmRealHeatLimitVector_add
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s)
    (f g : SturmH lam) :
    sturmRealHeatLimitVector lam hlam s hs (f + g) =
      sturmRealHeatLimitVector lam hlam s hs f +
        sturmRealHeatLimitVector lam hlam s hs g := by
  have hsum :=
    (sturmRealHeatLimitVector_tendsto lam hlam s hs f).add
      (sturmRealHeatLimitVector_tendsto lam hlam s hs g)
  have hsum' :
      Tendsto
        (fun k : ℕ =>
          sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
            (by positivity : 0 < (k : ℝ) + 1) s (f + g))
        atTop
        (𝓝 (sturmRealHeatLimitVector lam hlam s hs f +
          sturmRealHeatLimitVector lam hlam s hs g)) := by
    simpa only [map_add] using hsum
  exact tendsto_nhds_unique
    (sturmRealHeatLimitVector_tendsto lam hlam s hs (f + g))
    hsum'

/-- Real homogeneity of the strongly constructed heat-limit operator. -/
theorem sturmRealHeatLimitVector_smul
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s)
    (a : ℝ) (f : SturmH lam) :
    sturmRealHeatLimitVector lam hlam s hs (a • f) =
      a • sturmRealHeatLimitVector lam hlam s hs f := by
  have hsmul :=
    (sturmRealHeatLimitVector_tendsto lam hlam s hs f).const_smul a
  have hsmul' :
      Tendsto
        (fun k : ℕ =>
          sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
            (by positivity : 0 < (k : ℝ) + 1) s (a • f))
        atTop (𝓝 (a • sturmRealHeatLimitVector lam hlam s hs f)) := by
    simpa only [map_smul] using hsmul
  exact tendsto_nhds_unique
    (sturmRealHeatLimitVector_tendsto lam hlam s hs (a • f))
    hsmul'

/-- The actual strong Yosida limit contracts each L² vector. -/
theorem sturmRealHeatLimitVector_norm_le
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s)
    (f : SturmH lam) :
    ‖sturmRealHeatLimitVector lam hlam s hs f‖ ≤ ‖f‖ := by
  have htend :=
    (sturmRealHeatLimitVector_tendsto lam hlam s hs f).norm
  apply le_of_tendsto htend
  exact Filter.Eventually.of_forall fun k =>
    sturmRealYosidaExponential_norm_le lam ((k : ℝ) + 1) hlam
      (by positivity : 0 < (k : ℝ) + 1) s hs f

/-- The fully defined limiting heat operator is bounded, real-linear
and acts on every vector of the actual weighted real L². -/
noncomputable def sturmRealHeatLimitCLM
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s) :
    SturmH lam →L[ℝ] SturmH lam :=
  ({ toFun := sturmRealHeatLimitVector lam hlam s hs
     map_add' := sturmRealHeatLimitVector_add lam hlam s hs
     map_smul' := sturmRealHeatLimitVector_smul lam hlam s hs } :
      SturmH lam →ₗ[ℝ] SturmH lam).mkContinuous 1
        (by
          intro f
          change ‖sturmRealHeatLimitVector lam hlam s hs f‖ ≤ 1 * ‖f‖
          simpa only [one_mul] using
            sturmRealHeatLimitVector_norm_le lam hlam s hs f)

/-- Exact operator norm bound of the strong limiting heat evolution. -/
theorem sturmRealHeatLimitCLM_opNorm_le
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s) :
    ‖sturmRealHeatLimitCLM lam hlam s hs‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖sturmRealHeatLimitVector lam hlam s hs f‖ ≤ 1 * ‖f‖
  simpa only [one_mul] using
    sturmRealHeatLimitVector_norm_le lam hlam s hs f

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitVector_tendsto
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitVector_add
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitVector_smul
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitVector_norm_le
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_opNorm_le

end GegenbauerFock.Ultraspherical
