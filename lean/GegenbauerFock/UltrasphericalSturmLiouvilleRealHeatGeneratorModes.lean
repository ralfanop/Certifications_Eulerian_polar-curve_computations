import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitModeContinuity
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# V007 — infinitesimal heat generator on every normalized Gegenbauer mode

For λ>0, the true full-real-L² strongly continuous heat contraction
semigroup has the certified spectral mode action
H_s u_n = exp(-s n(n+2λ)) u_n.

The infinitesimal generator is identified explicitly on every
normalized Gegenbauer mode, using the right-hand difference quotient
at time zero and differentiation of the real exponential.
This does NOT yet identify the full generator domain with the closure
of the polynomial Sturm differential operator. That domain equality is
the subsequent maximal-dissipativity/spectral-core obligation.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The difference quotient of the genuine heat-limit semigroup
converges in the actual weighted real L² to the exact Gegenbauer
spectral generator eigenvalue on every normalized eigenmode. -/
theorem sturmRealHeatLimit_generator_on_normalized_Gegenbauer
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    Tendsto
      (fun h : ℝ => h⁻¹ •
        (sturmRealHeatLimitNonnegativeExtended lam hlam h
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n) -
         sturmMonicEigenCandidate_realL2_normalized lam hlam n))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((-((n : ℝ) * ((n : ℝ) + 2 * lam))) •
        sturmMonicEigenCandidate_realL2_normalized lam hlam n)) := by
  let omega : ℝ := (n : ℝ) * ((n : ℝ) + 2 * lam)
  let v : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam n
  have harg : HasDerivAt (fun t : ℝ => -t * omega) (-omega) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).neg.mul_const omega) using 1 <;> simp
  have hscalar : HasDerivAt
      (fun t : ℝ => Real.exp (-t * omega)) (-omega) 0 := by
    convert ((Real.hasDerivAt_exp (0 : ℝ)).comp 0 harg) using 1 <;> simp
  have hvec : HasDerivAt
      (fun t : ℝ => Real.exp (-t * omega) • v)
      ((-omega) • v) 0 :=
    hscalar.smul_const v
  have hright :
      Tendsto
        (fun t : ℝ =>
          t⁻¹ • (Real.exp (-t * omega) • v - v))
        (𝓝[>] (0 : ℝ)) (𝓝 ((-omega) • v)) := by
    simpa only [zero_add, neg_zero, zero_mul, Real.exp_zero, one_smul]
      using hvec.tendsto_slope_zero_right
  have hmode (t : ℝ) (ht : 0 < t) :
      sturmRealHeatLimitNonnegativeExtended lam hlam t v =
        Real.exp (-t * omega) • v := by
    simpa only [max_eq_right ht.le] using
      (sturmRealHeatLimitNonnegativeExtended_mode lam hlam t n)
  have hevent :
      (fun t : ℝ =>
          t⁻¹ • (Real.exp (-t * omega) • v - v)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ =>
          t⁻¹ • (sturmRealHeatLimitNonnegativeExtended lam hlam t v - v)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hmode t ht]
  change Tendsto
    (fun t : ℝ =>
      t⁻¹ • (sturmRealHeatLimitNonnegativeExtended lam hlam t v - v))
    (𝓝[>] (0 : ℝ)) (𝓝 ((-omega) • v))
  exact Filter.Tendsto.congr' hevent hright

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimit_generator_on_normalized_Gegenbauer

end GegenbauerFock.Ultraspherical
