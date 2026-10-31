import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaExponentialNorm
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# V007 — exponential action on an exact real-L² operator eigenvector

For a bounded real-linear endomorphism X on genuine ultraspherical
weighted L² and an eigenvector f with X f = mu f, the genuine
Banach-algebra operator exponential satisfies exp(X) f = exp(mu) f.

The proof uses the norm-convergent Banach-algebra exponential series,
continuous evaluation at f, and the scalar real exponential series.
No spectral theorem, analyticity or unbounded semigroup is assumed.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Exponentiation of any actual bounded real-L² endomorphism sends
each eigenvector to the same eigenvector with exponentiated eigenvalue. -/
theorem sturmRealOperatorExponential_eigenvector
    (lam : ℝ) (X : SturmH lam →L[ℝ] SturmH lam)
    (f : SturmH lam) (mu : ℝ)
    (hEigen : X f = mu • f) :
    (NormedSpace.exp X) f = (Real.exp mu) • f := by
  letI : NormedAlgebra ℚ (SturmH lam →L[ℝ] SturmH lam) :=
    .restrictScalars ℚ ℝ _
  have hpow (n : ℕ) :
      (X ^ n) f = (mu ^ n) • f := by
    induction n with
    | zero =>
        simp only [pow_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply,
          one_smul]
    | succ n ih =>
        calc
          (X ^ (n + 1)) f = (X ^ n) (X f) := by
            rw [pow_succ, ContinuousLinearMap.mul_def]
            rfl
          _ = (X ^ n) (mu • f) := by rw [hEigen]
          _ = mu • ((X ^ n) f) := by rw [map_smul]
          _ = mu • ((mu ^ n) • f) := by rw [ih]
          _ = (mu ^ (n + 1)) • f := by
            rw [smul_smul, pow_succ]
            congr 1
            ring
  have hOperator :
      HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • X ^ n)
        (NormedSpace.exp X) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X
  have hScalar :
      HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) * mu ^ n)
        (Real.exp mu) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa only [smul_eq_mul] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) mu)
  have hMapped := hOperator.mapL (ContinuousLinearMap.apply ℝ (SturmH lam) f)
  change HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • ((X ^ n) f))
      ((NormedSpace.exp X) f) at hMapped
  have hSeries :
      HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) * mu ^ n) • f)
        ((NormedSpace.exp X) f) := by
    simpa only [hpow, smul_smul] using hMapped
  exact hSeries.unique (hScalar.smul_const f)

#print axioms GegenbauerFock.Ultraspherical.sturmRealOperatorExponential_eigenvector

end GegenbauerFock.Ultraspherical
