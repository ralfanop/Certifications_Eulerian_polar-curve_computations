import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatClosedDomainCommutation
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatGeneratorExactGraph

/-!
# V007 — genuine Gegenbauer heat contraction in the canonical Sturm graph norm

For every positive ultraspherical parameter and every nonnegative time, the
actual full weighted-real-L² semigroup preserves the domain of the canonical
closure of the polynomial Gegenbauer Sturm–Liouville operator. Its action is
a contraction for the SUM GRAPH NORM

  ||f||_{graph} = ||f||₂ + ||closure(A_{lambda,0}) f||₂.

This assertion uses the true closed differential operator, not a formally
diagonal surrogate. Domain invariance and commutation were certified in the
earlier module; the two norm bounds use the certified full-L² contraction.
The exact equality of the closed operator with the heat generator was
independently certified in the imported generator-graph module.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The genuine heat semigroup is a contraction on the canonical closed
Sturm domain equipped with the sum graph norm. -/
theorem sturmRealHeatLimitCLM_closed_graph_norm_contracts
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    ∃ z : (sturmRealPartialOperator lam hlam).closure.domain,
      (z : SturmH lam) =
        sturmRealHeatLimitCLM lam hlam s hs (x : SturmH lam) ∧
      (sturmRealPartialOperator lam hlam).closure z =
        sturmRealHeatLimitCLM lam hlam s hs
          ((sturmRealPartialOperator lam hlam).closure x) ∧
      (‖(z : SturmH lam)‖ +
          ‖(sturmRealPartialOperator lam hlam).closure z‖ ≤
        ‖(x : SturmH lam)‖ +
          ‖(sturmRealPartialOperator lam hlam).closure x‖) := by
  let T : SturmH lam →L[ℝ] SturmH lam :=
    sturmRealHeatLimitCLM lam hlam s hs
  let A := (sturmRealPartialOperator lam hlam).closure
  obtain ⟨z, hz, hAz⟩ :=
    sturmRealHeatLimitCLM_closed_domain_invariant_commutes
      lam hlam s hs x
  have hT (f : SturmH lam) : ‖T f‖ ≤ ‖f‖ := by
    calc
      ‖T f‖ ≤ ‖T‖ * ‖f‖ := ContinuousLinearMap.le_opNorm T f
      _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
        (sturmRealHeatLimitCLM_opNorm_le lam hlam s hs) (norm_nonneg f)
      _ = ‖f‖ := one_mul _
  have hn1 : ‖(z : SturmH lam)‖ ≤ ‖(x : SturmH lam)‖ := by
    rw [hz]
    exact hT (x : SturmH lam)
  have hn2 : ‖A z‖ ≤ ‖A x‖ := by
    rw [hAz]
    exact hT (A x)
  exact ⟨z, hz, hAz, add_le_add hn1 hn2⟩

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_closed_graph_norm_contracts

end GegenbauerFock.Ultraspherical
