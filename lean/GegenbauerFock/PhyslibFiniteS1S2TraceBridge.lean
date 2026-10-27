import GegenbauerFock.PhyslibFinitePositiveTraceNorm
import GegenbauerFock.PhyslibS1S2TraceBridge

/-!
# V007 — finite positive Gram families: exact S₁/S₂ energy identity

The genuine CFC trace norm of a finite sum of arbitrary positive
source-conjugated Gegenbauer–Fock Grams equals the finite sum of the
squared, basis-independent Hilbert–Schmidt norms of their analysis maps.

The bounded source preconditioners need not commute, and none of the
Gram terms is assumed finite-rank. This is an exact finite-family
identity, not the unproved general Schatten-S₁ triangle inequality
or a claim of Banach completeness.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- Exact finite-family trace/HS identity for arbitrary bounded
source preconditioners, with genuine CFC S₁ and basis-independent S₂. -/
theorem gramFiniteSum_traceNorm_eq_sum_s2Norm_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (s : Finset ι)
    (B : ι → Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.traceNorm
      (gramFiniteSum lam alpha hlam ha s B)
      (gramFiniteSum_isTraceClass lam alpha hlam ha s B) =
    ∑ i ∈ s,
      (FockEnergy.s2Norm ((C lam alpha hlam ha).comp (B i))
        (C_comp_right_rows_summable lam alpha hlam ha (B i))) ^ 2 := by
  rw [gramFiniteSum_traceNorm_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact gramAfterRight_traceNorm_eq_s2Norm_sq lam alpha hlam ha (B i)

/-- Finite-family Schatten bound, expressed using the actual S₂ norm
of C rather than an auxiliary Kummer or nuclear-mass proxy. -/
theorem gramFiniteSum_traceNorm_le_s2Norm_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (s : Finset ι)
    (B : ι → Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.traceNorm
      (gramFiniteSum lam alpha hlam ha s B)
      (gramFiniteSum_isTraceClass lam alpha hlam ha s B) ≤
    (∑ i ∈ s, ‖B i‖ ^ 2) *
      (FockEnergy.s2Norm (C lam alpha hlam ha)
        (C_rows_summable lam alpha hlam ha)) ^ 2 := by
  rw [C_s2Norm_sq_eq_kummer]
  exact gramFiniteSum_traceNorm_le_kummer lam alpha hlam ha s B

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramFiniteSum_traceNorm_eq_sum_s2Norm_sq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramFiniteSum_traceNorm_le_s2Norm_sq

end GegenbauerFock.GeneralUltrasphericalFock
