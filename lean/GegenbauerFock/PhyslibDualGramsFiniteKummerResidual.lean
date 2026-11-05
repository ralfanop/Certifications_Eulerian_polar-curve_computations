import GegenbauerFock.PhyslibDualGramsFiniteKummerResolvent
import Mathlib.Algebra.Ring.GeomSum

/-!
# V007 — exact two-sided residual of finite Gamma–Kummer Gram inverses

For ANY bounded complex-linear operator A, the N-th geometric
polynomial P_N(A)=Σ_{k=0}^N A^k satisfies both exact identities:
  (I−A) P_N(A) − I = − A^(N+1),
  P_N(A) (I−A) − I = − A^(N+1).

For an actual CFC trace-class operator, the norm of each residual
is at most ‖A‖₁^(N+1). Thus, on either of the two distinct Gram
Hilbert spaces, the two-sided inverse residual is ≤ q^(N+1) with
q=‖z‖·KummerSeries(λ,1/(4α)). Unlike the full inverse error,
this is a *finite algebraic* identity valid even without q<1.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The finite geometric polynomial is a two-sided inverse up to
the *exact* final power, for any bounded operator. -/
theorem finite_geometric_ambient_two_sided_residual
    (A : H →L[ℂ] H) (N : ℕ) :
    (((1 : H →L[ℂ] H) - A) *
        (∑ k ∈ Finset.range (N + 1), A ^ k) - 1 =
        -(A ^ (N + 1))) ∧
    ((∑ k ∈ Finset.range (N + 1), A ^ k) *
        ((1 : H →L[ℂ] H) - A) - 1 =
        -(A ^ (N + 1))) := by
  constructor
  · rw [mul_neg_geom_sum]
    abel
  · rw [geom_sum_mul_neg]
    abel

/-- True trace-class power-norm domination gives both *ambient*
operator residuals the coefficient-one estimate ‖T‖₁^(N+1). -/
theorem finite_geometric_traceClass_two_sided_residual_le
    (T : TraceClass H) (N : ℕ) :
    (‖((1 : H →L[ℂ] H) - T.1) *
        (∑ k ∈ Finset.range (N + 1), T.1 ^ k) - 1‖ ≤
        ‖T‖ ^ (N + 1)) ∧
    (‖(∑ k ∈ Finset.range (N + 1), T.1 ^ k) *
        ((1 : H →L[ℂ] H) - T.1) - 1‖ ≤
        ‖T‖ ^ (N + 1)) := by
  have h := finite_geometric_ambient_two_sided_residual T.1 N
  have hbound : ‖T.1 ^ (N + 1)‖ ≤ ‖T‖ ^ (N + 1) := by
    calc
      ‖T.1 ^ (N + 1)‖ = ‖(positivePower T N).1‖ :=
        congrArg norm (positivePower_operator T N).symm
      _ ≤ ‖positivePower T N‖ := operator_norm_le_trace_norm _
      _ ≤ ‖T‖ ^ (N + 1) := norm_positivePower_le T N
  constructor
  · rw [h.1, norm_neg]
    exact hbound
  · rw [h.2, norm_neg]
    exact hbound

#print axioms ProbabilisticTheory.TraceClass.finite_geometric_ambient_two_sided_residual
#print axioms ProbabilisticTheory.TraceClass.finite_geometric_traceClass_two_sided_residual_le

end ProbabilisticTheory.TraceClass

namespace GegenbauerFock.GeneralUltrasphericalFock
open MeasureTheory

/-- Both finite two-sided inverse residuals for z C* C are bounded
by the exact Gamma–Kummer coupling power q^(N+1). -/
theorem sourceGram_finite_Kummer_two_sided_residual_le
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ) (N : ℕ) :
    let T := z • gramTraceClass lam alpha hlam ha
    (‖((1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)) - T.1) *
        (∑ k ∈ Finset.range (N + 1), T.1 ^ k) - 1‖ ≤
        (‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) ^ (N + 1)) ∧
    (‖(∑ k ∈ Finset.range (N + 1), T.1 ^ k) *
        ((1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam)) - T.1) - 1‖ ≤
        (‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) ^ (N + 1)) := by
  dsimp
  have hn := scaledGramTraceClass_actual_norm_eq_kummer lam alpha hlam ha z
  simpa only [hn] using
    (ProbabilisticTheory.TraceClass.finite_geometric_traceClass_two_sided_residual_le
      (z • gramTraceClass lam alpha hlam ha) N)

/-- Both finite two-sided inverse residuals for z C C* are bounded
by the identical Gamma–Kummer power, but in Fock coefficients. -/
theorem outputGram_finite_Kummer_two_sided_residual_le
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ) (N : ℕ) :
    let T := z • outputGramTraceClass lam alpha hlam ha
    (‖((1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
        InfiniteAnalysis.FockCoefficients) - T.1) *
        (∑ k ∈ Finset.range (N + 1), T.1 ^ k) - 1‖ ≤
        (‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) ^ (N + 1)) ∧
    (‖(∑ k ∈ Finset.range (N + 1), T.1 ^ k) *
        ((1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients) - T.1) - 1‖ ≤
        (‖z‖ * KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) ^ (N + 1)) := by
  dsimp
  have hn := scaledOutputGramTraceClass_actual_norm_eq_kummer lam alpha hlam ha z
  simpa only [hn] using
    (ProbabilisticTheory.TraceClass.finite_geometric_traceClass_two_sided_residual_le
      (z • outputGramTraceClass lam alpha hlam ha) N)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_finite_Kummer_two_sided_residual_le
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_finite_Kummer_two_sided_residual_le

end GegenbauerFock.GeneralUltrasphericalFock
