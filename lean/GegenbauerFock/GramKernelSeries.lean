import GegenbauerFock.AnalyticAdjoint
import GegenbauerFock.ConcreteFockCompact

/-!
# V007: exact infinite-rank Gram operator via Gegenbauer–Fock monomial rows

This gives an operator identity in the actual ultraspherical L² Hilbert
space, with *norm-convergent* output for every input, and the exact Gram
bilinear form as a convergent series of complex Hilbert coordinate
pairings.  The further identification with the single-integral kernel
exp(u*v/(4*alpha)) must be proved as a separate L² kernel/Bochner
interchange theorem, rather than assumed from the formal Taylor series.
-/

open MeasureTheory
open scoped ENNReal InnerProduct

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The genuine Gram operator C†C is the norm-convergent sum of
rank-one adjoint-row evaluations on every actual input f∈L²(νλ).
This is the nontruncated operator, not a formal finite matrix. -/
theorem gram_eq_tsum_rows
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    gram lam alpha hlam ha f =
      letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
        Ultraspherical.probability lam hlam
      ∑' n : ℕ,
        (WeightedMoments.coefficient
          (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n).adjoint
          ((WeightedMoments.coefficient
            (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n) f) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  change C_adjoint lam alpha hlam ha (C lam alpha hlam ha f) = _
  rw [C_adjoint_eq_tsum_rows lam alpha hlam ha (C lam alpha hlam ha f)]
  apply tsum_congr
  intro n
  rw [C_coefficient lam alpha hlam ha f n]

/-- The precise Gram sesquilinear form is the (convergent) sum of the
row-wise complex pairings; all coordinates are actual L² moments. -/
theorem gram_inner_eq_tsum_rows
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam)) :
    inner ℂ (gram lam alpha hlam ha f) g =
      letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
        Ultraspherical.probability lam hlam
      ∑' n : ℕ,
        inner ℂ
          ((WeightedMoments.coefficient
            (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n) f)
          ((WeightedMoments.coefficient
            (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n) g) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  calc
    inner ℂ (gram lam alpha hlam ha f) g =
        inner ℂ (C lam alpha hlam ha f) (C lam alpha hlam ha g) := by
          exact HilbertGram.gram_inner (C lam alpha hlam ha) f g
    _ = ∑' n : ℕ, inner ℂ ((C lam alpha hlam ha f) n)
         ((C lam alpha hlam ha g) n) := by
          rw [lp.inner_eq_tsum]
    _ = ∑' n : ℕ,
          inner ℂ
            ((WeightedMoments.coefficient
              (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n) f)
            ((WeightedMoments.coefficient
              (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n) g) := by
          apply tsum_congr
          intro n
          rw [C_coefficient lam alpha hlam ha f n,
            C_coefficient lam alpha hlam ha g n]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_eq_tsum_rows
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_inner_eq_tsum_rows

/-- The actual bounded ultraspherical exponential-kernel Gram operator
is compact in the infinite-dimensional source Hilbert space, by
compactness of the actual coefficient map and its Hilbert adjoint. -/
theorem gram_compact_concrete (lam alpha : ℝ)
    (hlam : 0 < lam) (ha : 0 < alpha) :
    IsCompactOperator (gram lam alpha hlam ha) := by
  exact HilbertGram.gram_compact
    (C lam alpha hlam ha) (C_compact lam alpha hlam ha)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_compact_concrete


end GegenbauerFock.GeneralUltrasphericalFock
