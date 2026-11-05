import GegenbauerFock.RealNuclearRankOneImpliesCompact
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# V007 — genuine compact positive real Gram of any nuclear operator

For any actual nuclear bounded real Hilbert T, we construct the actual
Gram T†T, rather than a diagonal surrogate or global-unitary phase.

Its compactness, selfadjointness, nonnegative quadratic form, exact
kernel and operator norm are certified separately. A polar square
root and partial isometry are not claimed in this module.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The ACTUAL bounded real Hilbert-space Gram. -/
noncomputable def realNuclearGram (T : H →L[ℝ] H) : H →L[ℝ] H :=
  T.adjoint ∘L T

/-- The Gram of an arbitrary nuclear real operator is compact. -/
theorem HasRealNuclearRankOneSeries.gram_isCompactOperator
    {T : H →L[ℝ] H} (hT : HasRealNuclearRankOneSeries T) :
    IsCompactOperator (realNuclearGram T) := by
  change IsCompactOperator (T.adjoint ∘ T)
  exact hT.isCompactOperator.clm_comp T.adjoint

/-- The real Gram is self-adjoint for every bounded T. -/
theorem realNuclearGram_isSelfAdjoint (T : H →L[ℝ] H) :
    IsSelfAdjoint (realNuclearGram T) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  change (T.adjoint ∘L T).adjoint = T.adjoint ∘L T
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

/-- Exact quadratic-form identity for the real Gram. -/
theorem realNuclearGram_inner_eq_norm_sq
    (T : H →L[ℝ] H) (x : H) :
    inner ℝ x (realNuclearGram T x) = ‖T x‖ ^ 2 := by
  change inner ℝ x ((T.adjoint ∘L T) x) = _
  rw [ContinuousLinearMap.comp_apply,
    T.adjoint_inner_right x (T x),
    real_inner_self_eq_norm_sq]

/-- The Gram quadratic form is nonnegative. -/
theorem realNuclearGram_inner_nonneg
    (T : H →L[ℝ] H) (x : H) :
    0 ≤ inner ℝ x (realNuclearGram T x) := by
  rw [realNuclearGram_inner_eq_norm_sq]
  positivity

/-- No injectivity hypothesis: ker(T†T) equals ker(T) exactly. -/
theorem realNuclearGram_ker_eq (T : H →L[ℝ] H) :
    (realNuclearGram T).ker = T.ker := by
  change (T.adjoint ∘L T).ker = T.ker
  exact T.ker_adjoint_comp_self

/-- Exact Gram norm is the square of the original operator norm. -/
theorem realNuclearGram_norm_eq_sq (T : H →L[ℝ] H) :
    ‖realNuclearGram T‖ = ‖T‖ ^ 2 := by
  simpa only [realNuclearGram, pow_two] using T.norm_adjoint_comp_self

#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.gram_isCompactOperator
#print axioms GegenbauerFock.Ultraspherical.realNuclearGram_isSelfAdjoint
#print axioms GegenbauerFock.Ultraspherical.realNuclearGram_inner_eq_norm_sq
#print axioms GegenbauerFock.Ultraspherical.realNuclearGram_inner_nonneg
#print axioms GegenbauerFock.Ultraspherical.realNuclearGram_ker_eq
#print axioms GegenbauerFock.Ultraspherical.realNuclearGram_norm_eq_sq

end GegenbauerFock.Ultraspherical
