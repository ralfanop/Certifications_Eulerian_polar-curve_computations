import Mathlib

/-!
# V007: compactness from norm-convergent finite-rank approximations

This generic Hilbert-space operator lemma isolates the exact missing
step between compact Fock coefficient truncations (already proven in
InfiniteFockTruncations.lean) and compactness of the *full* operator.

No compactness of the actual Gegenbauer–Fock transform follows until
a concrete operator is constructed and its truncations converge in
operator norm. The present theorem makes that hypothesis explicit.
-/

namespace GegenbauerFock.CompactnessBridge

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [CompleteSpace F]

/-- A norm-limit of compact bounded complex-linear maps is compact. -/
theorem compact_of_operator_norm_limit
    (T : E →L[ℂ] F) (Tn : ℕ → E →L[ℂ] F)
    (hcompact : ∀ n, IsCompactOperator (Tn n))
    (hlimit : Filter.Tendsto Tn Filter.atTop (nhds T)) :
    IsCompactOperator T := by
  exact isCompactOperator_of_tendsto hlimit
    (Filter.Eventually.of_forall hcompact)

#print axioms GegenbauerFock.CompactnessBridge.compact_of_operator_norm_limit

end GegenbauerFock.CompactnessBridge
