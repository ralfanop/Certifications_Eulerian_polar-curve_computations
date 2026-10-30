import GegenbauerFock.CanonicalCFCApproximateNullFamily

/-!
# V007 — a shared quantitative instability certificate for the polar factor

The true Gegenbauer--Fock operator C and its named canonical positive
CFC Gram square root P share exactly the same image norm under a
certified unitary factor W: C = W P. Their normalized approximate-null
vectors can therefore be chosen simultaneously, with the explicit
1/(n+1) estimate on both images.

This theorem combines compactness, injectivity, proper dense nonclosed
range, and quantitative instability into one reusable Lean result.
It makes no false claim of a nonzero kernel or a bounded inverse.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The actual canonical CFC square root and true Fock transform
have the same quantified approximate-null vectors, with identical
output norms, while the canonical square root remains a compact
injective operator with proper dense nonclosed image. -/
theorem exists_shared_cfc_polar_instability_family
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (W : Lp ℂ 2 (Ultraspherical.measure lam) ≃ₗᵢ[ℂ]
        InfiniteAnalysis.FockCoefficients)
      (u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam)),
      IsCompactOperator (localCFCGramSqrt lam alpha hlam ha) ∧
      Function.Injective (localCFCGramSqrt lam alpha hlam ha) ∧
      (localCFCGramSqrt lam alpha hlam ha).range.topologicalClosure =
        (⊤ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      ¬ IsClosed ((localCFCGramSqrt lam alpha hlam ha).range :
        Set (Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      (∀ f, C lam alpha hlam ha f =
        W (localCFCGramSqrt lam alpha hlam ha f)) ∧
      (∀ n : ℕ,
        ‖u n‖ = 1 ∧
        ‖C lam alpha hlam ha (u n)‖ =
          ‖localCFCGramSqrt lam alpha hlam ha (u n)‖ ∧
        ‖localCFCGramSqrt lam alpha hlam ha (u n)‖ <
          1 / ((n : ℝ) + 1)) := by
  classical
  obtain ⟨W, hcompact, hinj, hdense, hnotclosed, hC⟩ :=
    exists_local_cfc_sqrt_compact_dense_nonclosed lam alpha hlam ha
  obtain ⟨u, hquant⟩ :=
    local_cfc_root_exists_normalized_approximate_null_family
      lam alpha hlam ha
  refine ⟨W, u, hcompact, hinj, hdense, hnotclosed, hC, ?_⟩
  intro n
  refine ⟨(hquant n).1, ?_, (hquant n).2⟩
  rw [hC (u n)]
  exact W.norm_map _

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_shared_cfc_polar_instability_family

end GegenbauerFock.GeneralUltrasphericalFock
