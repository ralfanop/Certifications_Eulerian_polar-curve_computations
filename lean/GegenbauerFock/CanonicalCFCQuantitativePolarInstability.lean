import GegenbauerFock.CanonicalCFCApproximateNullFamily
import GegenbauerFock.GramApproximateZeroSpectrum

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

/-- A *single* normalized family tends strongly to zero under both
the canonical CFC Gram square root and the true Fock transform.
The inputs themselves stay on the unit sphere. -/
theorem exists_shared_cfc_polar_strong_null_sequence
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Filter.Tendsto
        (fun n : ℕ => localCFCGramSqrt lam alpha hlam ha (u n))
        Filter.atTop
        (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      Filter.Tendsto
        (fun n : ℕ => C lam alpha hlam ha (u n))
        Filter.atTop (nhds (0 : InfiniteAnalysis.FockCoefficients)) := by
  classical
  obtain ⟨W, u, hcompact, hinj, hdense, hnotclosed, hpolar, hquant⟩ :=
    exists_shared_cfc_polar_instability_family lam alpha hlam ha
  have hP : Filter.Tendsto
      (fun n : ℕ => localCFCGramSqrt lam alpha hlam ha (u n))
      Filter.atTop
      (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero
      (fun n : ℕ =>
        norm_nonneg (localCFCGramSqrt lam alpha hlam ha (u n)))
      (fun n : ℕ => (hquant n).2.2.le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine ⟨u, (fun n => (hquant n).1), hP, ?_⟩
  have hW : Filter.Tendsto
      (fun n : ℕ => W (localCFCGramSqrt lam alpha hlam ha (u n)))
      Filter.atTop
      (nhds (W (0 : Lp ℂ 2 (Ultraspherical.measure lam)))) :=
    W.continuous.continuousAt.tendsto.comp hP
  have hseq :
      (fun n : ℕ => C lam alpha hlam ha (u n)) =
      (fun n : ℕ => W (localCFCGramSqrt lam alpha hlam ha (u n))) := by
    funext n
    exact hpolar (u n)
  rw [hseq]
  simpa only [map_zero] using hW

/-- The same unit inputs are approximate-zero vectors simultaneously
for the Gegenbauer--Fock transform, its canonical CFC polar root, and
the genuine source Gram. In particular no extra selection of Gram
witnesses is necessary. -/
theorem exists_shared_cfc_fock_gram_strong_null_sequence
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Filter.Tendsto
        (fun n : ℕ => localCFCGramSqrt lam alpha hlam ha (u n))
        Filter.atTop
        (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      Filter.Tendsto
        (fun n : ℕ => C lam alpha hlam ha (u n))
        Filter.atTop (nhds (0 : InfiniteAnalysis.FockCoefficients)) ∧
      Filter.Tendsto
        (fun n : ℕ => gram lam alpha hlam ha (u n))
        Filter.atTop
        (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) := by
  obtain ⟨u, hunit, hP, hC⟩ :=
    exists_shared_cfc_polar_strong_null_sequence lam alpha hlam ha
  refine ⟨u, hunit, hP, hC, ?_⟩
  change Filter.Tendsto
    (fun n : ℕ => C_adjoint lam alpha hlam ha
      (C lam alpha hlam ha (u n)))
    Filter.atTop
    (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam)))
  have hG : Filter.Tendsto
      (fun n : ℕ => C_adjoint lam alpha hlam ha
        (C lam alpha hlam ha (u n)))
      Filter.atTop
      (nhds (C_adjoint lam alpha hlam ha
        (0 : InfiniteAnalysis.FockCoefficients))) :=
    (C_adjoint lam alpha hlam ha).continuous.continuousAt.tendsto.comp hC
  simpa only [map_zero] using hG

/-- A single unit sequence simultaneously controls the canonical
positive polar amplitude, the Fock transform and its source Gram.
The Gram estimate follows from the adjoint operator norm, not from
an assumed spectral gap. -/
theorem exists_shared_cfc_fock_gram_quantitative_family
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      ∀ n : ℕ,
        ‖u n‖ = 1 ∧
        ‖localCFCGramSqrt lam alpha hlam ha (u n)‖ <
          1 / ((n : ℝ) + 1) ∧
        ‖C lam alpha hlam ha (u n)‖ =
          ‖localCFCGramSqrt lam alpha hlam ha (u n)‖ ∧
        ‖gram lam alpha hlam ha (u n)‖ ≤
          ‖C_adjoint lam alpha hlam ha‖ * (1 / ((n : ℝ) + 1)) := by
  classical
  obtain ⟨W, u, hcompact, hinj, hdense, hnotclosed, hpolar, hquant⟩ :=
    exists_shared_cfc_polar_instability_family lam alpha hlam ha
  refine ⟨u, ?_⟩
  intro n
  refine ⟨(hquant n).1, (hquant n).2.2, (hquant n).2.1, ?_⟩
  have hCbound : ‖C lam alpha hlam ha (u n)‖ ≤
      1 / ((n : ℝ) + 1) := by
    rw [(hquant n).2.1]
    exact (hquant n).2.2.le
  calc
    ‖gram lam alpha hlam ha (u n)‖ =
        ‖C_adjoint lam alpha hlam ha (C lam alpha hlam ha (u n))‖ := rfl
    _ ≤ ‖C_adjoint lam alpha hlam ha‖ *
        ‖C lam alpha hlam ha (u n)‖ :=
      (C_adjoint lam alpha hlam ha).le_opNorm _
    _ ≤ ‖C_adjoint lam alpha hlam ha‖ * (1 / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hCbound (norm_nonneg _)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_shared_cfc_fock_gram_quantitative_family

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_shared_cfc_fock_gram_strong_null_sequence

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_shared_cfc_polar_strong_null_sequence

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_shared_cfc_polar_instability_family

end GegenbauerFock.GeneralUltrasphericalFock
