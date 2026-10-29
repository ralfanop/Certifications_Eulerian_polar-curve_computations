import GegenbauerFock.OutputGramApproximateZeroSpectrum
import GegenbauerFock.TwoSidedGramProperDenseRange
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# V007 — Gram approximate-zero sequences vanish weakly against range tests

Each exact selfadjoint Gram has a normalized approximate-null sequence.
For every test vector in its (certified dense) image, the sequence's
complex inner products converge to zero. The proof uses the exact
Hilbert adjoint relation and the continuous linear inner functional.
This is a certified *dense-range test* formulation, not a gratuitous
assertion of convergence in an unformalized weak-topology API.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- If an actual bounded Hilbert operator is selfadjoint and T u_n
converges to zero in norm, then inner(T y, u_n) tends to zero for
EVERY y. No compactness assumption is needed for this step. -/
private theorem approx_null_inner_range_tendsto_zero
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hself : T.adjoint = T)
    (u : ℕ → H)
    (himage : Tendsto (fun n : ℕ => T (u n))
      atTop (nhds (0 : H)))
    (y : H) :
    Tendsto (fun n : ℕ => inner ℂ (T y) (u n))
      atTop (nhds (0 : ℂ)) := by
  have hlinear : Tendsto
      (fun n : ℕ => (innerSL ℂ y) (T (u n)))
      atTop (nhds ((innerSL ℂ y) (0 : H))) :=
    (innerSL ℂ y).continuous.continuousAt.tendsto.comp himage
  have heq :
      (fun n : ℕ => inner ℂ (T y) (u n)) =
      (fun n : ℕ => (innerSL ℂ y) (T (u n))) := by
    funext n
    calc
      inner ℂ (T y) (u n) =
          inner ℂ (T.adjoint y) (u n) := by rw [hself]
      _ = inner ℂ y (T (u n)) := T.adjoint_inner_left (u n) y
      _ = (innerSL ℂ y) (T (u n)) := rfl
  rw [heq]
  simpa using hlinear

/-- True normalized approximate-zero source Gram sequence:
weak vanishing of all complex inner products against the
dense range of C†C, without replacing the ultraspherical L² space. -/
theorem sourceGram_approx_zero_weak_on_dense_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Tendsto (fun n : ℕ => gram lam alpha hlam ha (u n))
        atTop (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      (∀ y : Lp ℂ 2 (Ultraspherical.measure lam),
        Tendsto (fun n : ℕ =>
          inner ℂ (gram lam alpha hlam ha y) (u n))
          atTop (nhds (0 : ℂ))) := by
  obtain ⟨u, hunit, himage⟩ :=
    gram_exists_unit_approximate_zero_eigenvectors lam alpha hlam ha
  refine ⟨u, hunit, himage, ?_⟩
  intro y
  exact approx_null_inner_range_tendsto_zero
    (gram lam alpha hlam ha)
    (gram_selfadjoint lam alpha hlam ha)
    u himage y

/-- True normalized approximate-zero output Gram sequence:
weak vanishing against every vector in the dense image of CC†
on the full Fock coefficient Hilbert space. -/
theorem outputGram_approx_zero_weak_on_dense_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ v : ℕ → InfiniteAnalysis.FockCoefficients,
      (∀ n : ℕ, ‖v n‖ = 1) ∧
      Tendsto (fun n : ℕ => outputGram lam alpha hlam ha (v n))
        atTop (nhds (0 : InfiniteAnalysis.FockCoefficients)) ∧
      (∀ y : InfiniteAnalysis.FockCoefficients,
        Tendsto (fun n : ℕ =>
          inner ℂ (outputGram lam alpha hlam ha y) (v n))
          atTop (nhds (0 : ℂ))) := by
  obtain ⟨v, hunit, himage⟩ :=
    outputGram_exists_unit_approximate_zero_eigenvectors lam alpha hlam ha
  refine ⟨v, hunit, himage, ?_⟩
  intro y
  exact approx_null_inner_range_tendsto_zero
    (outputGram lam alpha hlam ha)
    (outputGram_selfadjoint lam alpha hlam ha)
    v himage y

/-- Simultaneous dense-range weak tests for the two actual Grams;
each acts on its own Hilbert space, and both ranges are dense. -/
theorem two_sided_gram_approx_zero_weak_on_dense_ranges
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Tendsto (fun n : ℕ => gram lam alpha hlam ha (u n))
        atTop (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      (∀ y : Lp ℂ 2 (Ultraspherical.measure lam),
        Tendsto (fun n : ℕ =>
          inner ℂ (gram lam alpha hlam ha y) (u n))
          atTop (nhds (0 : ℂ)))) ∧
    (∃ v : ℕ → InfiniteAnalysis.FockCoefficients,
      (∀ n : ℕ, ‖v n‖ = 1) ∧
      Tendsto (fun n : ℕ => outputGram lam alpha hlam ha (v n))
        atTop (nhds (0 : InfiniteAnalysis.FockCoefficients)) ∧
      (∀ y : InfiniteAnalysis.FockCoefficients,
        Tendsto (fun n : ℕ =>
          inner ℂ (outputGram lam alpha hlam ha y) (v n))
          atTop (nhds (0 : ℂ)))) :=
  ⟨sourceGram_approx_zero_weak_on_dense_range lam alpha hlam ha,
   outputGram_approx_zero_weak_on_dense_range lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_approx_zero_weak_on_dense_range
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_approx_zero_weak_on_dense_range
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_approx_zero_weak_on_dense_ranges

end GegenbauerFock.GeneralUltrasphericalFock
