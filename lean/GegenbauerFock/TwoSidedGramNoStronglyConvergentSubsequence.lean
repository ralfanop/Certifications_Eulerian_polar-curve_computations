import GegenbauerFock.OutputGramApproximateZeroSpectrum
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# V007 — both Gram approximate-zero sequences have no strongly convergent subsequence

Zero is a genuine continuous spectral point of the actual source
and output Grams. Each has a normalized sequence of approximate-zero
vectors. Here we strengthen nonconvergence of the full sequences:
for EVERY strictly increasing selection of indices, the selected
subsequence has NO norm limit in its own Hilbert space.

The proof uses only continuity of each actual bounded Gram,
triviality of its kernel and the exact constant unit norms. It neither
introduces a nonzero zero-eigenvector nor identifies the two spaces.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- A normalized approximate-null sequence for an injective bounded
operator cannot contain a strongly convergent subsequence. -/
private theorem unit_approx_null_no_strong_subsequence
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H)
    (hinj : Function.Injective T)
    (u : ℕ → H)
    (hunit : ∀ n : ℕ, ‖u n‖ = 1)
    (himage : Tendsto (fun n : ℕ => T (u n))
      atTop (nhds (0 : H)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (x : H) :
    ¬ Tendsto (fun n : ℕ => u (φ n)) atTop (nhds x) := by
  intro hconv
  have himage_sub : Tendsto (fun n : ℕ => T (u (φ n)))
      atTop (nhds (0 : H)) :=
    himage.comp hφ.tendsto_atTop
  have hmap_sub : Tendsto (fun n : ℕ => T (u (φ n)))
      atTop (nhds (T x)) :=
    T.continuous.continuousAt.tendsto.comp hconv
  have hTx : T x = 0 :=
    tendsto_nhds_unique hmap_sub himage_sub
  have hx : x = 0 := by
    apply hinj
    simpa using hTx
  have hnormconv : Tendsto (fun n : ℕ => ‖u (φ n)‖)
      atTop (nhds ‖x‖) := hconv.norm
  have hnormone : Tendsto (fun n : ℕ => ‖u (φ n)‖)
      atTop (nhds (1 : ℝ)) := by
    have heq : (fun n : ℕ => ‖u (φ n)‖) =
        (fun _ : ℕ => (1 : ℝ)) := by
      funext n
      exact hunit (φ n)
    rw [heq]
    exact tendsto_const_nhds
  have hnormx : ‖x‖ = 1 :=
    tendsto_nhds_unique hnormconv hnormone
  simp [hx] at hnormx

/-- Unit approximate-zero source Gram vectors with no strongly
convergent subsequence in the genuine ultraspherical L² space. -/
theorem sourceGram_approx_zero_no_strong_subsequence
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Tendsto (fun n : ℕ => gram lam alpha hlam ha (u n))
        atTop (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      (∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
          ¬ Tendsto (fun n : ℕ => u (φ n)) atTop (nhds f)) := by
  obtain ⟨u, hunit, himage⟩ :=
    gram_exists_unit_approximate_zero_eigenvectors lam alpha hlam ha
  have hinj : Function.Injective (gram lam alpha hlam ha) :=
    LinearMap.ker_eq_bot.mp
      (source_gram_zero_continuous_spectrum lam alpha hlam ha).2.1
  refine ⟨u, hunit, himage, ?_⟩
  intro φ hφ f
  exact unit_approx_null_no_strong_subsequence
    (gram lam alpha hlam ha) hinj u hunit himage φ hφ f

/-- Unit approximate-zero output Gram vectors with no strongly
convergent subsequence in full Gaussian–Fock coefficient ℓ². -/
theorem outputGram_approx_zero_no_strong_subsequence
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ v : ℕ → InfiniteAnalysis.FockCoefficients,
      (∀ n : ℕ, ‖v n‖ = 1) ∧
      Tendsto (fun n : ℕ => outputGram lam alpha hlam ha (v n))
        atTop (nhds (0 : InfiniteAnalysis.FockCoefficients)) ∧
      (∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ F : InfiniteAnalysis.FockCoefficients,
          ¬ Tendsto (fun n : ℕ => v (φ n)) atTop (nhds F)) := by
  obtain ⟨v, hunit, himage⟩ :=
    outputGram_exists_unit_approximate_zero_eigenvectors lam alpha hlam ha
  have hinj : Function.Injective (outputGram lam alpha hlam ha) :=
    LinearMap.ker_eq_bot.mp
      (output_gram_zero_continuous_spectrum lam alpha hlam ha).2.1
  refine ⟨v, hunit, himage, ?_⟩
  intro φ hφ F
  exact unit_approx_null_no_strong_subsequence
    (outputGram lam alpha hlam ha) hinj v hunit himage φ hφ F

/-- The two actual Grams have unit approximate-zero sequences, and
neither Hilbert-side sequence admits a norm-convergent subsequence. -/
theorem two_sided_gram_approx_zero_no_strong_subsequences
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Tendsto (fun n : ℕ => gram lam alpha hlam ha (u n))
        atTop (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      (∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
          ¬ Tendsto (fun n : ℕ => u (φ n)) atTop (nhds f))) ∧
    (∃ v : ℕ → InfiniteAnalysis.FockCoefficients,
      (∀ n : ℕ, ‖v n‖ = 1) ∧
      Tendsto (fun n : ℕ => outputGram lam alpha hlam ha (v n))
        atTop (nhds (0 : InfiniteAnalysis.FockCoefficients)) ∧
      (∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ F : InfiniteAnalysis.FockCoefficients,
          ¬ Tendsto (fun n : ℕ => v (φ n)) atTop (nhds F))) :=
  ⟨sourceGram_approx_zero_no_strong_subsequence lam alpha hlam ha,
   outputGram_approx_zero_no_strong_subsequence lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_approx_zero_no_strong_subsequence
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_approx_zero_no_strong_subsequence
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_approx_zero_no_strong_subsequences

end GegenbauerFock.GeneralUltrasphericalFock
