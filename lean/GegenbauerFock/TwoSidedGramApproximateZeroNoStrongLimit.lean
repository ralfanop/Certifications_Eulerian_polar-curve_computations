import GegenbauerFock.OutputGramApproximateZeroSpectrum

/-!
# V007 — neither normalized approximate-zero Gram sequence has a strong limit

Both exact Grams have normalized approximate-zero sequences. Because
both Grams are continuous and injective, any hypothetical strong limit
would be zero, contradicting the fact that every sequence element has
unit norm. This is an additional geometric consequence of the
continuous-spectrum classification in each *different* Hilbert space.

All results concern the actual nontruncated ultraspherical/Fock maps.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- No strong limit can exist for a unit approximate-null sequence
of an injective bounded Hilbert-space endomorphism. -/
private theorem unit_approximate_null_no_strong_limit
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hinj : Function.Injective T)
    (u : ℕ → H)
    (hunit : ∀ n : ℕ, ‖u n‖ = 1)
    (himage : Tendsto (fun n : ℕ => T (u n))
      atTop (nhds (0 : H))) :
    ∀ x : H, ¬ Tendsto u atTop (nhds x) := by
  intro x hconv
  have hTconv : Tendsto (fun n : ℕ => T (u n))
      atTop (nhds (T x)) :=
    T.continuous.continuousAt.tendsto.comp hconv
  have hTx : T x = 0 := tendsto_nhds_unique hTconv himage
  have hx : x = 0 := by
    apply hinj
    simpa using hTx
  have hnormconv : Tendsto (fun n : ℕ => ‖u n‖)
      atTop (nhds ‖x‖) := hconv.norm
  have hnormunit : Tendsto (fun n : ℕ => ‖u n‖)
      atTop (nhds (1 : ℝ)) := by
    have heq : (fun n : ℕ => ‖u n‖) =
        (fun _ : ℕ => (1 : ℝ)) := funext hunit
    rw [heq]
    exact tendsto_const_nhds
  have hn : ‖x‖ = 1 := tendsto_nhds_unique hnormconv hnormunit
  simp [hx] at hn

/-- The source Gram admits a unit approximate-zero sequence whose
values do not converge strongly to any L² vector. -/
theorem sourceGram_exists_approximate_zero_without_strong_limit
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Tendsto (fun n : ℕ => gram lam alpha hlam ha (u n))
        atTop (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      (∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
        ¬ Tendsto u atTop (nhds f)) := by
  obtain ⟨u, hunit, himage⟩ :=
    gram_exists_unit_approximate_zero_eigenvectors lam alpha hlam ha
  have hzero :
      (gram lam alpha hlam ha).ker =
        (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :=
    (source_gram_zero_continuous_spectrum lam alpha hlam ha).2.1
  refine ⟨u, hunit, himage, ?_⟩
  exact unit_approximate_null_no_strong_limit
    (gram lam alpha hlam ha) (LinearMap.ker_eq_bot.mp hzero)
      u hunit himage

/-- The Fock output Gram admits a unit approximate-zero sequence
without any strong limit in the full Fock coefficient Hilbert space. -/
theorem outputGram_exists_approximate_zero_without_strong_limit
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ v : ℕ → InfiniteAnalysis.FockCoefficients,
      (∀ n : ℕ, ‖v n‖ = 1) ∧
      Tendsto (fun n : ℕ => outputGram lam alpha hlam ha (v n))
        atTop (nhds (0 : InfiniteAnalysis.FockCoefficients)) ∧
      (∀ F : InfiniteAnalysis.FockCoefficients,
        ¬ Tendsto v atTop (nhds F)) := by
  obtain ⟨v, hunit, himage⟩ :=
    outputGram_exists_unit_approximate_zero_eigenvectors lam alpha hlam ha
  have hzero :
      (outputGram lam alpha hlam ha).ker =
        (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients) :=
    (output_gram_zero_continuous_spectrum lam alpha hlam ha).2.1
  refine ⟨v, hunit, himage, ?_⟩
  exact unit_approximate_null_no_strong_limit
    (outputGram lam alpha hlam ha) (LinearMap.ker_eq_bot.mp hzero)
      v hunit himage

/-- Both actual Gram operators have normalized approximate-zero
sequences with no strong limit in their distinct source/target spaces. -/
theorem two_sided_gram_approximate_zero_without_strong_limits
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Tendsto (fun n : ℕ => gram lam alpha hlam ha (u n))
        atTop (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      (∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
        ¬ Tendsto u atTop (nhds f))) ∧
    (∃ v : ℕ → InfiniteAnalysis.FockCoefficients,
      (∀ n : ℕ, ‖v n‖ = 1) ∧
      Tendsto (fun n : ℕ => outputGram lam alpha hlam ha (v n))
        atTop (nhds (0 : InfiniteAnalysis.FockCoefficients)) ∧
      (∀ F : InfiniteAnalysis.FockCoefficients,
        ¬ Tendsto v atTop (nhds F))) :=
  ⟨sourceGram_exists_approximate_zero_without_strong_limit lam alpha hlam ha,
    outputGram_exists_approximate_zero_without_strong_limit lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_exists_approximate_zero_without_strong_limit
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_exists_approximate_zero_without_strong_limit
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_approximate_zero_without_strong_limits

end GegenbauerFock.GeneralUltrasphericalFock
