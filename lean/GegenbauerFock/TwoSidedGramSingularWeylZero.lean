import GegenbauerFock.TwoSidedGramWeakConvergence

/-!
# V007 — singular Weyl sequences at zero for both true Grams

A *singular Weyl sequence at zero* consists of unit vectors whose
images under the operator converge strongly to zero, while the vectors
themselves converge weakly to zero against ALL Hilbert test vectors.

This is the sequence-level criterion relevant to the essential
spectrum of a selfadjoint operator. Here it is formalized as an
explicit predicate, without claiming an unproved equivalence to any
particular Mathlib definition of essential spectrum.

Source and output Grams act on different Hilbert spaces; both are
genuine infinite-dimensional endomorphisms, not finite truncations.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- An explicitly test-vector-formulated singular Weyl sequence at zero.
The third condition is full weak convergence, not just a dense test
family. -/
def IsSingularWeylSequenceAtZero
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (u : ℕ → H) : Prop :=
  (∀ n : ℕ, ‖u n‖ = 1) ∧
  Tendsto (fun n : ℕ => T (u n)) atTop (nhds (0 : H)) ∧
  (∀ x : H, Tendsto (fun n : ℕ => inner ℂ x (u n))
    atTop (nhds (0 : ℂ)))

/-- The actual source Gram C†C has a singular Weyl sequence at zero,
without a zero eigenvector and without identifying Hilbert spaces. -/
theorem sourceGram_has_singular_weyl_sequence_at_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      IsSingularWeylSequenceAtZero (gram lam alpha hlam ha) u := by
  obtain ⟨u, hu, hGu, hw⟩ :=
    sourceGram_unit_approximate_zero_weakly_null lam alpha hlam ha
  exact ⟨u, ⟨hu, hGu, hw⟩⟩

/-- The actual output Gram CC† has a singular Weyl sequence at zero
in the full Gaussian-Fock coefficient Hilbert space. -/
theorem outputGram_has_singular_weyl_sequence_at_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ v : ℕ → InfiniteAnalysis.FockCoefficients,
      IsSingularWeylSequenceAtZero (outputGram lam alpha hlam ha) v := by
  obtain ⟨v, hv, hGv, hw⟩ :=
    outputGram_unit_approximate_zero_weakly_null lam alpha hlam ha
  exact ⟨v, ⟨hv, hGv, hw⟩⟩

/-- Both true Grams simultaneously possess singular Weyl sequences
at zero in their respective distinct Hilbert spaces. -/
theorem two_sided_gram_has_singular_weyl_sequences_at_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      IsSingularWeylSequenceAtZero (gram lam alpha hlam ha) u) ∧
    (∃ v : ℕ → InfiniteAnalysis.FockCoefficients,
      IsSingularWeylSequenceAtZero (outputGram lam alpha hlam ha) v) :=
  ⟨sourceGram_has_singular_weyl_sequence_at_zero lam alpha hlam ha,
   outputGram_has_singular_weyl_sequence_at_zero lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_has_singular_weyl_sequence_at_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_has_singular_weyl_sequence_at_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_has_singular_weyl_sequences_at_zero

end GegenbauerFock.GeneralUltrasphericalFock
