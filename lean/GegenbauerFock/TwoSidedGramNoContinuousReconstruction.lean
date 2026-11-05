import GegenbauerFock.OutputGramApproximateZeroSpectrum

/-!
# V007 — no continuous exact reconstruction for either compact Gram

Even a nonlinear reconstruction map defined on the entire ambient
Hilbert space cannot simultaneously invert an actual Gram on its
range and be continuous at zero. The normalized approximate-null
sequences provide a direct contradiction with continuous recovery:
inputs stay on the unit sphere while Gram data tend to zero.

This theorem is about the genuine infinite-dimensional source and
output Grams in two different Hilbert spaces. No finite truncation,
unproved surjectivity, or identification of spaces is invoked.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- An operator with a unit approximate-null sequence does not
admit a globally defined exact left inverse continuous at zero,
even when the proposed reconstruction is nonlinear. -/
private theorem no_continuous_global_left_inverse_of_unit_approx_null
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H)
    (u : ℕ → H)
    (hunit : ∀ n : ℕ, ‖u n‖ = 1)
    (himage : Tendsto (fun n : ℕ => T (u n))
      atTop (nhds (0 : H)))
    (r : H → H)
    (hleft : ∀ x : H, r (T x) = x) :
    ¬ ContinuousAt r (0 : H) := by
  intro hcont
  have hrec : Tendsto
      (fun n : ℕ => r (T (u n)))
      atTop (nhds (r (0 : H))) :=
    hcont.tendsto.comp himage
  have heq : (fun n : ℕ => r (T (u n))) = u := by
    funext n
    exact hleft (u n)
  rw [heq] at hrec
  have hrzero : r (0 : H) = 0 := by
    simpa using hleft (0 : H)
  rw [hrzero] at hrec
  have hnormzero : Tendsto (fun n : ℕ => ‖u n‖)
      atTop (nhds (0 : ℝ)) := by
    simpa using hrec.norm
  have hnormone : Tendsto (fun n : ℕ => ‖u n‖)
      atTop (nhds (1 : ℝ)) := by
    have heqnorm : (fun n : ℕ => ‖u n‖) = (fun _ : ℕ => (1 : ℝ)) :=
      funext hunit
    rw [heqnorm]
    exact tendsto_const_nhds
  have himpossible : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hnormzero hnormone
  norm_num at himpossible

/-- No globally defined (even nonlinear) source-Gram reconstruction,
exact on Ran(C†C), can be continuous at zero. -/
theorem sourceGram_no_continuous_global_left_inverse_at_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (r : Lp ℂ 2 (Ultraspherical.measure lam) →
      Lp ℂ 2 (Ultraspherical.measure lam))
    (hleft : ∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
      r (gram lam alpha hlam ha f) = f) :
    ¬ ContinuousAt r (0 : Lp ℂ 2 (Ultraspherical.measure lam)) := by
  obtain ⟨u, hunit, himage⟩ :=
    gram_exists_unit_approximate_zero_eigenvectors lam alpha hlam ha
  exact no_continuous_global_left_inverse_of_unit_approx_null
    (gram lam alpha hlam ha) u hunit himage r hleft

/-- No globally defined (even nonlinear) output-Gram reconstruction,
exact on Ran(CC†), can be continuous at zero. -/
theorem outputGram_no_continuous_global_left_inverse_at_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (r : InfiniteAnalysis.FockCoefficients →
      InfiniteAnalysis.FockCoefficients)
    (hleft : ∀ F : InfiniteAnalysis.FockCoefficients,
      r (outputGram lam alpha hlam ha F) = F) :
    ¬ ContinuousAt r (0 : InfiniteAnalysis.FockCoefficients) := by
  obtain ⟨v, hunit, himage⟩ :=
    outputGram_exists_unit_approximate_zero_eigenvectors lam alpha hlam ha
  exact no_continuous_global_left_inverse_of_unit_approx_null
    (outputGram lam alpha hlam ha) v hunit himage r hleft

/-- Neither source nor output Gram admits an everywhere-defined,
continuous, exact reconstruction on its ambient Hilbert space. -/
theorem two_sided_gram_no_continuous_global_reconstruction
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (¬ ∃ r : Lp ℂ 2 (Ultraspherical.measure lam) →
        Lp ℂ 2 (Ultraspherical.measure lam),
        Continuous r ∧
          ∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
            r (gram lam alpha hlam ha f) = f) ∧
    (¬ ∃ r : InfiniteAnalysis.FockCoefficients →
        InfiniteAnalysis.FockCoefficients,
        Continuous r ∧
          ∀ F : InfiniteAnalysis.FockCoefficients,
            r (outputGram lam alpha hlam ha F) = F) := by
  constructor
  · rintro ⟨r, hcont, hleft⟩
    exact sourceGram_no_continuous_global_left_inverse_at_zero
      lam alpha hlam ha r hleft hcont.continuousAt
  · rintro ⟨r, hcont, hleft⟩
    exact outputGram_no_continuous_global_left_inverse_at_zero
      lam alpha hlam ha r hleft hcont.continuousAt

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_no_continuous_global_left_inverse_at_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_no_continuous_global_left_inverse_at_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_no_continuous_global_reconstruction

end GegenbauerFock.GeneralUltrasphericalFock
