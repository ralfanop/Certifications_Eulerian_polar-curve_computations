import GegenbauerFock.OutputGramApproximateZeroSpectrum
import Mathlib.Topology.Constructions

/-!
# V007 — exact inverses on the true Gram ranges are discontinuous at zero

This refines the earlier global-reconstruction obstruction. We equip
each *actual range* with its induced subtype topology, and consider a
reconstruction function r from this range back to the corresponding
Hilbert space, with r(G x)=x for every source x. A unit approximate-null
sequence maps to zero in the range topology, while its recovered inputs
stay on the unit sphere. Therefore r cannot be continuous at zero.

This result is about inverses whose DOMAIN IS THE RANGE; it makes no
assumption of a global extension to the entire ambient Hilbert space.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- On the genuine range subtype, any exact inverse of a bounded
Hilbert endomorphism with a unit approximate-null sequence is
discontinuous at zero. No global extension of the inverse is used. -/
private theorem inverse_on_range_discontinuous_at_zero
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H)
    (u : ℕ → H) (hunit : ∀ n : ℕ, ‖u n‖ = 1)
    (himage : Tendsto (fun n : ℕ => T (u n))
      atTop (nhds (0 : H)))
    (r : T.range → H)
    (hleft : ∀ x : H, r ⟨T x, ⟨x, rfl⟩⟩ = x) :
    ¬ ContinuousAt r (0 : T.range) := by
  intro hcont
  have hsub : Tendsto
      (fun n : ℕ => (⟨T (u n), ⟨u n, rfl⟩⟩ : T.range))
      atTop (nhds (0 : T.range)) := by
    apply tendsto_subtype_rng.mpr
    simpa using himage
  have hrec : Tendsto
      (fun n : ℕ => r (⟨T (u n), ⟨u n, rfl⟩⟩ : T.range))
      atTop (nhds (r (0 : T.range))) :=
    hcont.tendsto.comp hsub
  have heq :
      (fun n : ℕ => r (⟨T (u n), ⟨u n, rfl⟩⟩ : T.range)) = u := by
    funext n
    exact hleft (u n)
  rw [heq] at hrec
  have hrzero : r (0 : T.range) = 0 := by
    simpa using hleft (0 : H)
  rw [hrzero] at hrec
  have hnormzero : Tendsto (fun n : ℕ => ‖u n‖)
      atTop (nhds (0 : ℝ)) := by
    simpa using hrec.norm
  have hnormone : Tendsto (fun n : ℕ => ‖u n‖)
      atTop (nhds (1 : ℝ)) := by
    have heqnorm : (fun n : ℕ => ‖u n‖) =
        (fun _ : ℕ => (1 : ℝ)) := funext hunit
    rw [heqnorm]
    exact tendsto_const_nhds
  have hcontradiction : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hnormzero hnormone
  norm_num at hcontradiction

/-- The inverse of the source Gram, even defined only on the actual
dense proper range of C†C with induced topology, is discontinuous
at zero. This excludes nonlinear exact reconstructions as well. -/
theorem sourceGram_inverse_on_range_discontinuous_at_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (r : (gram lam alpha hlam ha).range →
      Lp ℂ 2 (Ultraspherical.measure lam))
    (hleft : ∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
      r ⟨gram lam alpha hlam ha f, ⟨f, rfl⟩⟩ = f) :
    ¬ ContinuousAt r (0 : (gram lam alpha hlam ha).range) := by
  obtain ⟨u, hunit, himage⟩ :=
    gram_exists_unit_approximate_zero_eigenvectors lam alpha hlam ha
  exact inverse_on_range_discontinuous_at_zero
    (gram lam alpha hlam ha) u hunit himage r hleft

/-- The inverse of the output Gram on its actual dense proper
Gaussian–Fock coefficient-space range is discontinuous at zero. -/
theorem outputGram_inverse_on_range_discontinuous_at_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (r : (outputGram lam alpha hlam ha).range →
      InfiniteAnalysis.FockCoefficients)
    (hleft : ∀ F : InfiniteAnalysis.FockCoefficients,
      r ⟨outputGram lam alpha hlam ha F, ⟨F, rfl⟩⟩ = F) :
    ¬ ContinuousAt r (0 : (outputGram lam alpha hlam ha).range) := by
  obtain ⟨u, hunit, himage⟩ :=
    outputGram_exists_unit_approximate_zero_eigenvectors lam alpha hlam ha
  exact inverse_on_range_discontinuous_at_zero
    (outputGram lam alpha hlam ha) u hunit himage r hleft

/-- The precise noncontinuity result for any exact inverses on their
respective range subtypes, without any hypothetical global extensions. -/
theorem two_sided_gram_inverse_on_ranges_discontinuous_at_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (rsource : (gram lam alpha hlam ha).range →
      Lp ℂ 2 (Ultraspherical.measure lam))
    (rout : (outputGram lam alpha hlam ha).range →
      InfiniteAnalysis.FockCoefficients)
    (hsource : ∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
      rsource ⟨gram lam alpha hlam ha f, ⟨f, rfl⟩⟩ = f)
    (hout : ∀ F : InfiniteAnalysis.FockCoefficients,
      rout ⟨outputGram lam alpha hlam ha F, ⟨F, rfl⟩⟩ = F) :
    (¬ ContinuousAt rsource (0 : (gram lam alpha hlam ha).range)) ∧
    (¬ ContinuousAt rout (0 : (outputGram lam alpha hlam ha).range)) :=
  ⟨sourceGram_inverse_on_range_discontinuous_at_zero lam alpha hlam ha rsource hsource,
   outputGram_inverse_on_range_discontinuous_at_zero lam alpha hlam ha rout hout⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_inverse_on_range_discontinuous_at_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_inverse_on_range_discontinuous_at_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_inverse_on_ranges_discontinuous_at_zero

end GegenbauerFock.GeneralUltrasphericalFock
