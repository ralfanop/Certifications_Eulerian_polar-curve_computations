import GegenbauerFock.FockApproximateNullConvergence
import GegenbauerFock.GeneralUltrasphericalFock

/-!
# V007 — approximate zero spectrum of the genuine source Gram

The true Hilbert Gram G = C†C is positive, compact and injective.
Nevertheless it has a normalized approximate-null sequence, obtained
by applying the bounded Hilbert adjoint to the already certified
normalized approximate-null source vectors for C.

This concerns the genuine infinite ultraspherical L² space, not
a finite truncation; zero is an approximate eigenvalue but not an
eigenvalue of G (the latter already certified separately).
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- There is a sequence of unit L² vectors whose images under the
genuine compact source Gram C†C converge strongly to zero. -/
theorem gram_exists_unit_approximate_zero_eigenvectors
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Tendsto (fun n : ℕ => gram lam alpha hlam ha (u n))
        atTop (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) := by
  obtain ⟨u, hunit, himage⟩ :=
    C_exists_normalized_approximate_null_sequence lam alpha hlam ha
  refine ⟨u, hunit, ?_⟩
  change Tendsto
    (fun n : ℕ => C_adjoint lam alpha hlam ha
      (C lam alpha hlam ha (u n)))
    atTop (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam)))
  have hadjoint : Tendsto
    (fun n : ℕ => C_adjoint lam alpha hlam ha
      (C lam alpha hlam ha (u n)))
    atTop (nhds (C_adjoint lam alpha hlam ha
      (0 : InfiniteAnalysis.FockCoefficients))) :=
    (C_adjoint lam alpha hlam ha).continuous.continuousAt.tendsto.comp himage
  simpa using hadjoint

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_exists_unit_approximate_zero_eigenvectors

end GegenbauerFock.GeneralUltrasphericalFock
