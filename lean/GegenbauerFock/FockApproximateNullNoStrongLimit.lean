import GegenbauerFock.FockApproximateNullConvergence

/-!
# V007 — no strong limit for normalized approximate null vectors

For λ,α>0 there exists a sequence of genuine L² source vectors of
constant norm one whose images under the compact injective
Gegenbauer--Fock map converge strongly to zero in the coefficient
Hilbert space.

Such a sequence cannot have a strong L² limit: continuity would force
a limit vector into ker(C)={0}, but the constant unit norms force its
norm to be one. This expresses severe inverse ill-posedness without
incorrectly asserting the existence of a nonzero kernel vector.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- A normalized approximate-null sequence whose images converge to
zero in Fock coefficients, but which has no strong limit in source L². -/
theorem C_exists_approximate_null_sequence_without_strong_limit
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Tendsto (fun n : ℕ => C lam alpha hlam ha (u n))
        atTop (𝓝 (0 : InfiniteAnalysis.FockCoefficients)) ∧
      (∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
        ¬ Tendsto u atTop (𝓝 f)) := by
  obtain ⟨u, hunit, himage⟩ :=
    C_exists_normalized_approximate_null_sequence lam alpha hlam ha
  refine ⟨u, hunit, himage, ?_⟩
  intro f hconv
  have hCconv : Tendsto
      (fun n : ℕ => C lam alpha hlam ha (u n))
      atTop (𝓝 (C lam alpha hlam ha f)) :=
    (C lam alpha hlam ha).continuous.continuousAt.tendsto.comp hconv
  have hCzero : C lam alpha hlam ha f = 0 :=
    tendsto_nhds_unique hCconv himage
  have hfzero : f = 0 := by
    apply C_injective lam alpha hlam ha
    simpa using hCzero
  have hnormconv : Tendsto (fun n : ℕ => ‖u n‖)
      atTop (𝓝 ‖f‖) := hconv.norm
  have hnormunit : Tendsto (fun n : ℕ => ‖u n‖)
      atTop (𝓝 (1 : ℝ)) := by
    have heq : (fun n : ℕ => ‖u n‖) =
        (fun _ : ℕ => (1 : ℝ)) := funext hunit
    rw [heq]
    exact tendsto_const_nhds
  have hnormf : ‖f‖ = 1 := tendsto_nhds_unique hnormconv hnormunit
  simp [hfzero] at hnormf

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_exists_approximate_null_sequence_without_strong_limit

end GegenbauerFock.GeneralUltrasphericalFock
