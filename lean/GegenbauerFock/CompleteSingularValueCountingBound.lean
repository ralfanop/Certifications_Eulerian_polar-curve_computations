import GegenbauerFock.CompleteSingularCountingBound

/-!
# V007 — quantitative multiplicity bound for actual singular values

For the genuine compact Gegenbauer--Fock transform, the complete
two-sided singular Hilbert system is indexed with multiplicities.
The positive singular values sigma_i = sqrt(mu_i) obey a sharp
trace-counting estimate at every positive singular threshold:
  delta² * #{i : sigma_i >= delta} <= unregularized Kummer trace.

No arbitrary finite truncations or surjectivity of C are assumed.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

theorem exists_complete_singular_value_counting_bound
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (u : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (v : HilbertBasis ι ℂ InfiniteAnalysis.FockCoefficients)
      (sigma : ι → ℝ),
      (∀ i, 0 < sigma i) ∧
      Summable (fun i : ι => sigma i ^ 2) ∧
      (∑' i : ι, sigma i ^ 2) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ i, C lam alpha hlam ha (u i) =
        (sigma i : ℂ) • v i) ∧
      (∀ i, C_adjoint lam alpha hlam ha (v i) =
        (sigma i : ℂ) • u i) ∧
      (∀ delta : ℝ, 0 < delta →
        ∃ s : Finset ι,
          (∀ i, i ∈ s ↔ delta ≤ sigma i) ∧
          (s.card : ℝ) * delta ^ 2 ≤
            KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) := by
  classical
  obtain ⟨ι, u, v, mu, hp, hsum, hK, hC, hAdj⟩ :=
    exists_complete_positive_singular_hilbert_bases_kummer lam alpha hlam ha
  let sigma : ι → ℝ := fun i => Real.sqrt (mu i)
  have hsigma (i : ι) : sigma i ^ 2 = mu i :=
    Real.sq_sqrt (hp i).le
  have heq : (fun i : ι => sigma i ^ 2) = mu := funext hsigma
  refine ⟨ι, u, v, sigma, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Real.sqrt_pos.2 (hp i)
  · rw [heq]
    exact hsum
  · rw [heq]
    exact hK
  · intro i
    exact hC i
  · intro i
    exact hAdj i
  · intro delta hdelta
    obtain ⟨s, hmem, hbound⟩ :=
      finite_threshold_count_le_tsum
        mu (fun i => (hp i).le) hsum (delta ^ 2)
        (sq_pos_of_pos hdelta)
    refine ⟨s, ?_, ?_⟩
    · intro i
      change i ∈ s ↔ delta ≤ Real.sqrt (mu i)
      rw [hmem i]
      exact (Real.le_sqrt' hdelta).symm
    · simpa only [hK] using hbound

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_complete_singular_value_counting_bound

end GegenbauerFock.GeneralUltrasphericalFock
