import GegenbauerFock.CompletePositiveSingularHilbertBasis

/-!
# V007 — quantitative singular-mode count from the exact Kummer trace

For a complete positive singular Hilbert family of the genuine
Gegenbauer--Fock compact operator, the number of Gram eigenmodes
with mu_i >= epsilon is finite and obeys
  epsilon * card {i : epsilon <= mu_i} <= Kummer mass.
All multiplicities are counted by the common Hilbert index.
No spectral ordering, truncation or global C inverse is assumed.
-/

noncomputable section
open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- A summable family of nonnegative real numbers has an exact
finite spectral threshold set and a trace-counting inequality. -/
theorem finite_threshold_count_le_tsum
    {ι : Type*} (mu : ι → ℝ)
    (hnonneg : ∀ i, 0 ≤ mu i) (hs : Summable mu)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ s : Finset ι,
      (∀ i, i ∈ s ↔ eps ≤ mu i) ∧
      (s.card : ℝ) * eps ≤ ∑' i, mu i := by
  classical
  have hf : {i : ι | eps ≤ mu i}.Finite := by
    simpa using hs.tendsto_cofinite_zero.eventually_lt_const heps
  let s : Finset ι := hf.toFinset
  have hsmem (i : ι) : i ∈ s ↔ eps ≤ mu i := by
    simp [s]
  refine ⟨s, hsmem, ?_⟩
  calc
    (s.card : ℝ) * eps = ∑ i ∈ s, eps := by simp
    _ ≤ ∑ i ∈ s, mu i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hsmem i).mp hi
    _ ≤ ∑' i, mu i :=
      sum_le_hasSum s (fun i hi => hnonneg i) hs.hasSum

/-- The genuine compact bilateral singular system has a
multiplicity-counting bound controlled by the SAME exact
unregularized Kummer trace for every positive Gram threshold. -/
theorem exists_complete_singular_kummer_counting_bound
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (u : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (v : HilbertBasis ι ℂ InfiniteAnalysis.FockCoefficients)
      (mu : ι → ℝ),
      (∀ i, 0 < mu i) ∧
      (∀ i, C lam alpha hlam ha (u i) =
        (Real.sqrt (mu i) : ℂ) • v i) ∧
      (∀ i, C_adjoint lam alpha hlam ha (v i) =
        (Real.sqrt (mu i) : ℂ) • u i) ∧
      (∑' i : ι, mu i) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ eps : ℝ, 0 < eps →
        ∃ s : Finset ι, (∀ i, i ∈ s ↔ eps ≤ mu i) ∧
          (s.card : ℝ) * eps ≤
            KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) := by
  classical
  obtain ⟨ι, u, v, mu, hp, hs, hK, hC, hAdj⟩ :=
    exists_complete_positive_singular_hilbert_bases_kummer lam alpha hlam ha
  refine ⟨ι, u, v, mu, hp, hC, hAdj, hK, ?_⟩
  intro eps heps
  obtain ⟨s, hmem, hbound⟩ :=
    finite_threshold_count_le_tsum mu (fun i => (hp i).le) hs eps heps
  exact ⟨s, hmem, by simpa only [hK] using hbound⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.finite_threshold_count_le_tsum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_complete_singular_kummer_counting_bound

end GegenbauerFock.GeneralUltrasphericalFock
