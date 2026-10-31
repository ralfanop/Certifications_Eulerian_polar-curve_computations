import GegenbauerFock.CompletePositiveSingularHilbertBasis

/-!
# V007 — direct square summability of the genuine singular values

The unregularized Kummer identity is here expressed for the actual
positive singular values sigma_i = sqrt(mu_i), rather than the Gram
eigenvalues mu_i. This is the spectral S₂ mass with multiplicities;
the source and target Hilbert spaces and the C, C† equations are
genuine, and there is no finite-rank or surjectivity assumption.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The rectangular Gegenbauer–Fock transform admits matched
complete source and output singular Hilbert bases, with positive
REAL singular values whose squares are summable and whose exact
square sum is the same unregularized Kummer function. -/
theorem exists_complete_singular_values_squared_sum_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (u : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (v : HilbertBasis ι ℂ InfiniteAnalysis.FockCoefficients)
      (sigma : ι → ℝ),
      (∀ i, 0 < sigma i) ∧
      Summable (fun i : ι => sigma i ^ 2) ∧
      (∑' i : ι, sigma i ^ 2) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ i, C lam alpha hlam ha (u i) = (sigma i : ℂ) • v i) ∧
      (∀ i, C_adjoint lam alpha hlam ha (v i) = (sigma i : ℂ) • u i) := by
  classical
  obtain ⟨ι, u, v, mu, hmu, hsum, hK, hC, hAdj⟩ :=
    exists_complete_positive_singular_hilbert_bases_kummer lam alpha hlam ha
  let sigma : ι → ℝ := fun i => Real.sqrt (mu i)
  have hsigma (i : ι) : sigma i ^ 2 = mu i :=
    Real.sq_sqrt (hmu i).le
  have heq : (fun i : ι => sigma i ^ 2) = mu := funext hsigma
  refine ⟨ι, u, v, sigma, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Real.sqrt_pos.2 (hmu i)
  · simpa only [heq] using hsum
  · rw [heq]
    exact hK
  · intro i
    exact hC i
  · intro i
    exact hAdj i

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_complete_singular_values_squared_sum_kummer

end GegenbauerFock.GeneralUltrasphericalFock
