import GegenbauerFock.CompleteSingularSquareMass

/-!
# V007 — all real Schatten powers p >= 2 of the genuine singular system

The exact Hilbert--Schmidt square mass implies summability of all
higher real singular-value powers.  We prove the scalar majorant
using the actual square sum, not an assumed uniform singular bound.

The range 0 < p < 2 requires a stronger finite-rank approximation
estimate; the present theorem makes no claim in that range.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- A strictly positive square-summable family has summable real
p-th powers for every p >= 2.  No ordering of the index type is
needed, so eigenvalue multiplicities are fully retained. -/
theorem summable_real_powers_of_square_summable
    {ι : Type*} (sigma : ι → ℝ)
    (hpos : ∀ i, 0 < sigma i)
    (hsq : Summable (fun i : ι => sigma i ^ 2))
    (p : ℝ) (hp : 2 ≤ p) :
    Summable (fun i : ι => sigma i ^ p) := by
  classical
  let S : ℝ := ∑' i : ι, sigma i ^ 2
  let M : ℝ := max 1 S
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_max_left 1 S)
  have hbound (i : ι) : sigma i ≤ M := by
    have hle : sigma i ^ 2 ≤ S := by
      simpa [S] using
        (sum_le_hasSum ({i} : Finset ι)
          (fun j _ => sq_nonneg (sigma j)) hsq.hasSum)
    by_cases hsmall : sigma i ≤ 1
    · exact le_trans hsmall (le_max_left 1 S)
    · have hlarge : 1 < sigma i := lt_of_not_ge hsmall
      have hsqbound : sigma i ≤ sigma i ^ 2 := by nlinarith
      exact le_trans hsqbound (le_trans hle (le_max_right 1 S))
  have hq : 0 ≤ p - 2 := by linarith
  have hpowbound (i : ι) : sigma i ^ (p - 2) ≤ M ^ (p - 2) := by
    exact Real.rpow_le_rpow (hpos i).le (hbound i) hq
  have hpoint (i : ι) :
      sigma i ^ p ≤ M ^ (p - 2) * sigma i ^ 2 := by
    have heq : p = (p - 2) + 2 := by ring
    rw [heq, Real.rpow_add (hpos i), Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right (hpowbound i) (sq_nonneg (sigma i))
  have hmajor : Summable
      (fun i : ι => M ^ (p - 2) * sigma i ^ 2) := by
    exact hsq.mul_left _
  apply Summable.of_nonneg_of_le
  · intro i
    exact Real.rpow_nonneg (hpos i).le _
  · exact hpoint
  · exact hmajor

/-- True Gegenbauer--Fock singular Hilbert bases have a summable
p-th singular mass for every real p >= 2.  The same singular
system realizes the exact unregularized Kummer S₂ mass. -/
theorem exists_complete_singular_schatten_pge_two
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ (ι : Type)
      (u : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (v : HilbertBasis ι ℂ InfiniteAnalysis.FockCoefficients)
      (sigma : ι → ℝ),
      (∀ i, 0 < sigma i) ∧
      Summable (fun i : ι => sigma i ^ p) ∧
      (∑' i : ι, sigma i ^ 2) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ i, C lam alpha hlam ha (u i) = (sigma i : ℂ) • v i) ∧
      (∀ i, C_adjoint lam alpha hlam ha (v i) = (sigma i : ℂ) • u i) := by
  obtain ⟨ι, u, v, sigma, hpos, hsq, hK, hC, hAdj⟩ :=
    exists_complete_singular_values_squared_sum_kummer lam alpha hlam ha
  exact ⟨ι, u, v, sigma, hpos,
    summable_real_powers_of_square_summable sigma hpos hsq p hp,
    hK, hC, hAdj⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.summable_real_powers_of_square_summable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_complete_singular_schatten_pge_two

end GegenbauerFock.GeneralUltrasphericalFock
