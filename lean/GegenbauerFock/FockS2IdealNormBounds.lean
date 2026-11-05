import GegenbauerFock.FockHilbertSchmidtNorm

/-!
# V007: quantitative ideal inequalities in the true S₂ energy norm

This module upgrades previously certified square-energy bounds to
Schatten-S₂ *norm* inequalities. It uses the basis-independent Fock
S₂ norm of the preceding module, and proves the two-sided inequality
on every complete input Hilbert basis even when the post-composition
target is an arbitrary complete complex Hilbert space.

The stronger assertion that a universal Schatten ideal Banach API is
available in the pinned Mathlib is not made here.
-/

noncomputable section

namespace GegenbauerFock.FockEnergy

open MeasureTheory

/-- Genuine right-ideal Hilbert–Schmidt norm inequality for every
bounded Fock-target map with summable rows and every bounded
endomorphism of the probability L² source. -/
theorem s2Norm_comp_right_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (T : Lp ℂ 2 μ →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hT : HasSummableRows μ T)
    (B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    s2Norm (T.comp B) (summableRows_comp_right μ T hT B) ≤
      ‖B‖ * s2Norm T hT := by
  have ht : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row T n‖ ^ 2) := hT
  have htb : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row (T.comp B) n‖ ^ 2) :=
    summableRows_comp_right μ T hT B
  have hrow (n : ℕ) :
      ‖SummableRowsCompact.row (T.comp B) n‖ ^ 2 ≤
        ‖B‖ ^ 2 * ‖SummableRowsCompact.row T n‖ ^ 2 := by
    change ‖(coordinate n).comp (T.comp B)‖ ^ 2 ≤
      ‖B‖ ^ 2 * ‖(coordinate n).comp T‖ ^ 2
    exact row_comp_right_norm_sq_le μ T B n
  have hsum :
      (∑' n : ℕ, ‖SummableRowsCompact.row (T.comp B) n‖ ^ 2) ≤
      ‖B‖ ^ 2 * (∑' n : ℕ,
        ‖SummableRowsCompact.row T n‖ ^ 2) := by
    calc
      _ ≤ ∑' n : ℕ,
          ‖B‖ ^ 2 * ‖SummableRowsCompact.row T n‖ ^ 2 :=
        htb.tsum_le_tsum hrow (ht.mul_left (‖B‖ ^ 2))
      _ = ‖B‖ ^ 2 *
            (∑' n : ℕ, ‖SummableRowsCompact.row T n‖ ^ 2) :=
        tsum_mul_left
  have hsq :
      (s2Norm (T.comp B) htb) ^ 2 ≤
        (‖B‖ * s2Norm T ht) ^ 2 := by
    calc
      _ = ∑' n : ℕ,
          ‖SummableRowsCompact.row (T.comp B) n‖ ^ 2 :=
        s2Norm_sq_eq_rowEnergy (T.comp B) htb
      _ ≤ ‖B‖ ^ 2 *
          (∑' n : ℕ, ‖SummableRowsCompact.row T n‖ ^ 2) := hsum
      _ = (‖B‖ * s2Norm T ht) ^ 2 := by
        rw [mul_pow, s2Norm_sq_eq_rowEnergy]
  exact (sq_le_sq₀
    (s2Norm_nonneg (T.comp B) htb)
    (mul_nonneg (norm_nonneg B) (s2Norm_nonneg T ht))).mp hsq

/-- True quantitative TWO-SIDED Hilbert–Schmidt norm estimate computed
on *any* complete input Hilbert basis; the left postprocessing map
may take values in an arbitrary complete complex Hilbert space G.
Membership of the composite in S₂ follows separately from the
already certified `summableRows_twoSided_IsHS`. -/
theorem s2Norm_twoSided_basis_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (T : Lp ℂ 2 μ →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hT : HasSummableRows μ T)
    (B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : InfiniteAnalysis.FockCoefficients →L[ℂ] G)
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) :
    Real.sqrt (∑' i : ι, ‖(A.comp (T.comp B)) (b i)‖ ^ 2) ≤
      ‖A‖ * ‖B‖ * s2Norm T hT := by
  have ht : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row T n‖ ^ 2) := hT
  have hsum := summableRows_twoSided_basis_energy_le μ T hT B A b
  have hsq :
      (Real.sqrt (∑' i : ι, ‖(A.comp (T.comp B)) (b i)‖ ^ 2)) ^ 2 ≤
        (‖A‖ * ‖B‖ * s2Norm T ht) ^ 2 := by
    calc
      _ = ∑' i : ι, ‖(A.comp (T.comp B)) (b i)‖ ^ 2 :=
        Real.sq_sqrt (tsum_nonneg (fun _ => sq_nonneg _))
      _ ≤ ‖A‖ ^ 2 * ‖B‖ ^ 2 *
            (∑' n : ℕ, ‖SummableRowsCompact.row T n‖ ^ 2) := hsum
      _ = (‖A‖ * ‖B‖ * s2Norm T ht) ^ 2 := by
        rw [← s2Norm_sq_eq_rowEnergy T ht]
        ring
  exact (sq_le_sq₀
    (Real.sqrt_nonneg _)
    (mul_nonneg (mul_nonneg (norm_nonneg A) (norm_nonneg B))
      (s2Norm_nonneg T ht))).mp hsq

#print axioms GegenbauerFock.FockEnergy.s2Norm_comp_right_le
#print axioms GegenbauerFock.FockEnergy.s2Norm_twoSided_basis_le

end GegenbauerFock.FockEnergy
