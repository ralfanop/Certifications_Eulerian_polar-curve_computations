import GegenbauerFock.TwoSidedGramInverseInstability
import GegenbauerFock.GramApproximateZeroSpectrum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# V007 — normalized approximate zero spectrum on both Hilbert sides

The source Gram already has a normalized approximate-null sequence.
Here we construct one independently for the output Gram CC† from its
quantitatively unbounded inverse on the dense, nonclosed range.
Both sequences refer to genuine infinite-dimensional Hilbert operators.
Zero is NOT asserted to be a genuine eigenvalue in either space.
-/

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- For any finite candidate inverse bound K, the full output Gram
has a unit Fock vector whose image violates that bound. -/
theorem outputGram_unit_vector_no_lower_bound
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (K : ℝ≥0) :
    ∃ g : InfiniteAnalysis.FockCoefficients,
      ‖g‖ = 1 ∧ (K : ℝ) * ‖outputGram lam alpha hlam ha g‖ < 1 := by
  obtain ⟨f, hf⟩ :=
    outputGram_inverse_unbounded_on_range lam alpha hlam ha K
  have hfpos : 0 < ‖f‖ := by
    have hnonneg : 0 ≤ (K : ℝ) * ‖outputGram lam alpha hlam ha f‖ :=
      mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _)
    exact lt_of_le_of_lt hnonneg hf
  have h_inv_pos : 0 < (‖f‖ : ℝ)⁻¹ := inv_pos.mpr hfpos
  let z : ℂ := ((‖f‖⁻¹ : ℝ) : ℂ)
  let g : InfiniteAnalysis.FockCoefficients := z • f
  have h_norm_scale : ‖z‖ = ‖f‖⁻¹ := by
    dsimp [z]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h_inv_pos]
  have hg_norm : ‖g‖ = 1 := by
    change ‖z • f‖ = 1
    calc
      ‖z • f‖ = ‖z‖ * ‖f‖ := norm_smul z f
      _ = ‖f‖⁻¹ * ‖f‖ := by rw [h_norm_scale]
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hfpos)
  have hg_output : ‖outputGram lam alpha hlam ha g‖ =
      ‖f‖⁻¹ * ‖outputGram lam alpha hlam ha f‖ := by
    change ‖outputGram lam alpha hlam ha (z • f)‖ = _
    calc
      ‖outputGram lam alpha hlam ha (z • f)‖ =
          ‖z • outputGram lam alpha hlam ha f‖ := by rw [map_smul]
      _ = ‖z‖ * ‖outputGram lam alpha hlam ha f‖ := norm_smul z _
      _ = ‖f‖⁻¹ * ‖outputGram lam alpha hlam ha f‖ := by rw [h_norm_scale]
  refine ⟨g, hg_norm, ?_⟩
  rw [hg_output]
  calc
    (K : ℝ) * (‖f‖⁻¹ * ‖outputGram lam alpha hlam ha f‖) =
        ‖f‖⁻¹ * ((K : ℝ) * ‖outputGram lam alpha hlam ha f‖) := by ring
    _ < ‖f‖⁻¹ * ‖f‖ := mul_lt_mul_of_pos_left hf h_inv_pos
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hfpos)

/-- A unit output vector with Gram norm below 1/(n+1). -/
theorem outputGram_unit_approximate_zero_vector
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (n : ℕ) :
    ∃ F : InfiniteAnalysis.FockCoefficients,
      ‖F‖ = 1 ∧
      ‖outputGram lam alpha hlam ha F‖ < 1 / ((n : ℝ) + 1) := by
  obtain ⟨F, hunit, hsmall⟩ :=
    outputGram_unit_vector_no_lower_bound lam alpha hlam ha
      (K := (n + 1 : ℝ≥0))
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine ⟨F, hunit, ?_⟩
  have hcast : ((n + 1 : ℝ≥0) : ℝ) = (n : ℝ) + 1 := by
    norm_cast
  rw [hcast] at hsmall
  apply (lt_div_iff₀ hnpos).2
  calc
    ‖outputGram lam alpha hlam ha F‖ * ((n : ℝ) + 1) =
      ((n : ℝ) + 1) * ‖outputGram lam alpha hlam ha F‖ := by ring
    _ < 1 := hsmall

/-- A normalized output approximate-zero Gram sequence converges
strongly to zero after application of CC†, but stays of unit norm. -/
theorem outputGram_exists_unit_approximate_zero_eigenvectors
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → InfiniteAnalysis.FockCoefficients,
      (∀ n : ℕ, ‖u n‖ = 1) ∧
      Tendsto (fun n : ℕ => outputGram lam alpha hlam ha (u n))
        atTop (nhds (0 : InfiniteAnalysis.FockCoefficients)) := by
  classical
  choose u hunit hsmall using
    (fun n : ℕ => outputGram_unit_approximate_zero_vector lam alpha hlam ha n)
  refine ⟨u, hunit, ?_⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero
    (fun n : ℕ => norm_nonneg (outputGram lam alpha hlam ha (u n)))
    (fun n : ℕ => (hsmall n).le)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Two genuine normalized approximate-zero Gram sequences,
one in ultraspherical L² and one in Gaussian–Fock coefficients. -/
theorem two_sided_gram_normalized_approximate_zero_sequences
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
        Tendsto (fun n : ℕ => gram lam alpha hlam ha (u n))
          atTop (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam)))) ∧
    (∃ v : ℕ → InfiniteAnalysis.FockCoefficients,
      (∀ n : ℕ, ‖v n‖ = 1) ∧
        Tendsto (fun n : ℕ => outputGram lam alpha hlam ha (v n))
          atTop (nhds (0 : InfiniteAnalysis.FockCoefficients))) :=
  ⟨gram_exists_unit_approximate_zero_eigenvectors lam alpha hlam ha,
   outputGram_exists_unit_approximate_zero_eigenvectors lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_unit_vector_no_lower_bound
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_unit_approximate_zero_vector
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_exists_unit_approximate_zero_eigenvectors
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_normalized_approximate_zero_sequences

end GegenbauerFock.GeneralUltrasphericalFock
