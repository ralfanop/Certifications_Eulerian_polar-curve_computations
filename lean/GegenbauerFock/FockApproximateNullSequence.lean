import GegenbauerFock.FockInverseInstability

/-!
# V007 — normalized approximate null sequence of the genuine Fock transform

The actual compact, injective Gegenbauer--Fock map has a dense,
nonclosed range. Its inverse is not bounded below. This file
upgrades arbitrary badly conditioned vectors to *unit vectors*,
then obtains a sequence of unit sources whose output norm
decreases below 1/(n+1).

These vectors are approximate null vectors, NOT genuine elements
of the kernel: C remains injective.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- For any finite inverse-conditioning constant K, a *unit*
ultraspherical source vector violates the corresponding lower bound. -/
theorem C_unit_vector_no_lower_bound
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (K : ℝ≥0) :
    ∃ g : Lp ℂ 2 (Ultraspherical.measure lam),
      ‖g‖ = 1 ∧ (K : ℝ) * ‖C lam alpha hlam ha g‖ < 1 := by
  obtain ⟨f, hf⟩ :=
    C_no_uniform_lower_norm_bound lam alpha hlam ha K
  have hfpos : 0 < ‖f‖ := by
    have hnonneg : 0 ≤ (K : ℝ) * ‖C lam alpha hlam ha f‖ :=
      mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _)
    exact lt_of_le_of_lt hnonneg hf
  have h_inv_pos : 0 < (‖f‖ : ℝ)⁻¹ := inv_pos.mpr hfpos
  let g : Lp ℂ 2 (Ultraspherical.measure lam) :=
    ((‖f‖⁻¹ : ℝ) : ℂ) • f
  have h_norm_scale : ‖((‖f‖⁻¹ : ℝ) : ℂ)‖ = ‖f‖⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h_inv_pos]
  have hg_norm : ‖g‖ = 1 := by
    dsimp [g]
    rw [norm_smul, h_norm_scale]
    exact inv_mul_cancel₀ (ne_of_gt hfpos)
  have hg_output : ‖C lam alpha hlam ha g‖ =
      ‖f‖⁻¹ * ‖C lam alpha hlam ha f‖ := by
    dsimp [g]
    rw [map_smul, norm_smul, h_norm_scale]
  refine ⟨g, hg_norm, ?_⟩
  rw [hg_output]
  calc
    (K : ℝ) * (‖f‖⁻¹ * ‖C lam alpha hlam ha f‖) =
        ‖f‖⁻¹ * ((K : ℝ) * ‖C lam alpha hlam ha f‖) := by ring
    _ < ‖f‖⁻¹ * ‖f‖ := mul_lt_mul_of_pos_left hf h_inv_pos
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hfpos)

/-- Arbitrarily small Fock image norm on the unit sphere:
a normalized approximate-null family with explicit 1/(n+1) bound. -/
theorem C_unit_approximate_null_vector
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (n : ℕ) :
    ∃ f : Lp ℂ 2 (Ultraspherical.measure lam),
      ‖f‖ = 1 ∧
        ‖C lam alpha hlam ha f‖ < 1 / ((n : ℝ) + 1) := by
  obtain ⟨f, hunit, hbound⟩ :=
    C_unit_vector_no_lower_bound lam alpha hlam ha
      (K := (n + 1 : ℝ≥0))
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine ⟨f, hunit, ?_⟩
  apply (lt_div_iff₀ hnpos).2
  convert hbound using 1 <;> norm_cast

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_unit_vector_no_lower_bound
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_unit_approximate_null_vector

end GegenbauerFock.GeneralUltrasphericalFock
