import CriticalWindowDCT
import EulerianGrothendieck.FockVacuumProjection

/-! Identify the actual critical-window integral with the pre-existing
Hilbert-space Fock state and vacuum projection, not a newly defined reciprocal.
The only probabilistic premises are the original independent uniform variables. -/
namespace M12CriticalVacuum
open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology BigOperators
open M12CriticalPointwise M12CriticalDCT
open EulerianGrothendieck.Fock

theorem rE_eq_profile (z : ℂ) : rE z = M12FockDomination.fockProfile z := by
  by_cases hz : z = 0
  · rw [hz, rE_zero]; simp [M12FockDomination.fockProfile]
  · rw [rE_eq_sin_div hz, M12FockDomination.fockProfile, if_neg hz]

theorem density_kernel (M : ℕ) (a x y : ℝ) :
    ‖rE (⟨x,y⟩ : ℂ)^M‖^2 * fockDensity a ⟨x,y⟩ =
      (a/Real.pi)*M12CriticalAssembly.originalKernel M a x y := by
  rw [fockDensity, mk_norm_sq, norm_pow, ← pow_mul, mk_eq, rE_eq_profile]
  unfold M12CriticalAssembly.originalKernel
  rw [show M*2=2*M by omega]
  ring

theorem density_integrable (M : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℂ => ‖rE z ^ M‖^2 * fockDensity a z) := by
  refine (integrable_exp_abs_im_mul_fockDensity ha M).mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact (((continuous_rE.pow M).norm.pow 2).mul (continuous_fockDensity a)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (fockDensity_nonneg ha.le z))]
    exact mul_le_mul_of_nonneg_right (norm_rE_pow_sq_le z M) (fockDensity_nonneg ha.le z)

theorem original_eq_complex_integral (M : ℕ) {a : ℝ} (ha : 0 < a) :
    M12CriticalAssembly.originalFockNorm M a =
      ∫ z : ℂ, ‖rE z ^ M‖^2 * fockDensity a z := by
  let f := fun z : ℂ => ‖rE z ^ M‖^2 * fockDensity a z
  have hi : Integrable (fun p : ℝ × ℝ => f ⟨p.1,p.2⟩)
      ((volume : Measure ℝ).prod volume) :=
    (integrable_complex_iff_prod f).mp (density_integrable M ha)
  change _ = ∫ z : ℂ, f z
  rw [integral_complex_eq_prod]
  change _ = ∫ p : ℝ × ℝ, f ⟨p.1,p.2⟩ ∂(volume : Measure ℝ).prod volume
  rw [integral_prod _ hi]
  unfold M12CriticalAssembly.originalFockNorm
  simp_rw [f, density_kernel, integral_const_mul]

section Probability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
variable (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)

theorem original_eq_probability (M : ℕ) {a : ℝ} (ha : 0 < a) :
    M12CriticalAssembly.originalFockNorm M a =
      ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) *
        (∑ i ∈ range M, U i xy.2) / a) ∂μ.prod μ := by
  rw [original_eq_complex_integral M ha]
  exact fock_norm_eq_probability_integral U hU hind hlaw M ha

theorem original_eq_state_norm (M : ℕ) {a : ℝ} (ha : 0 < a) :
    M12CriticalAssembly.originalFockNorm M a = ‖fockState a M‖^2 := by
  rw [original_eq_probability U hU hind hlaw M ha, fockState_norm_sq U hU hind hlaw M ha]

theorem vacuum_eq_original_inv (M : ℕ) {a : ℝ} (ha : 0 < a) :
    fockVacuumProbability a M = (M12CriticalAssembly.originalFockNorm M a)⁻¹ := by
  rw [fockVacuumProbability, (fock_vacuum_probability U hU hind hlaw M ha).2.2,
    original_eq_probability U hU hind hlaw M ha, one_div]

theorem eventual_alpha_pos (lam : ℝ) :
    ∀ᶠ M : ℕ in atTop, 0 < (1/12+lam*scale M^2)*(M:ℝ) := by
  filter_upwards [eventual_scale_conditions |lam| (abs_nonneg lam)] with M hM
  rcases hM with ⟨hm,hsmall,_⟩
  have hb := mul_le_mul_of_nonneg_right (neg_abs_le lam) (sq_nonneg (scale M))
  have hc : 0 < (1/12:ℝ)+lam*scale M^2 := by nlinarith only [hb,hsmall]
  exact mul_pos hc (by exact_mod_cast hm)

/-- The actual vacuum projection, at the physical critical-window scale. -/
theorem actual_vacuum_critical_limit (lam : ℝ) :
    Tendsto (fun M : ℕ => (scale M)⁻¹ *
      fockVacuumProbability ((1/12+lam*scale M^2)*(M:ℝ)) M)
      atTop (𝓝 ((F lam)⁻¹)) := by
  apply (reciprocal_Fock_limit lam).congr'
  filter_upwards [eventual_alpha_pos lam] with M hM
  rw [vacuum_eq_original_inv U hU hind hlaw M hM]

/-- Original probability integral, not just an asymptotic surrogate. -/
theorem actual_probability_critical_limit (lam : ℝ) :
    Tendsto (fun M : ℕ => scale M *
      ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) *
        (∑ i ∈ range M, U i xy.2) / ((1/12+lam*scale M^2)*(M:ℝ))) ∂μ.prod μ)
      atTop (𝓝 (F lam)) := by
  apply (fixed_lambda_Fock_limit lam).congr'
  filter_upwards [eventual_alpha_pos lam] with M hM
  rw [original_eq_probability U hU hind hlaw M hM]

theorem actual_vacuum_at_critical :
    Tendsto (fun M : ℕ => (scale M)⁻¹ * fockVacuumProbability ((M:ℝ)/12) M)
      atTop (𝓝 (((40:ℝ)^(1/4:ℝ)*Real.Gamma (1/4)/(4*Real.sqrt Real.pi))⁻¹)) := by
  have h := actual_vacuum_critical_limit U hU hind hlaw 0
  rw [F_zero] at h
  convert h using 1 <;> simp <;> ring

end Probability
end M12CriticalVacuum

#print axioms M12CriticalVacuum.rE_eq_profile
#print axioms M12CriticalVacuum.density_kernel
#print axioms M12CriticalVacuum.density_integrable
#print axioms M12CriticalVacuum.original_eq_complex_integral
#print axioms M12CriticalVacuum.original_eq_probability
#print axioms M12CriticalVacuum.original_eq_state_norm
#print axioms M12CriticalVacuum.vacuum_eq_original_inv
#print axioms M12CriticalVacuum.eventual_alpha_pos
#print axioms M12CriticalVacuum.actual_vacuum_critical_limit
#print axioms M12CriticalVacuum.actual_probability_critical_limit
#print axioms M12CriticalVacuum.actual_vacuum_at_critical
