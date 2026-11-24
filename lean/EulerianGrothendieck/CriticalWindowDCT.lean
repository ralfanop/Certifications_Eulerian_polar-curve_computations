import CriticalWindowPointwise

/-! M12 §9. Dominated convergence on the actual rescaled Fock plane,
with the fixed real critical parameter. Local uniformity is a separate step.
The original Fock norm is the integral defined in CriticalWindowFinalAssembly. -/
namespace M12CriticalDCT

open MeasureTheory Filter
open scoped Topology
open M12CriticalPointwise

noncomputable def planeMeasure : Measure (ℝ × ℝ) :=
  (volume : Measure ℝ).prod volume

noncomputable def H (lam : ℝ) (M : ℕ) (p : ℝ × ℝ) : ℝ :=
  M12FockDomination.scaledIntegrand M (scale M) lam p.1 p.2

noncomputable def G (lam : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (limitingExponent lam p.1 p.2)

noncomputable def profile (lam u : ℝ) : ℝ :=
  Real.exp (-u^4/40-6*lam*u^2)

noncomputable def F (lam : ℝ) : ℝ :=
  (1/(2*Real.sqrt Real.pi)) * ∫ u : ℝ, profile lam u

theorem csinhc_measurable : Measurable M12ComplexMGF.csinhc := by
  unfold M12ComplexMGF.csinhc
  exact Measurable.ite (measurableSet_singleton (0:ℂ)) measurable_const
    (by fun_prop)

theorem mgf_measurable : Measurable M12ComplexMGF.mgf := by
  unfold M12ComplexMGF.mgf
  exact csinhc_measurable.comp (by fun_prop)

theorem H_measurable (lam : ℝ) (M : ℕ) : Measurable (H lam M) := by
  unfold H M12FockDomination.scaledIntegrand
  apply Measurable.mul
  · fun_prop
  · apply Measurable.pow_const
    exact (mgf_measurable.comp (by fun_prop)).norm

theorem H_nonneg (lam : ℝ) (M : ℕ) (p : ℝ × ℝ) : 0 ≤ H lam M p := by
  unfold H M12FockDomination.scaledIntegrand
  positivity

theorem eventual_scale_conditions (L : ℝ) (hL : 0 ≤ L) :
    ∀ᶠ M : ℕ in atTop, 0 < M ∧
      L*scale M^2 ≤ 1/24 ∧
      (6*L+1)*scale M^2 ≤ M12GlobalMGF.deficitConstant := by
  have h1 : Tendsto (fun M => L*scale M^2) atTop (𝓝 0) := by
    simpa using (scale_tendsto.pow 2).const_mul L
  have h2 : Tendsto (fun M => (6*L+1)*scale M^2) atTop (𝓝 0) := by
    simpa using (scale_tendsto.pow 2).const_mul (6*L+1)
  filter_upwards [eventually_ge_atTop 1,
    h1.eventually (gt_mem_nhds (show (0:ℝ) < 1/24 by norm_num)),
    h2.eventually (gt_mem_nhds M12GlobalMGF.deficitConstant_pos)] with M hM ha hb
  exact ⟨by omega,ha.le,hb.le⟩

/-- One eventual envelope valid simultaneously for the whole parameter interval. -/
theorem eventual_uniform_majorant (L : ℝ) (hL : 0 ≤ L) :
    ∀ᶠ M : ℕ in atTop, ∀ lam : ℝ, |lam| ≤ L →
      ∀ p : ℝ × ℝ, H lam M p ≤ M12FockDomination.majorant L p := by
  filter_upwards [eventual_scale_conditions L hL] with M hM
  rcases hM with ⟨hM,ha,hb⟩
  intro lam hlam p
  have hs : 0 < scale M := scale_pos M hM
  have hsq : 0 ≤ scale M^2 := sq_nonneg _
  have hl : -L ≤ lam := by linarith [neg_abs_le lam]
  have hc : (1/24:ℝ) ≤ 1/12+lam*scale M^2 := by
    nlinarith only [ha,mul_le_mul_of_nonneg_right hl hsq]
  have hb' : (6*|lam|+1)*scale M^2 ≤ M12GlobalMGF.deficitConstant := by
    have h := mul_le_mul_of_nonneg_right (show 6*|lam|+1 ≤ 6*L+1 by linarith) hsq
    exact h.trans hb
  have hm := M12FockDomination.scaledIntegrand_le_majorant M (scale M) lam p.1 p.2
    hs (scale_identity M hM) hc hb'
  have hmon : M12FockDomination.majorant lam p ≤ M12FockDomination.majorant L p := by
    unfold M12FockDomination.majorant
    rw [abs_of_nonneg hL]
    have hsq' : (6*|lam|+1)^2 ≤ (6*L+1)^2 := by
      apply pow_le_pow_left₀ (by positivity) (by linarith) 2
    gcongr
  exact hm.trans hmon

theorem eventual_H_integrable (lam : ℝ) :
    ∀ᶠ M : ℕ in atTop, Integrable (H lam M) planeMeasure := by
  filter_upwards [eventual_uniform_majorant |lam| (abs_nonneg lam)] with M hM
  apply (M12FockDomination.majorant_integrable |lam|).mono'
    (H_measurable lam M).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs,abs_of_nonneg (H_nonneg lam M p)]
    exact hM lam le_rfl p

theorem profile_integrable (lam : ℝ) : Integrable (profile lam) := by
  have h := (integrable_exp_neg_mul_sq (b := 1) (by norm_num : (0:ℝ)<1)).const_mul
    (Real.exp ((6*|lam|+1)^2*20))
  apply h.mono' (by unfold profile; fun_prop)
  refine Eventually.of_forall fun u => ?_
  unfold profile
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb := sq_nonneg (u^2/40-(6*|lam|+1)/2)
  have hl := mul_le_mul_of_nonneg_right (neg_le_abs lam) (sq_nonneg u)
  nlinarith only [hb,hl,sq_nonneg (6*|lam|+1)]

theorem G_eq_product (lam : ℝ) (p : ℝ × ℝ) :
    G lam p = profile lam p.1 * Real.exp (-p.2^2) := by
  unfold G profile limitingExponent
  rw [← Real.exp_add]
  congr 1
  ring

theorem G_integrable (lam : ℝ) : Integrable (G lam) planeMeasure := by
  have hw : Integrable (fun w : ℝ => Real.exp (-w^2)) := by
    simpa using (integrable_exp_neg_mul_sq (b := 1) (by norm_num))
  have h := (profile_integrable lam).mul_prod hw
  apply h.congr
  exact Eventually.of_forall fun p => (G_eq_product lam p).symm

/-- DCT on the actual full product measure, not on a truncated domain. -/
theorem integral_H_tendsto (lam : ℝ) :
    Tendsto (fun M : ℕ => ∫ p, H lam M p ∂planeMeasure) atTop
      (𝓝 (∫ p, G lam p ∂planeMeasure)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (M12FockDomination.majorant |lam|)
  · exact Eventually.of_forall fun M => (H_measurable lam M).aestronglyMeasurable
  · filter_upwards [eventual_uniform_majorant |lam| (abs_nonneg lam)] with M hM
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (H_nonneg lam M p)]
      exact hM lam le_rfl p
  · exact M12FockDomination.majorant_integrable |lam|
  · exact Eventually.of_forall fun p => actual_integrand_tendsto lam p.1 p.2

theorem integral_G_factor (lam : ℝ) :
    (∫ p, G lam p ∂planeMeasure) =
      (∫ u : ℝ, profile lam u) * Real.sqrt Real.pi := by
  have heq : G lam = fun p => profile lam p.1 * Real.exp (-p.2^2) :=
    funext (G_eq_product lam)
  rw [heq]
  unfold planeMeasure
  rw [integral_prod_mul, M12FockDomination.gaussian_factor]

theorem eventual_original_Fock_eq (lam : ℝ) :
    ∀ᶠ M : ℕ in atTop,
      scale M * M12CriticalAssembly.originalFockNorm M
        ((1/12+lam*scale M^2)*(M:ℝ)) =
      (6*(1/12+lam*scale M^2)/Real.pi) *
        (∫ p, H lam M p ∂planeMeasure) := by
  filter_upwards [eventually_ge_atTop 1, eventual_H_integrable lam] with M hM hi
  have hm : 0 < M := by omega
  rw [M12CriticalAssembly.normalized_Fock_eq_actual_scaled_integrand M (scale M) lam
    (scale_pos M hm) (scale_identity M hm)]
  rw [integral_prod_symm (H lam M) hi]
  rfl

theorem fixed_lambda_Fock_limit (lam : ℝ) :
    Tendsto (fun M : ℕ => scale M * M12CriticalAssembly.originalFockNorm M
        ((1/12+lam*scale M^2)*(M:ℝ))) atTop (𝓝 (F lam)) := by
  have hc : Tendsto (fun M : ℕ => 6*(1/12+lam*scale M^2)/Real.pi)
      atTop (𝓝 (1/(2*Real.pi))) := by
    have hh : Tendsto (fun M : ℕ => (1/12:ℝ)+lam*scale M^2) atTop
        (𝓝 ((1/12:ℝ)+lam*0^2)) :=
      tendsto_const_nhds.add ((scale_tendsto.pow 2).const_mul lam)
    have ht := (hh.const_mul 6).div_const Real.pi
    convert ht using 1 <;> ring
  have h := hc.mul (integral_H_tendsto lam)
  rw [integral_G_factor] at h
  have hs : Real.sqrt Real.pi ≠ 0 := by positivity
  have hpi : (Real.sqrt Real.pi)^2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have heq : (1/(2*Real.pi))*((∫ u : ℝ, profile lam u)*Real.sqrt Real.pi) = F lam := by
    unfold F
    field_simp [hs,Real.pi_ne_zero]
    nlinarith only [hpi]
  rw [heq] at h
  exact h.congr' (eventual_original_Fock_eq lam).symm

theorem F_pos (lam : ℝ) : 0 < F lam := by
  unfold F
  apply mul_pos (by positivity)
  exact integral_exp_pos (profile_integrable lam)

theorem F_zero :
    F 0 = (40:ℝ)^(1/4:ℝ)*Real.Gamma (1/4)/(4*Real.sqrt Real.pi) := by
  have heq : profile 0 = M12CriticalGamma.quarticProfile := by
    funext u
    simp [profile,M12CriticalGamma.quarticProfile]
  unfold F
  rw [heq]
  exact M12CriticalGamma.critical_constant

/-- The reciprocal of the actual Fock norm; identifying it with the
manuscript's vacuum probability is a separate definition bridge. -/
theorem reciprocal_Fock_limit (lam : ℝ) :
    Tendsto (fun M : ℕ => (scale M)⁻¹ *
      (M12CriticalAssembly.originalFockNorm M
        ((1/12+lam*scale M^2)*(M:ℝ)))⁻¹) atTop (𝓝 ((F lam)⁻¹)) := by
  simpa only [mul_inv_rev,mul_comm] using
    (fixed_lambda_Fock_limit lam).inv₀ (F_pos lam).ne'

end M12CriticalDCT

#print axioms M12CriticalDCT.csinhc_measurable
#print axioms M12CriticalDCT.mgf_measurable
#print axioms M12CriticalDCT.H_measurable
#print axioms M12CriticalDCT.H_nonneg
#print axioms M12CriticalDCT.eventual_scale_conditions
#print axioms M12CriticalDCT.eventual_uniform_majorant
#print axioms M12CriticalDCT.eventual_H_integrable
#print axioms M12CriticalDCT.profile_integrable
#print axioms M12CriticalDCT.G_eq_product
#print axioms M12CriticalDCT.G_integrable
#print axioms M12CriticalDCT.integral_H_tendsto
#print axioms M12CriticalDCT.integral_G_factor
#print axioms M12CriticalDCT.eventual_original_Fock_eq
#print axioms M12CriticalDCT.fixed_lambda_Fock_limit
#print axioms M12CriticalDCT.F_pos
#print axioms M12CriticalDCT.F_zero
#print axioms M12CriticalDCT.reciprocal_Fock_limit
