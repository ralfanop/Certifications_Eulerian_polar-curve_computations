import CriticalWindowLocalUniform

/-! M12 KREIN_EDITORIAL, 26 Nov: prop:cross-cw12 and
prop:cross-binary12. The CW kernel is the real-axis slice of the
already proved Fock kernel. The probabilistic Gaussian representation
and the full angular/polar substitution are separate obligations. -/
namespace M12CrossNormalization
open MeasureTheory Filter
open scoped Topology
open M12CriticalPointwise M12CriticalDCT M12CriticalUniform

noncomputable def cwKernel (lam : ℝ) (M : ℕ) (u : ℝ) : ℝ :=
  H lam M (u,0)

noncomputable def cwBound (L u : ℝ) : ℝ :=
  Real.exp ((6*|L|+1)^2/(2*M12GlobalMGF.deficitConstant)) *
    Real.exp (-u^2)

theorem cwBound_integrable (L : ℝ) : Integrable (cwBound L) := by
  unfold cwBound
  have h : Integrable (fun u : ℝ => Real.exp (-u^2)) := by
    simpa using (integrable_exp_neg_mul_sq (b := 1) (by norm_num))
  exact h.const_mul _

theorem cwKernel_measurable (lam : ℝ) (M : ℕ) : Measurable (cwKernel lam M) := by
  exact (H_measurable lam M).comp (by fun_prop)

theorem cwKernel_tendsto (lam u : ℝ) :
    Tendsto (fun M : ℕ => cwKernel lam M u) atTop (𝓝 (profile lam u)) := by
  simpa [cwKernel,H,limitingExponent,profile,neg_div] using actual_integrand_tendsto lam u 0

theorem cw_uniform_majorant (L : ℝ) (hL : 0 ≤ L) :
    ∀ᶠ M : ℕ in atTop, ∀ lam, |lam| ≤ L →
      ∀ u, ‖cwKernel lam M u‖ ≤ cwBound L u := by
  filter_upwards [eventual_uniform_majorant L hL] with M hM
  intro lam hlam u
  change ‖H lam M (u,0)‖ ≤ cwBound L u
  rw [Real.norm_eq_abs, abs_of_nonneg (H_nonneg lam M (u,0))]
  simpa [cwKernel,cwBound,M12FockDomination.majorant] using hM lam hlam (u,0)

theorem cw_factor (M : ℕ) (hM : 0 < M) (L lam u : ℝ) :
    cwKernel lam M u = cwKernel (-L) M u * Real.exp (-6*(lam+L)*u^2) := by
  simpa [cwKernel] using H_factor M hM L lam (u,0)

theorem profile_factor (L lam u : ℝ) :
    profile lam u = profile (-L) u * Real.exp (-6*(lam+L)*u^2) := by
  unfold profile
  rw [← Real.exp_add]
  congr 1
  ring

theorem cw_error (M : ℕ) (hM : 0 < M) (L lam u : ℝ) (hlam : |lam| ≤ L) :
    |cwKernel lam M u-profile lam u| ≤ |cwKernel (-L) M u-profile (-L) u| := by
  have ha : 0 ≤ lam+L := by linarith [neg_abs_le lam]
  have hb : Real.exp (-6*(lam+L)*u^2) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ha (sq_nonneg u)]
  rw [cw_factor M hM L lam u,profile_factor L lam u,← sub_mul,abs_mul,
    abs_of_nonneg (Real.exp_nonneg _)]
  simpa using mul_le_mul_of_nonneg_left hb (abs_nonneg (cwKernel (-L) M u-profile (-L) u))

theorem cw_integral_error_tendsto (L : ℝ) (hL : 0 ≤ L) :
    Tendsto (fun M : ℕ => ∫ u : ℝ, |cwKernel (-L) M u-profile (-L) u|)
      atTop (𝓝 0) := by
  have h : Tendsto (fun M : ℕ => ∫ u : ℝ, |cwKernel (-L) M u-profile (-L) u|)
      atTop (𝓝 (∫ _ : ℝ, (0:ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun u : ℝ => cwBound L u + ‖profile (-L) u‖)
    · exact Eventually.of_forall fun M =>
        ((cwKernel_measurable (-L) M).sub (by unfold profile; fun_prop)).abs.aestronglyMeasurable
    · filter_upwards [cw_uniform_majorant L hL] with M hM
      exact Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs,abs_abs]
        exact (norm_sub_le (cwKernel (-L) M u) (profile (-L) u)).trans
          (add_le_add_right (hM (-L) (by simpa [abs_of_nonneg hL]) u) _)
    · exact (cwBound_integrable L).add (profile_integrable (-L)).norm
    · exact Eventually.of_forall fun u => by
        have h := (cwKernel_tendsto (-L) u).sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => profile (-L) u) atTop (𝓝 (profile (-L) u)))
        simpa using h.abs
  simpa using h

theorem cw_locally_uniform_integral (L : ℝ) (hL : 0 ≤ L) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ M : ℕ in atTop, ∀ lam, |lam| ≤ L →
      |(∫ u : ℝ, cwKernel lam M u)-(∫ u : ℝ, profile lam u)| < eps := by
  filter_upwards [eventually_ge_atTop 1, cw_uniform_majorant L hL,
    (cw_integral_error_tendsto L hL).eventually (gt_mem_nhds heps)] with M hM hB hE
  intro lam hlam
  have hi (l : ℝ) (hl : |l| ≤ L) : Integrable (cwKernel l M) :=
    (cwBound_integrable L).mono' (cwKernel_measurable l M).aestronglyMeasurable
      (Eventually.of_forall (hB l hl))
  have hj := hi (-L) (by simpa [abs_of_nonneg hL])
  rw [← integral_sub (hi lam hlam) (profile_integrable lam),← Real.norm_eq_abs]
  calc
    _ ≤ ∫ u : ℝ, ‖cwKernel lam M u-profile lam u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, |cwKernel (-L) M u-profile (-L) u| := by
      apply integral_mono_ae ((hi lam hlam).sub (profile_integrable lam)).norm
      · simpa only [Real.norm_eq_abs] using (hj.sub (profile_integrable (-L))).norm
      · exact Eventually.of_forall fun u => by
          change ‖cwKernel lam M u-profile lam u‖ ≤ |cwKernel (-L) M u-profile (-L) u|
          rw [Real.norm_eq_abs]
          exact cw_error M (by omega) L lam u hlam
    _ < eps := hE

noncomputable def binaryQ (b x y : ℝ) : ℝ :=
  (x^2+y^2)^2-4*b^2*x^2*y^2

theorem binaryQ_lower (b x y : ℝ) :
    (1-b^2)*(x^2+y^2)^2 ≤ binaryQ b x y := by
  unfold binaryQ
  nlinarith only [mul_nonneg (sq_nonneg b) (sq_nonneg (x^2-y^2))]

theorem binaryQ_selfdual (x y : ℝ) :
    binaryQ (1/Real.sqrt 2) x y = x^4+y^4 := by
  have hs : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  unfold binaryQ
  rw [div_pow,hs]
  ring

noncomputable def binaryZ (b : ℝ) : ℝ :=
  (1/(4*Real.pi))*∫ p : ℝ × ℝ, Real.exp (-binaryQ b p.1 p.2/40) ∂planeMeasure

theorem binaryZ_selfdual :
    binaryZ (1/Real.sqrt 2) = (F 0)^2 := by
  have he : (fun p : ℝ × ℝ => Real.exp (-binaryQ (1/Real.sqrt 2) p.1 p.2/40)) =
      fun p => profile 0 p.1 * profile 0 p.2 := by
    funext p
    rw [binaryQ_selfdual]
    unfold profile
    rw [← Real.exp_add]
    congr 1
    ring
  unfold binaryZ
  rw [he]
  unfold planeMeasure
  rw [integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))]
  unfold F
  have hs : Real.sqrt Real.pi ≠ 0 := by positivity
  have hpi : (Real.sqrt Real.pi)^2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  field_simp [hs,Real.pi_ne_zero]
  simp only [Real.sq_sqrt Real.pi_pos.le]
  <;> ring

theorem cw_bipartite_exponent_difference (t a b m : ℝ) (hm : m ≠ 0) :
    t*(a+b)^2/(4*m)-t*(a-b)^2/(4*m) = t*a*b/m := by
  field_simp [hm]
  <;> ring

end M12CrossNormalization

#print axioms M12CrossNormalization.cwBound_integrable
#print axioms M12CrossNormalization.cwKernel_measurable
#print axioms M12CrossNormalization.cwKernel_tendsto
#print axioms M12CrossNormalization.cw_uniform_majorant
#print axioms M12CrossNormalization.cw_factor
#print axioms M12CrossNormalization.profile_factor
#print axioms M12CrossNormalization.cw_error
#print axioms M12CrossNormalization.cw_integral_error_tendsto
#print axioms M12CrossNormalization.cw_locally_uniform_integral
#print axioms M12CrossNormalization.binaryQ_lower
#print axioms M12CrossNormalization.binaryQ_selfdual
#print axioms M12CrossNormalization.binaryZ_selfdual
#print axioms M12CrossNormalization.cw_bipartite_exponent_difference
