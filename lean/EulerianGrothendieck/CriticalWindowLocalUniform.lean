import CriticalWindowDCT

/-! M12 §9: a single measurable error envelope on each compact parameter
interval. No parameter-dependent DCT threshold and no abstract convergence
premise. -/
namespace M12CriticalUniform
open MeasureTheory Filter
open scoped Topology
open M12CriticalPointwise M12CriticalDCT

noncomputable def A (M : ℕ) (lam : ℝ) : ℝ :=
  scale M * M12CriticalAssembly.originalFockNorm M
    ((1/12+lam*scale M^2)*(M:ℝ))

theorem H_factor (M : ℕ) (hM : 0 < M) (L lam : ℝ) (p : ℝ × ℝ) :
    H lam M p = H (-L) M p *
      Real.exp (-6*(lam+L)*(p.1^2+scale M^2*p.2^2)) := by
  have hs := scale_identity M hM
  have he : -6*(1/12+lam*scale M^2)*(M:ℝ)*
      (p.1^2*scale M^2+p.2^2*scale M^4) =
      -6*(1/12+(-L)*scale M^2)*(M:ℝ)*
      (p.1^2*scale M^2+p.2^2*scale M^4) -
      6*(lam+L)*(p.1^2+scale M^2*p.2^2) := by
    linear_combination (-6*(lam+L)*(p.1^2+scale M^2*p.2^2))*hs
  unfold H M12FockDomination.scaledIntegrand
  rw [he, sub_eq_add_neg, Real.exp_add]
  ring

theorem G_factor (L lam : ℝ) (p : ℝ × ℝ) :
    G lam p = G (-L) p * Real.exp (-6*(lam+L)*p.1^2) := by
  unfold G limitingExponent
  rw [← Real.exp_add]
  congr 1
  ring

noncomputable def err (L : ℝ) (M : ℕ) (p : ℝ × ℝ) : ℝ :=
  |H (-L) M p - G (-L) p| +
    G (-L) p*(1-Real.exp (-12*L*scale M^2*p.2^2))

theorem G_nonneg (lam : ℝ) (p : ℝ × ℝ) : 0 ≤ G lam p := Real.exp_nonneg _

theorem err_nonneg (L : ℝ) (hL : 0 ≤ L) (M : ℕ) (p : ℝ × ℝ) :
    0 ≤ err L M p := by
  unfold err
  have h : Real.exp (-12*L*scale M^2*p.2^2) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have h' : 0 ≤ 12*L*scale M^2*p.2^2 := by positivity
    linarith
  exact add_nonneg (abs_nonneg _) (mul_nonneg (G_nonneg _ _) (sub_nonneg.mpr h))

theorem uniform_pointwise_error (L : ℝ) (hL : 0 ≤ L) (M : ℕ) (hM : 0 < M)
    (lam : ℝ) (hlam : |lam| ≤ L) (p : ℝ × ℝ) :
    |H lam M p - G lam p| ≤ err L M p := by
  have hlow : 0 ≤ lam+L := by linarith [neg_abs_le lam]
  have hhigh : lam+L ≤ 2*L := by linarith [le_abs_self lam]
  let a := Real.exp (-6*(lam+L)*(p.1^2+scale M^2*p.2^2))
  let b := Real.exp (-6*(lam+L)*p.1^2)
  let c := Real.exp (-6*(lam+L)*scale M^2*p.2^2)
  let d := Real.exp (-12*L*scale M^2*p.2^2)
  have hab : a = b*c := by
    dsimp [a,b,c]
    rw [← Real.exp_add]
    congr 1
    ring
  have hb0 : 0 ≤ b := Real.exp_nonneg _
  have hc0 : 0 ≤ c := Real.exp_nonneg _
  have hb1 : b ≤ 1 := by
    dsimp [b]
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hh : 0 ≤ 6*(lam+L)*p.1^2 := by positivity
    linarith
  have hc1 : c ≤ 1 := by
    dsimp [c]
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hh : 0 ≤ 6*(lam+L)*scale M^2*p.2^2 := by positivity
    linarith
  have hdc : d ≤ c := by
    dsimp [d,c]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hhigh
      (show 0 ≤ 6*scale M^2*p.2^2 by positivity)
    nlinarith only [hh]
  have ha0 : 0 ≤ a := Real.exp_nonneg _
  have ha1 : a ≤ 1 := by
    rw [hab]
    calc b*c ≤ 1*c := mul_le_mul_of_nonneg_right hb1 hc0
         _ ≤ 1 := by simpa using hc1
  have hab' : a ≤ b := by
    rw [hab]
    simpa using mul_le_mul_of_nonneg_left hc1 hb0
  have hdiff : |a-b| ≤ 1-d := by
    rw [abs_of_nonpos (sub_nonpos.mpr hab'), hab]
    calc
      -(b*c-b) = b*(1-c) := by ring
      _ ≤ 1*(1-c) := mul_le_mul_of_nonneg_right hb1 (sub_nonneg.mpr hc1)
      _ ≤ 1-d := by linarith
  rw [H_factor M hM L lam p, G_factor L lam p]
  change |H (-L) M p*a-G (-L) p*b| ≤ _
  have he : H (-L) M p*a-G (-L) p*b =
      (H (-L) M p-G (-L) p)*a+G (-L) p*(a-b) := by ring
  rw [he]
  calc
    _ ≤ |(H (-L) M p-G (-L) p)*a| + |G (-L) p*(a-b)| := abs_add_le _ _
    _ = |H (-L) M p-G (-L) p| *a+G (-L) p* |a-b| := by
      rw [abs_mul,abs_mul,abs_of_nonneg ha0,abs_of_nonneg (G_nonneg _ _)]
    _ ≤ |H (-L) M p-G (-L) p| *1+G (-L) p*(1-d) :=
      add_le_add (mul_le_mul_of_nonneg_left ha1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hdiff (G_nonneg _ _))
    _ = err L M p := by simp [err,d]

theorem err_measurable (L : ℝ) (M : ℕ) : Measurable (err L M) := by
  have hH := H_measurable (-L) M
  have hG : Measurable (G (-L)) := by unfold G limitingExponent; fun_prop
  unfold err
  exact (hH.sub hG).abs.add (hG.mul (by fun_prop))

theorem err_tendsto (L : ℝ) (p : ℝ × ℝ) :
    Tendsto (fun M : ℕ => err L M p) atTop (𝓝 0) := by
  have hH : Tendsto (fun M : ℕ => H (-L) M p) atTop (𝓝 (G (-L) p)) :=
    actual_integrand_tendsto (-L) p.1 p.2
  have hG : Tendsto (fun _ : ℕ => G (-L) p) atTop (𝓝 (G (-L) p)) := tendsto_const_nhds
  have hX : Tendsto (fun M : ℕ => -12*L*scale M^2*p.2^2) atTop (𝓝 0) := by
    simpa using ((scale_tendsto.pow 2).const_mul (-12*L)).mul_const (p.2^2)
  have hE := Real.continuous_exp.continuousAt.tendsto.comp hX
  have hOne : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := ((hH.sub hG).abs).add (hG.mul (hOne.sub hE))
  simpa [err,Real.exp_zero] using h

noncomputable def errBound (L : ℝ) (p : ℝ × ℝ) : ℝ :=
  M12FockDomination.majorant L p+2*G (-L) p

theorem errBound_integrable (L : ℝ) : Integrable (errBound L) planeMeasure :=
  (M12FockDomination.majorant_integrable L).add ((G_integrable (-L)).const_mul 2)

theorem eventual_err_bound (L : ℝ) (hL : 0 ≤ L) :
    ∀ᶠ M : ℕ in atTop, ∀ p, ‖err L M p‖ ≤ errBound L p := by
  filter_upwards [eventual_uniform_majorant L hL] with M hM
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (err_nonneg L hL M p)]
  have h := hM (-L) (by simpa [abs_of_nonneg hL]) p
  have ht : |H (-L) M p - G (-L) p| ≤ H (-L) M p + G (-L) p := by
    calc
      _ ≤ |H (-L) M p| + |-G (-L) p| := abs_add_le _ _
      _ = _ := by rw [abs_neg, abs_of_nonneg (H_nonneg _ _ _), abs_of_nonneg (G_nonneg _ _)]
  have hg := mul_nonneg (G_nonneg (-L) p)
    (Real.exp_nonneg (-12*L*scale M^2*p.2^2))
  unfold err errBound
  nlinarith only [h,ht,hg]

theorem integral_err_tendsto (L : ℝ) (hL : 0 ≤ L) :
    Tendsto (fun M : ℕ => ∫ p, err L M p ∂planeMeasure) atTop (𝓝 0) := by
  have h : Tendsto (fun M : ℕ => ∫ p, err L M p ∂planeMeasure) atTop
      (𝓝 (∫ _ : ℝ × ℝ, (0:ℝ) ∂planeMeasure)) := by
    apply tendsto_integral_filter_of_dominated_convergence (errBound L)
    · exact Eventually.of_forall fun M => (err_measurable L M).aestronglyMeasurable
    · filter_upwards [eventual_err_bound L hL] with M hM
      exact Eventually.of_forall hM
    · exact errBound_integrable L
    · exact Eventually.of_forall (err_tendsto L)
  simpa using h

theorem eventual_integral_error (L : ℝ) (hL : 0 ≤ L) :
    ∀ᶠ M : ℕ in atTop, ∀ lam, |lam| ≤ L →
      |(∫ p, H lam M p ∂planeMeasure)-(∫ p, G lam p ∂planeMeasure)| ≤
        ∫ p, err L M p ∂planeMeasure := by
  filter_upwards [eventually_ge_atTop 1, eventual_uniform_majorant L hL,
    eventual_err_bound L hL] with M hM hB hE
  intro lam hlam
  have hi : Integrable (H lam M) planeMeasure := by
    refine (M12FockDomination.majorant_integrable L).mono'
      (H_measurable lam M).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs,abs_of_nonneg (H_nonneg _ _ _)]
    exact hB lam hlam p
  have he : Integrable (err L M) planeMeasure :=
    (errBound_integrable L).mono' (err_measurable L M).aestronglyMeasurable
      (Eventually.of_forall hE)
  rw [← integral_sub hi (G_integrable lam), ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ p, ‖H lam M p-G lam p‖ ∂planeMeasure := norm_integral_le_integral_norm _
    _ ≤ _ := integral_mono_ae (hi.sub (G_integrable lam)).norm he
      (Eventually.of_forall fun p => by
        change ‖H lam M p-G lam p‖ ≤ err L M p
        rw [Real.norm_eq_abs]
        exact uniform_pointwise_error L hL M (by omega) lam hlam p)

theorem eventual_A_eq (L : ℝ) (hL : 0 ≤ L) :
    ∀ᶠ M : ℕ in atTop, ∀ lam, |lam| ≤ L →
      A M lam = (6*(1/12+lam*scale M^2)/Real.pi) *
        (∫ p, H lam M p ∂planeMeasure) := by
  filter_upwards [eventually_ge_atTop 1, eventual_uniform_majorant L hL] with M hM hB
  intro lam hlam
  have hm : 0 < M := by omega
  have hi : Integrable (H lam M) planeMeasure := by
    refine (M12FockDomination.majorant_integrable L).mono'
      (H_measurable lam M).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs,abs_of_nonneg (H_nonneg _ _ _)]
    exact hB lam hlam p
  unfold A
  rw [M12CriticalAssembly.normalized_Fock_eq_actual_scaled_integrand M (scale M) lam
    (scale_pos M hm) (scale_identity M hm)]
  have hf := integral_prod_symm (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ)) (H lam M) hi
  change (∫ p, H lam M p ∂planeMeasure) =
    (∫ w : ℝ, ∫ u : ℝ, M12FockDomination.scaledIntegrand M (scale M) lam u w) at hf
  rw [hf]

theorem F_eq_plane (lam : ℝ) :
    F lam = (1/(2*Real.pi))*(∫ p, G lam p ∂planeMeasure) := by
  rw [integral_G_factor]
  unfold F
  have hs : Real.sqrt Real.pi ≠ 0 := by positivity
  have hpi : (Real.sqrt Real.pi)^2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  field_simp [hs,Real.pi_ne_zero]
  linear_combination -(∫ u : ℝ, profile lam u) * hpi

noncomputable def uniformBound (L : ℝ) (M : ℕ) : ℝ :=
  (6*L*scale M^2/Real.pi)*(∫ p, M12FockDomination.majorant L p ∂planeMeasure) +
    (1/(2*Real.pi))*(∫ p, err L M p ∂planeMeasure)

theorem uniformBound_tendsto (L : ℝ) (hL : 0 ≤ L) :
    Tendsto (uniformBound L) atTop (𝓝 0) := by
  have h1 : Tendsto (fun M : ℕ => 6*L*scale M^2/Real.pi) atTop (𝓝 0) := by
    simpa using ((scale_tendsto.pow 2).const_mul (6*L)).div_const Real.pi
  have h2 := h1.mul_const (∫ p, M12FockDomination.majorant L p ∂planeMeasure)
  have h3 := (integral_err_tendsto L hL).const_mul (1/(2*Real.pi))
  convert h2.add h3 using 1 <;> simp [uniformBound, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem eventual_normalized_error (L : ℝ) (hL : 0 ≤ L) :
    ∀ᶠ M : ℕ in atTop, ∀ lam, |lam| ≤ L →
      |A M lam-F lam| ≤ uniformBound L M := by
  filter_upwards [eventual_A_eq L hL, eventual_integral_error L hL,
    eventual_uniform_majorant L hL] with M hA hE hB
  intro lam hlam
  let I := ∫ p, H lam M p ∂planeMeasure
  let J := ∫ p, G lam p ∂planeMeasure
  let K := ∫ p, M12FockDomination.majorant L p ∂planeMeasure
  let c : ℝ := 6*(1/12+lam*scale M^2)/Real.pi
  let d : ℝ := 1/(2*Real.pi)
  have hi : Integrable (H lam M) planeMeasure := by
    refine (M12FockDomination.majorant_integrable L).mono'
      (H_measurable lam M).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs,abs_of_nonneg (H_nonneg _ _ _)]
    exact hB lam hlam p
  have hi0 : 0 ≤ I := integral_nonneg (H_nonneg lam M)
  have hiK : I ≤ K := integral_mono_ae hi (M12FockDomination.majorant_integrable L)
    (Eventually.of_forall (hB lam hlam))
  have hk0 : 0 ≤ K := hi0.trans hiK
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hc : |c-d| ≤ 6*L*scale M^2/Real.pi := by
    have he : c-d = 6*lam*scale M^2/Real.pi := by
      dsimp [c,d]
      field_simp [Real.pi_ne_zero] <;> ring
    rw [he, abs_div,abs_mul,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ 6 by norm_num),
      abs_of_nonneg (sq_nonneg (scale M)),abs_of_nonneg Real.pi_pos.le]
    gcongr
  rw [hA lam hlam,F_eq_plane]
  change |c*I-d*J| ≤ _
  rw [show c*I-d*J = (c-d)*I+d*(I-J) by ring]
  calc
    _ ≤ |(c-d)*I| + |d*(I-J)| := abs_add_le _ _
    _ = |c-d| *I+d* |I-J| := by rw [abs_mul,abs_mul,abs_of_nonneg hi0,abs_of_nonneg hd0]
    _ ≤ (6*L*scale M^2/Real.pi)*K + d*(∫ p, err L M p ∂planeMeasure) :=
      add_le_add (mul_le_mul hc hiK hi0 (by positivity))
        (mul_le_mul_of_nonneg_left (hE lam hlam) hd0)
    _ = _ := rfl

/-- Explicit uniform convergence on every compact interval. -/
theorem locally_uniform_Fock (L : ℝ) (hL : 0 ≤ L) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ M : ℕ in atTop, ∀ lam, |lam| ≤ L → |A M lam-F lam| < eps := by
  filter_upwards [eventual_normalized_error L hL,
    (uniformBound_tendsto L hL).eventually (gt_mem_nhds heps)] with M hM hb
  intro lam hlam
  exact lt_of_le_of_lt (hM lam hlam) hb

end M12CriticalUniform

#print axioms M12CriticalUniform.H_factor
#print axioms M12CriticalUniform.G_factor
#print axioms M12CriticalUniform.G_nonneg
#print axioms M12CriticalUniform.err_nonneg
#print axioms M12CriticalUniform.uniform_pointwise_error
#print axioms M12CriticalUniform.err_measurable
#print axioms M12CriticalUniform.err_tendsto
#print axioms M12CriticalUniform.errBound_integrable
#print axioms M12CriticalUniform.eventual_err_bound
#print axioms M12CriticalUniform.integral_err_tendsto
#print axioms M12CriticalUniform.eventual_integral_error
#print axioms M12CriticalUniform.eventual_A_eq
#print axioms M12CriticalUniform.F_eq_plane
#print axioms M12CriticalUniform.uniformBound_tendsto
#print axioms M12CriticalUniform.eventual_normalized_error
#print axioms M12CriticalUniform.locally_uniform_Fock
