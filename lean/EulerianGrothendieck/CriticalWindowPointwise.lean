import CriticalWindowFinalAssembly

/-! Actual critical exponent with a quantitative sixth-order remainder.
No limit or logarithmic nonvanishing is assumed. -/
namespace M12CriticalPointwise
open Filter
open scoped Topology

noncomputable def q (e u w : ℝ) : ℂ :=
  ((u*e/Real.sqrt 2 : ℝ) : ℂ) + ((-w*e^2/Real.sqrt 2 : ℝ) : ℂ)*Complex.I

noncomputable def exponent (M : ℕ) (e lam u w : ℝ) : ℝ :=
  -6*(1/12+lam*e^2)*(M:ℝ)*(u^2*e^2+w^2*e^4) +
    2*(M:ℝ)*(Complex.log (M12ComplexMGF.mgf (q e u w))).re

noncomputable def limitingExponent (lam u w : ℝ) : ℝ :=
  -w^2-u^4/40-6*lam*u^2

theorem mgf_ne_zero (z : ℂ) (hz : ‖z‖ ≤ 1/4) :
    M12ComplexMGF.mgf z ≠ 0 := by
  let v := (Real.sqrt 3 : ℂ)*z
  have hs : Real.sqrt 3 ≤ 2 := by nlinarith [Real.sq_sqrt (show 0 ≤ (3:ℝ) by norm_num), Real.sqrt_nonneg 3]
  have hv : ‖v‖ ≤ 1/2 := by
    dsimp [v]
    rw [norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg 3)]
    have h := mul_le_mul_of_nonneg_right hs (norm_nonneg z)
    linarith
  let t := ‖v‖
  have ht : 0 ≤ t := norm_nonneg _
  have ht' : t ≤ 1/2 := hv
  have h2 : t^2 ≤ 1/4 := by nlinarith [mul_nonneg ht (sub_nonneg.mpr ht')]
  have h4 : t^4 ≤ 1/16 := by
    nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr h2)]
  have h6 : t^6 ≤ 1/64 := by
    nlinarith [mul_le_mul h4 h2 (sq_nonneg t) (by norm_num : (0:ℝ) ≤ 1/16)]
  intro hzero
  have hzv : M12ComplexMGF.csinhc v = 0 := hzero
  have hr := M12CriticalRemainder.csinhc_sixth_remainder v hv
  rw [hzv, zero_sub, norm_neg] at hr
  have hp : ‖v^2/6+v^4/120‖ ≤ t^2/6+t^4/120 := by
    calc
      _ ≤ ‖v^2/6‖+‖v^4/120‖ := norm_add_le _ _
      _ = _ := by simp [t, norm_div, norm_pow]
  have ha : ‖(1:ℂ)‖ ≤ ‖1+v^2/6+v^4/120‖+‖v^2/6+v^4/120‖ := by
    calc
      _ = ‖(1+v^2/6+v^4/120)-(v^2/6+v^4/120)‖ := by congr 1 <;> ring
      _ ≤ _ := norm_sub_le _ _
  change ‖1+v^2/6+v^4/120‖ ≤ 2*t^6 at hr
  rw [norm_one] at ha
  linarith only [ha,hp,hr,h2,h4,h6]

theorem q_norm_bound (e u w : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    ‖q e u w‖ ≤ (|u| + |w|) * e := by
  have hs : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num), Real.sqrt_nonneg 2]
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have he2 : e^2 ≤ e := by nlinarith [mul_nonneg he (sub_nonneg.mpr he1)]
  unfold q
  calc
    _ ≤ ‖((u*e/Real.sqrt 2 : ℝ) : ℂ)‖ +
        ‖((-w*e^2/Real.sqrt 2 : ℝ) : ℂ)*Complex.I‖ := norm_add_le _ _
    _ = |u| * e/Real.sqrt 2+|w| * e^2/Real.sqrt 2 := by
      simp [Complex.norm_real, norm_mul, abs_div, abs_mul, abs_neg, abs_of_nonneg he,
        abs_of_nonneg hs0.le, abs_of_nonneg (sq_nonneg e)]
    _ ≤ |u| * e+|w| * e^2 := by
      apply add_le_add <;> apply (div_le_iff₀ hs0).2
      · nlinarith [mul_nonneg (mul_nonneg (abs_nonneg u) he) (sub_nonneg.mpr hs)]
      · nlinarith [mul_nonneg (mul_nonneg (abs_nonneg w) (sq_nonneg e)) (sub_nonneg.mpr hs)]
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_left he2 (abs_nonneg w)]

theorem real_jet (a b : ℝ) :
    (((((a:ℂ)+(b:ℂ)*Complex.I)^2)/2 -
      (((a:ℂ)+(b:ℂ)*Complex.I)^4)/20)).re =
    (a^2-b^2)/2-(a^4-6*a^2*b^2+b^4)/20 := by
  simp [show (4:ℕ) = 2*2 by norm_num, pow_mul, pow_two, Complex.div_re, Complex.mul_re, Complex.mul_im,
    Complex.normSq_apply] <;> ring

theorem scaled_jet (e u w : ℝ) :
    ((q e u w)^2/2-(q e u w)^4/20).re =
      (u^2*e^2-w^2*e^4)/4 -
      (u^4*e^4-6*u^2*w^2*e^6+w^4*e^8)/80 := by
  unfold q
  rw [real_jet]
  have hs : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hs4 : (Real.sqrt (2:ℝ))^4 = 4 := by rw [show (4:ℕ)=2*2 by norm_num,pow_mul,hs]; norm_num
  rw [div_pow, div_pow, div_pow, div_pow, hs, hs4]
  ring

theorem exponent_error (M : ℕ) (e lam u w : ℝ)
    (he : 0 ≤ e) (he1 : e ≤ 1) (hM : (M:ℝ)*e^4 = 1)
    (hq : ‖q e u w‖ ≤ 1/4) :
    |exponent M e lam u w -
       (limitingExponent lam u w + e^2*(3/20*u^2*w^2-6*lam*w^2) -
        e^4*w^4/40)| ≤ 640*(|u| + |w|)^6*e^2 := by
  let z := q e u w
  let d := Complex.log (M12ComplexMGF.mgf z)-(z^2/2-z^4/20)
  have hd : ‖d‖ ≤ 320*‖z‖^6 := M12CriticalRemainder.standardized_log_sixth_remainder z hq
  have hreal : |d.re| ≤ ‖d‖ := Complex.abs_re_le_norm d
  have hn := q_norm_bound e u w he he1
  have hjet := scaled_jet e u w
  have hnormal := M12CriticalWindow.critical_exponent_normal_form e lam u w
  have heq : exponent M e lam u w -
       (limitingExponent lam u w + e^2*(3/20*u^2*w^2-6*lam*w^2) -
        e^4*w^4/40) = 2*(M:ℝ)*d.re := by
    dsimp [d,z,exponent,limitingExponent]
    have hj : (q e u w ^ 2 / 2).re - (q e u w ^ 4 / 20).re =
        (u^2*e^2-w^2*e^4)/4 - (u^4*e^4-6*u^2*w^2*e^6+w^4*e^8)/80 := by
      simpa only [Complex.sub_re] using hjet
    rw [hj]
    linear_combination (M:ℝ)*hnormal +
      (-w^2-u^4/40-6*lam*u^2+e^2*(3/20*u^2*w^2-6*lam*w^2)-e^4*w^4/40)*(hM)
  rw [heq, abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ (2:ℝ) by norm_num),
    abs_of_nonneg (show 0 ≤ (M:ℝ) by positivity)]
  calc
    _ ≤ 2*(M:ℝ)*(320*‖z‖^6) := mul_le_mul_of_nonneg_left (hreal.trans hd) (by positivity)
    _ ≤ 2*(M:ℝ)*(320*((|u| + |w|) * e)^6) := by
      gcongr
    _ = 640*(|u| + |w|)^6*e^2 := by
      calc
        _ = ((M:ℝ)*e^4)*(640*(|u| + |w|)^6*e^2) := by ring
        _ = _ := by rw [hM,one_mul]

theorem scaledIntegrand_eq_exp (M : ℕ) (e lam u w : ℝ)
    (hq : ‖q e u w‖ ≤ 1/4) :
    M12FockDomination.scaledIntegrand M e lam u w =
      Real.exp (exponent M e lam u w) := by
  have hn := mgf_ne_zero (q e u w) hq
  have hnorm : ‖M12ComplexMGF.mgf (q e u w)‖ =
      Real.exp (Complex.log (M12ComplexMGF.mgf (q e u w))).re := by
    rw [← Complex.norm_exp, Complex.exp_log hn]
  unfold M12FockDomination.scaledIntegrand exponent
  change Real.exp _ * ‖M12ComplexMGF.mgf (q e u w)‖^(2*M) = _
  rw [hnorm, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- Actual anisotropic scale, defined for every positive sample size. -/
noncomputable def scale (M : ℕ) : ℝ := (Real.sqrt (Real.sqrt (M:ℝ)))⁻¹

theorem scale_pos (M : ℕ) (hM : 0 < M) : 0 < scale M := by
  unfold scale
  positivity

theorem scale_identity (M : ℕ) (hM : 0 < M) : (M:ℝ)*scale M^4 = 1 := by
  have hm : 0 < (M:ℝ) := by exact_mod_cast hM
  have hs : (Real.sqrt (Real.sqrt (M:ℝ)))^2 = Real.sqrt (M:ℝ) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have h4 : (Real.sqrt (Real.sqrt (M:ℝ)))^4 = (M:ℝ) := by
    rw [show (4:ℕ)=2*2 by norm_num, pow_mul, hs, Real.sq_sqrt hm.le]
  rw [scale, inv_pow, h4, mul_inv_cancel₀ hm.ne']

theorem scale_tendsto : Tendsto scale atTop (𝓝 0) := by
  have h : Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto Real.sqrt atTop atTop := by
    refine tendsto_atTop.2 (fun x => ?_)
    filter_upwards [eventually_ge_atTop ((max x 0)^2)] with y hy
    have hx : 0 ≤ max x 0 := le_max_right _ _
    have hy0 : 0 ≤ y := (sq_nonneg _).trans hy
    have hh : max x 0 ≤ Real.sqrt y := by
      have hmono := Real.sqrt_le_sqrt hy
      rwa [Real.sqrt_sq hx] at hmono
    exact (le_max_left x 0).trans hh
  exact tendsto_inv_atTop_zero.comp (hsqrt.comp (hsqrt.comp h))

theorem actual_exponent_tendsto (lam u w : ℝ) :
    Tendsto (fun M : ℕ => exponent M (scale M) lam u w) atTop
      (𝓝 (limitingExponent lam u w)) := by
  let P := fun M : ℕ => limitingExponent lam u w +
      (scale M)^2*(3/20*u^2*w^2-6*lam*w^2)-(scale M)^4*w^4/40
  have hp : Tendsto P atTop (𝓝 (limitingExponent lam u w)) := by
    have hc : Tendsto (fun _ : ℕ => limitingExponent lam u w) atTop (𝓝 (limitingExponent lam u w)) := tendsto_const_nhds
    have hh := (hc.add ((scale_tendsto.pow 2).mul_const
      (3/20*u^2*w^2-6*lam*w^2))).sub (((scale_tendsto.pow 4).mul_const (w^4)).div_const 40)
    simpa [P] using hh
  have hsmall : ∀ᶠ M : ℕ in atTop, ‖q (scale M) u w‖ ≤ 1/4 := by
    have ht := scale_tendsto.const_mul (|u| + |w|)
    have ht' : Tendsto (fun M : ℕ => (|u| + |w|) * scale M) atTop (𝓝 0) := by simpa using ht
    filter_upwards [eventually_ge_atTop 1, scale_tendsto.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
      ht'.eventually (gt_mem_nhds (show (0:ℝ)<1/4 by norm_num))] with M hM h1 hq
    exact (q_norm_bound _ _ _ (scale_pos M (by omega)).le h1.le).trans hq.le
  have herr : ∀ᶠ M : ℕ in atTop,
      |exponent M (scale M) lam u w-P M| ≤ 640*(|u| + |w|)^6*(scale M)^2 := by
    filter_upwards [eventually_ge_atTop 1, scale_tendsto.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)), hsmall] with M hM h1 hq
    exact exponent_error M _ _ _ _ (scale_pos M (by omega)).le h1.le (scale_identity M (by omega)) hq
  have hbound : Tendsto (fun M : ℕ => 640*(|u| + |w|)^6*(scale M)^2) atTop (𝓝 0) := by
    simpa using (scale_tendsto.pow 2).const_mul (640*(|u| + |w|)^6)
  have hdiff : Tendsto (fun M : ℕ => exponent M (scale M) lam u w-P M) atTop (𝓝 0) := by
    apply squeeze_zero_norm' herr hbound
  have ht := hdiff.add hp
  convert ht using 1 <;> simp <;> ring

theorem actual_integrand_tendsto (lam u w : ℝ) :
    Tendsto (fun M : ℕ => M12FockDomination.scaledIntegrand M (scale M) lam u w) atTop
      (𝓝 (Real.exp (limitingExponent lam u w))) := by
  have ht := (Real.continuous_exp.continuousAt.tendsto.comp (actual_exponent_tendsto lam u w))
  apply ht.congr'
  have hq : Tendsto (fun M : ℕ => (|u| + |w|) * scale M) atTop (𝓝 0) := by
    simpa using scale_tendsto.const_mul (|u| + |w|)
  filter_upwards [eventually_ge_atTop 1, scale_tendsto.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    hq.eventually (gt_mem_nhds (show (0:ℝ)<1/4 by norm_num))] with M hM h1 hsmall
  exact (scaledIntegrand_eq_exp M _ _ _ _ ((q_norm_bound _ _ _ (scale_pos M (by omega)).le h1.le).trans hsmall.le)).symm

end M12CriticalPointwise

#print axioms M12CriticalPointwise.mgf_ne_zero
#print axioms M12CriticalPointwise.q_norm_bound
#print axioms M12CriticalPointwise.real_jet
#print axioms M12CriticalPointwise.scaled_jet
#print axioms M12CriticalPointwise.exponent_error
#print axioms M12CriticalPointwise.scaledIntegrand_eq_exp
#print axioms M12CriticalPointwise.scale_pos
#print axioms M12CriticalPointwise.scale_identity
#print axioms M12CriticalPointwise.scale_tendsto
#print axioms M12CriticalPointwise.actual_exponent_tendsto
#print axioms M12CriticalPointwise.actual_integrand_tendsto
