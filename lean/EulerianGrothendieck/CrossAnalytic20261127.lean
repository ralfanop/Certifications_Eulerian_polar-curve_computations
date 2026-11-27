import CrossNormalization20261126

/-! M12 Propositions 9.19 and 9.20 (378)-(387).
Actual Gaussian transform, scaled real-axis kernel, fixed-parameter
normalization and quotient, and polar/radial reduction of binaryZ.
The probability/Tonelli identification, uniform quotient, final angular
period and improper period are not asserted by these declarations. -/
namespace M12CrossAnalytic
open MeasureTheory Set Filter
open scoped Topology
open M12CriticalPointwise M12CriticalDCT M12CriticalUniform M12CrossNormalization

theorem gaussian_complete_square (a s : ℝ) (ha : 0 < a) :
    (∫ h : ℝ, Real.exp (s*h-a*h^2)) =
      Real.exp (s^2/(4*a))*Real.sqrt (Real.pi/a) := by
  have he : (fun h : ℝ => Real.exp (s*h-a*h^2)) =
      fun h => Real.exp (s^2/(4*a))*Real.exp (-a*(h+(-s/(2*a)))^2) := by
    funext h
    rw [← Real.exp_add]
    congr 1
    field_simp [ne_of_gt ha] <;> ring
  rw [he, integral_const_mul,
    integral_add_right_eq_self (fun h : ℝ => Real.exp (-a*h^2)), integral_gaussian]

noncomputable def invT (M : ℕ) (lam : ℝ) : ℝ :=
  1+12*lam*scale M^2

noncomputable def gaussianKernel (M : ℕ) (v h : ℝ) : ℝ :=
  Real.exp (-(M:ℝ)*v*h^2)*‖M12ComplexMGF.mgf (h:ℂ)‖^(2*M)

noncomputable def gaussianCW (M : ℕ) (v : ℝ) : ℝ :=
  Real.sqrt ((M:ℝ)*v/Real.pi) * ∫ h : ℝ, gaussianKernel M v h

noncomputable def cwPrefactor (M : ℕ) (lam : ℝ) : ℝ :=
  Real.sqrt (invT M lam/(2*Real.pi))

noncomputable def cwScaled (M : ℕ) (lam : ℝ) : ℝ :=
  cwPrefactor M lam * ∫ u : ℝ, cwKernel lam M u

theorem gaussian_kernel_dilation (M : ℕ) (lam u : ℝ) :
    gaussianKernel M (invT M lam) (scale M/Real.sqrt 2*u) =
      cwKernel lam M u := by
  unfold gaussianKernel invT cwKernel H M12FockDomination.scaledIntegrand
  have he : scale M/Real.sqrt 2*u = u*scale M/Real.sqrt 2 := by ring
  rw [he]
  simp only [Prod.fst, Prod.snd, zero_mul, mul_zero, zero_div, Complex.ofReal_zero, add_zero,
    zero_pow (by decide : (2:ℕ) ≠ 0), neg_zero]
  congr 1
  congr 1
  have hs : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  rw [div_pow, mul_pow, hs]
  ring

theorem scale_square_mul_sqrt (M : ℕ) (hM : 0 < M) :
    scale M^2*Real.sqrt (M:ℝ) = 1 := by
  have hm : 0 < (M:ℝ) := by exact_mod_cast hM
  unfold scale
  rw [inv_pow,Real.sq_sqrt (Real.sqrt_nonneg _), inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 hm))]

theorem scaled_gaussian_prefactor (M : ℕ) (hM : 0 < M) (lam : ℝ)
    (hv : 0 ≤ invT M lam) :
    scale M*Real.sqrt ((M:ℝ)*invT M lam/Real.pi)*(scale M/Real.sqrt 2) =
      cwPrefactor M lam := by
  have hs : Real.sqrt (2:ℝ) ≠ 0 := by positivity
  rw [show (M:ℝ)*invT M lam/Real.pi = (M:ℝ)*(invT M lam/Real.pi) by ring,
    Real.sqrt_mul (Nat.cast_nonneg M)]
  calc
    _ = (scale M^2*Real.sqrt (M:ℝ)) *
        (Real.sqrt (invT M lam/Real.pi)/Real.sqrt 2) := by ring
    _ = cwPrefactor M lam := by
      rw [scale_square_mul_sqrt M hM, one_mul,
        ← Real.sqrt_div (div_nonneg hv Real.pi_pos.le)]
      unfold cwPrefactor
      congr 1
      field_simp [Real.pi_ne_zero] <;> ring

theorem actual_gaussian_normalization (M : ℕ) (hM : 0 < M) (lam : ℝ)
    (hv : 0 ≤ invT M lam) :
    scale M*gaussianCW M (invT M lam) = cwScaled M lam := by
  have hd := M12CriticalAssembly.line_dilation (gaussianKernel M (invT M lam))
    (scale M/Real.sqrt 2) (div_pos (scale_pos M hM) (by positivity))
  unfold gaussianCW cwScaled
  rw [hd]
  simp_rw [gaussian_kernel_dilation]
  rw [← mul_assoc, ← mul_assoc, scaled_gaussian_prefactor M hM lam hv]

theorem invT_tendsto (lam : ℝ) :
    Tendsto (fun M : ℕ => invT M lam) atTop (𝓝 1) := by
  simpa [invT] using ((scale_tendsto.pow 2).const_mul (12*lam)).const_add 1

theorem cwPrefactor_tendsto (lam : ℝ) :
    Tendsto (fun M : ℕ => cwPrefactor M lam) atTop (𝓝 (Real.sqrt (1/(2*Real.pi)))) := by
  exact Real.continuous_sqrt.continuousAt.tendsto.comp ((invT_tendsto lam).div_const (2*Real.pi))

theorem cwIntegral_tendsto (lam : ℝ) :
    Tendsto (fun M : ℕ => ∫ u : ℝ, cwKernel lam M u) atTop
      (𝓝 (∫ u : ℝ, profile lam u)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [cw_locally_uniform_integral |lam| (abs_nonneg lam)
      ((∫ u : ℝ, profile lam u)-a) (sub_pos.mpr ha)] with M hM
    have h := (abs_lt.mp (hM lam le_rfl)).1
    linarith
  · intro a ha
    filter_upwards [cw_locally_uniform_integral |lam| (abs_nonneg lam)
      (a-(∫ u : ℝ, profile lam u)) (sub_pos.mpr ha)] with M hM
    have h := (abs_lt.mp (hM lam le_rfl)).2
    linarith

theorem cw_prefactor_limit_exact :
    Real.sqrt (1/(2*Real.pi)) = Real.sqrt 2*(1/(2*Real.sqrt Real.pi)) := by
  have h1 : 0 ≤ Real.sqrt (1/(2*Real.pi)) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt 2*(1/(2*Real.sqrt Real.pi)) := by positivity
  have hs : Real.sqrt Real.pi ≠ 0 := by positivity
  have he : (Real.sqrt (1/(2*Real.pi)))^2 =
      (Real.sqrt 2*(1/(2*Real.sqrt Real.pi)))^2 := by
    rw [Real.sq_sqrt (by positivity),mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
      div_pow,mul_pow,Real.sq_sqrt Real.pi_pos.le]
    field_simp [Real.pi_ne_zero] <;> ring
  nlinarith only [he,h1,h2]

theorem cwScaled_tendsto (lam : ℝ) :
    Tendsto (fun M : ℕ => cwScaled M lam) atTop (𝓝 (Real.sqrt 2*F lam)) := by
  have h := (cwPrefactor_tendsto lam).mul (cwIntegral_tendsto lam)
  rw [cw_prefactor_limit_exact] at h
  simpa [cwScaled,F,mul_assoc] using h

theorem gaussianCW_tendsto (lam : ℝ) :
    Tendsto (fun M : ℕ => scale M*gaussianCW M (invT M lam)) atTop
      (𝓝 (Real.sqrt 2*F lam)) := by
  apply (cwScaled_tendsto lam).congr'
  filter_upwards [eventually_ge_atTop 1,
    (invT_tendsto lam).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with M hm hv
  exact (actual_gaussian_normalization M (by omega) lam hv.le).symm

theorem fock_A_tendsto (lam : ℝ) :
    Tendsto (fun M : ℕ => A M lam) atTop (𝓝 (F lam)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [locally_uniform_Fock |lam| (abs_nonneg lam)
      (F lam-a) (sub_pos.mpr ha)] with M hM
    have h := (abs_lt.mp (hM lam le_rfl)).1
    linarith
  · intro a ha
    filter_upwards [locally_uniform_Fock |lam| (abs_nonneg lam)
      (a-F lam) (sub_pos.mpr ha)] with M hM
    have h := (abs_lt.mp (hM lam le_rfl)).2
    linarith

theorem gaussian_ratio_tendsto (lam : ℝ) :
    Tendsto (fun M : ℕ => A M lam/(scale M*gaussianCW M (invT M lam))) atTop
      (𝓝 (1/Real.sqrt 2)) := by
  have hn : Real.sqrt 2*F lam ≠ 0 := ne_of_gt (mul_pos (by positivity) (F_pos lam))
  have h := (fock_A_tendsto lam).div (gaussianCW_tendsto lam) hn
  have he : F lam/(Real.sqrt 2*F lam) = 1/Real.sqrt 2 := by
    field_simp [ne_of_gt (F_pos lam),show Real.sqrt (2:ℝ) ≠ 0 by positivity]
  rwa [he] at h

theorem binaryQ_polar (b r θ : ℝ) :
    binaryQ b (r*Real.cos θ) (r*Real.sin θ) =
      r^4*(1-b^2*Real.sin (2*θ)^2) := by
  have hrad : (r*Real.cos θ)^2+(r*Real.sin θ)^2 = r^2 := by
    calc
      _ = r^2*(Real.sin θ^2+Real.cos θ^2) := by ring
      _ = r^2 := by rw [Real.sin_sq_add_cos_sq,mul_one]
  unfold binaryQ
  rw [hrad,Real.sin_two_mul]
  ring

theorem binaryZ_polar (b : ℝ) :
    binaryZ b = (1/(4*Real.pi)) *
      ∫ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 * Real.exp (-p.1^4*(1-b^2*Real.sin (2*p.2)^2)/40) := by
  unfold binaryZ planeMeasure
  congr 1
  rw [← Measure.volume_eq_prod, ← integral_comp_polarCoord_symm, polarCoord_target]
  refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
  rw [polarCoord_symm_apply, smul_eq_mul, binaryQ_polar]

theorem angular_coefficient_pos (b θ : ℝ) (hb : 0 ≤ b) (hb1 : b < 1) :
    0 < 1-b^2*Real.sin (2*θ)^2 := by
  have hs : Real.sin (2*θ)^2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (2*θ),sq_nonneg (Real.cos (2*θ))]
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg b)
  nlinarith [mul_pos (sub_pos.mpr hb1) (show 0 < 1+b by linarith)]

theorem radial_quartic (a : ℝ) (ha : 0 < a) :
    (∫ r in Ioi (0:ℝ), r*Real.exp (-a*r^4/40)) =
      Real.sqrt (Real.pi/(a/40))/4 := by
  calc
    _ = (1/2:ℝ)*(∫ y in Ioi (0:ℝ), Real.exp (-(a/40)*y^2)) := by
      rw [← integral_comp_rpow_Ioi_of_pos (by norm_num : (0:ℝ) < 2), ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
      norm_num [smul_eq_mul, Real.rpow_natCast] <;> ring_nf
    _ = _ := by
      rw [integral_gaussian_Ioi]
      ring

end M12CrossAnalytic
#print axioms M12CrossAnalytic.gaussian_complete_square
#print axioms M12CrossAnalytic.gaussian_kernel_dilation
#print axioms M12CrossAnalytic.scale_square_mul_sqrt
#print axioms M12CrossAnalytic.scaled_gaussian_prefactor
#print axioms M12CrossAnalytic.actual_gaussian_normalization
#print axioms M12CrossAnalytic.invT_tendsto
#print axioms M12CrossAnalytic.cwPrefactor_tendsto
#print axioms M12CrossAnalytic.cwIntegral_tendsto
#print axioms M12CrossAnalytic.cw_prefactor_limit_exact
#print axioms M12CrossAnalytic.cwScaled_tendsto
#print axioms M12CrossAnalytic.gaussianCW_tendsto
#print axioms M12CrossAnalytic.fock_A_tendsto
#print axioms M12CrossAnalytic.gaussian_ratio_tendsto
#print axioms M12CrossAnalytic.binaryQ_polar
#print axioms M12CrossAnalytic.binaryZ_polar
#print axioms M12CrossAnalytic.angular_coefficient_pos
#print axioms M12CrossAnalytic.radial_quartic
