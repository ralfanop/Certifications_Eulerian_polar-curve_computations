import CriticalWindowComplexMGF

/-! M12 §9: the actual anisotropically rescaled Fock integrand, with a
single integrable Gaussian bound on the entire plane. No truncated domains
and no postulated majorant. The scale e satisfies M * e^4 = 1. -/
namespace M12FockDomination
open MeasureTheory

noncomputable def fockProfile (z : ℂ) : ℂ :=
  if z = 0 then 1 else Complex.sin (z/2) / (z/2)

/-- The removable sine profile is precisely the rotated hyperbolic profile. -/
theorem fockProfile_eq_csinhc (z : ℂ) :
    fockProfile z = M12ComplexMGF.csinhc (-(z/2 * Complex.I)) := by
  by_cases hz : z = 0
  · simp [hz, fockProfile, M12ComplexMGF.csinhc]
  have hd : z/2 ≠ 0 := div_ne_zero hz (by norm_num)
  have hi : -(z/2 * Complex.I) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hd Complex.I_ne_zero)
  rw [fockProfile, if_neg hz, M12ComplexMGF.csinhc, if_neg hi,
    Complex.sinh_neg, Complex.sinh_mul_I]
  field_simp [hd, Complex.I_ne_zero] <;> ring

/-- Identification with the standardized uniform MGF, including at zero. -/
theorem fockProfile_eq_mgf (z : ℂ) :
    fockProfile z = M12ComplexMGF.mgf (-(z/2 * Complex.I) / (Real.sqrt 3 : ℂ)) := by
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (show Real.sqrt 3 ≠ 0 by positivity)
  rw [fockProfile_eq_csinhc, M12ComplexMGF.mgf]
  congr 1
  field_simp [hs]

noncomputable def scaledIntegrand (M : ℕ) (e lam u w : ℝ) : ℝ :=
  Real.exp (-6 * (1/12 + lam*e^2) * (M:ℝ) * (u^2*e^2 + w^2*e^4)) *
    ‖M12ComplexMGF.mgf (((u*e/Real.sqrt 2 : ℝ) : ℂ) +
      ((-w*e^2/Real.sqrt 2 : ℝ) : ℂ)*Complex.I)‖^(2*M)

noncomputable def majorant (lam : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp ((6* |lam|+1)^2 / (2*M12GlobalMGF.deficitConstant)) *
    Real.exp (-p.1^2) * Real.exp (- (1/4) * p.2^2)

theorem quartic_le_gaussian (b A u : ℝ) (hb : 0 < b) :
    A*u^2-b*u^4/2 ≤ (A+1)^2/(2*b)-u^2 := by
  have h := sq_nonneg (b*u^2-(A+1))
  have h' : (A*u^2-b*u^4/2+u^2)*(2*b) ≤ (A+1)^2 := by
    nlinarith only [h]
  have hh := (le_div_iff₀ (show 0 < 2*b by positivity)).2 h'
  linarith only [hh]

/-- A uniform majorant for the actual MGF power with precisely the Fock
Gaussian. The hypotheses hold eventually for each fixed lambda. -/
theorem scaledIntegrand_le_majorant (M : ℕ) (e lam u w : ℝ)
    (he : 0 < e) (hM : (M:ℝ)*e^4 = 1)
    (hc : (1/24:ℝ) ≤ 1/12+lam*e^2)
    (hbscale : (6* |lam|+1)*e^2 ≤ M12GlobalMGF.deficitConstant) :
    scaledIntegrand M e lam u w ≤ majorant lam (u,w) := by
  let b := M12GlobalMGF.deficitConstant
  let h := u*e/Real.sqrt 2
  let k := -w*e^2/Real.sqrt 2
  have hb : 0 < b := M12GlobalMGF.deficitConstant_pos
  have hs : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  have hh : h^2 = u^2*e^2/2 := by
    dsimp [h]
    rw [div_pow, hs]
    ring
  have hh4 : h^4 = u^4*e^4/4 := by
    rw [show h^4 = (h^2)^2 by ring, hh]
    ring
  have hm0 : 0 ≤ (M:ℝ) := by positivity
  have habs : -lam ≤ |lam| := neg_le_abs lam
  have hu : -6*lam*u^2 ≤ 6* |lam|*u^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right habs (sq_nonneg u)]
  have hw : -6*(1/12+lam*e^2)*w^2 ≤ -w^2/4 := by
    nlinarith only [mul_le_mul_of_nonneg_right hc (sq_nonneg w)]
  have hnorm :
      ‖M12ComplexMGF.mgf ((h:ℂ)+(k:ℂ)*Complex.I)‖^(2*M) ≤
      Real.exp (h^2/2-b*min (h^4) (h^2))^(2*M) :=
    pow_le_pow_left₀ (norm_nonneg _) (M12ComplexMGF.critical_exponential_envelope h k) _
  have hexp :
      -6*(1/12+lam*e^2)*(M:ℝ)*(u^2*e^2+w^2*e^4) +
        ((2*M:ℕ):ℝ)*(h^2/2-b*min (h^4) (h^2)) =
      -6*lam*u^2-6*(1/12+lam*e^2)*w^2-2*(M:ℝ)*b*min (h^4) (h^2) := by
    nth_rw 1 [hh]
    push_cast
    calc
      _ = ((M:ℝ)*e^4)*(-6*lam*u^2-6*(1/12+lam*e^2)*w^2) -
          2*(M:ℝ)*b*min (h^4) (h^2) := by ring
      _ = _ := by rw [hM, one_mul]
  have hdef : 6* |lam|*u^2-2*(M:ℝ)*b*min (h^4) (h^2) ≤
      (6* |lam|+1)^2/(2*b)-u^2 := by
    by_cases hsmall : h^4 ≤ h^2
    · rw [min_eq_left hsmall, hh4]
      have heq : 2*(M:ℝ)*b*(u^4*e^4/4) = b*u^4/2 := by
        calc
          _ = ((M:ℝ)*e^4)*(b*u^4/2) := by ring
          _ = _ := by rw [hM, one_mul]
      rw [heq]
      exact quartic_le_gaussian b (6* |lam|) u hb
    · rw [min_eq_right (le_of_not_ge hsmall), hh]
      have hmul := mul_le_mul_of_nonneg_left hbscale
        (show 0 ≤ (M:ℝ)*e^2*u^2 by positivity)
      have hscale : (M:ℝ)*e^2*u^2*((6* |lam|+1)*e^2) =
          (6* |lam|+1)*u^2 := by
        calc
          _ = ((M:ℝ)*e^4)*((6* |lam|+1)*u^2) := by ring
          _ = _ := by rw [hM, one_mul]
      rw [hscale] at hmul
      have hC : 0 ≤ (6* |lam|+1)^2/(2*b) := by positivity
      nlinarith only [hmul, hC]
  unfold scaledIntegrand majorant
  change Real.exp _ * ‖M12ComplexMGF.mgf ((h:ℂ)+(k:ℂ)*Complex.I)‖^(2*M) ≤ _
  calc
    _ ≤ Real.exp (-6*(1/12+lam*e^2)*(M:ℝ)*(u^2*e^2+w^2*e^4)) *
          Real.exp (h^2/2-b*min (h^4) (h^2))^(2*M) :=
      mul_le_mul_of_nonneg_left hnorm (Real.exp_nonneg _)
    _ = Real.exp (-6*lam*u^2-6*(1/12+lam*e^2)*w^2-2*(M:ℝ)*b*min (h^4) (h^2)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, hexp]
    _ ≤ Real.exp ((6* |lam|+1)^2/(2*b)-u^2-w^2/4) :=
      Real.exp_le_exp.mpr (by linarith only [hu, hw, hdef])
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [b]
      ring

/-- Integrability on the entire real plane, with the product Lebesgue measure. -/
theorem majorant_integrable (lam : ℝ) :
    Integrable (majorant lam) ((volume : Measure ℝ).prod volume) := by
  have hu : Integrable (fun u : ℝ => Real.exp (-u^2)) := by
    simpa using (integrable_exp_neg_mul_sq (b := 1) (by norm_num))
  have hw : Integrable (fun w : ℝ => Real.exp (-(1/4)*w^2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  exact (hu.const_mul _).mul_prod hw

theorem gaussian_factor :
    (∫ w : ℝ, Real.exp (-w^2)) = Real.sqrt Real.pi := by
  simpa using integral_gaussian (1:ℝ)

end M12FockDomination

#print axioms M12FockDomination.fockProfile_eq_csinhc
#print axioms M12FockDomination.fockProfile_eq_mgf
#print axioms M12FockDomination.quartic_le_gaussian
#print axioms M12FockDomination.scaledIntegrand_le_majorant
#print axioms M12FockDomination.majorant_integrable
#print axioms M12FockDomination.gaussian_factor
