import CriticalWindowComplexMGF

/-! M12 §9: genuine sixth-order remainder of the actual uniform MGF and its
principal logarithm. The proof sums the convergent sinh tail and applies the
Mathlib complex logarithm Taylor bound, rather than merely comparing jets. -/
namespace M12CriticalRemainder
open Complex

noncomputable def coeffTerm (z : ℂ) (n : ℕ) : ℂ :=
  z^(2*n) / ((2*n+1).factorial : ℂ)

theorem hasSum_csinhc (z : ℂ) (hz : z ≠ 0) :
    HasSum (coeffTerm z) (M12ComplexMGF.csinhc z) := by
  rw [M12ComplexMGF.csinhc, if_neg hz]
  convert (Complex.hasSum_sinh z).div_const z using 1 with n
  unfold coeffTerm
  rw [pow_succ]
  field_simp

theorem tail_term_bound (z : ℂ) (hz : ‖z‖ ≤ 1/2) (n : ℕ) :
    ‖coeffTerm z (n+3)‖ ≤ ‖z‖^6 * (1/4 : ℝ)^n := by
  simp only [coeffTerm, norm_div, norm_pow, Complex.norm_natCast]
  have hf : (1 : ℝ) ≤ ((2*(n+3)+1).factorial : ℝ) := by
    have hp := Nat.factorial_pos (2*(n+3)+1)
    exact_mod_cast (show 1 ≤ (2*(n+3)+1).factorial by omega)
  have hb : ‖z‖^2 ≤ (1/4 : ℝ) := by
    nlinarith [norm_nonneg z, mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hz)]
  calc
    ‖z‖^(2*(n+3)) / ((2*(n+3)+1).factorial : ℝ) ≤ ‖z‖^(2*(n+3)) := by
      apply (div_le_iff₀ (by positivity)).2
      have h := mul_le_mul_of_nonneg_left hf (pow_nonneg (norm_nonneg z) (2*(n+3)))
      simpa only [mul_one] using h
    _ = ‖z‖^6 * (‖z‖^2)^n := by
      rw [show 2*(n+3)=6+2*n by omega, pow_add, pow_mul]
    _ ≤ ‖z‖^6 * (1/4 : ℝ)^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) hb n) (by positivity)

theorem csinhc_sixth_remainder (z : ℂ) (hz : ‖z‖ ≤ 1/2) :
    ‖M12ComplexMGF.csinhc z - (1+z^2/6+z^4/120)‖ ≤ 2*‖z‖^6 := by
  by_cases h0 : z = 0
  · simp [h0, M12ComplexMGF.csinhc]
  have hf := hasSum_csinhc z h0
  have hp : ∑ n ∈ Finset.range 3, coeffTerm z n = 1+z^2/6+z^4/120 := by
    norm_num [coeffTerm, Finset.sum_range_succ] <;> ring
  have hs := hf.summable.sum_add_tsum_nat_add 3
  rw [hf.tsum_eq, hp] at hs
  have heq : M12ComplexMGF.csinhc z - (1+z^2/6+z^4/120) =
      ∑' n : ℕ, coeffTerm z (n+3) := by
    rw [← hs]
    ring
  have hg : HasSum (fun n : ℕ => ‖z‖^6 * (1/4 : ℝ)^n) (‖z‖^6 * (1-1/4)⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
      (by norm_num : (1/4:ℝ) < 1)).mul_left _
  have hn : Summable (fun n : ℕ => ‖coeffTerm z (n+3)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (tail_term_bound z hz) hg.summable
  rw [heq]
  calc
    ‖∑' n : ℕ, coeffTerm z (n+3)‖ ≤ ∑' n : ℕ, ‖coeffTerm z (n+3)‖ :=
      norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, ‖z‖^6*(1/4 : ℝ)^n :=
      hn.tsum_le_tsum (tail_term_bound z hz) hg.summable
    _ = ‖z‖^6 * (1-1/4)⁻¹ := hg.tsum_eq
    _ ≤ 2*‖z‖^6 := by
      norm_num
      nlinarith [pow_nonneg (norm_nonneg z) 6]

theorem logTaylor_three (w : ℂ) : Complex.logTaylor 3 w = w-w^2/2 := by
  norm_num [Complex.logTaylor, Finset.sum_range_succ] <;> ring

theorem csinhc_log_sixth_remainder (z : ℂ) (hz : ‖z‖ ≤ 1/2) :
    ‖Complex.log (M12ComplexMGF.csinhc z) - (z^2/6-z^4/180)‖ ≤ 5*‖z‖^6 := by
  let t : ℝ := ‖z‖
  let a : ℂ := z^2/6
  let b : ℂ := z^4/120
  let w : ℂ := M12ComplexMGF.csinhc z-1
  let r : ℂ := M12ComplexMGF.csinhc z-(1+a+b)
  have ht : 0 ≤ t := norm_nonneg _
  have ht' : t ≤ 1/2 := hz
  have ht2 : t^2 ≤ 1/4 := by nlinarith [mul_nonneg ht (sub_nonneg.mpr ht')]
  have ht4 : t^4 ≤ t^2/4 := by
    nlinarith only [mul_le_mul_of_nonneg_right ht2 (sq_nonneg t)]
  have ht6 : t^6 ≤ t^4/4 := by
    nlinarith only [mul_le_mul_of_nonneg_right ht2 (pow_nonneg ht 4)]
  have ha : ‖a‖ = t^2/6 := by simp [a, t, norm_div, norm_pow]
  have hb : ‖b‖ = t^4/120 := by simp [b, t, norm_div, norm_pow]
  have hr : ‖r‖ ≤ 2*t^6 := csinhc_sixth_remainder z hz
  have hw_a : w-a=r+b := by dsimp [w,r,a,b]; ring
  have hwa : ‖w-a‖ ≤ t^4 := by
    rw [hw_a]
    calc
      ‖r+b‖ ≤ ‖r‖+‖b‖ := norm_add_le _ _
      _ ≤ t^4 := by rw [hb]; linarith only [hr,ht6,pow_nonneg ht 4]
  have hw : ‖w‖ ≤ t^2 := by
    calc
      ‖w‖ = ‖(w-a)+a‖ := by rw [sub_add_cancel]
      _ ≤ ‖w-a‖+‖a‖ := norm_add_le _ _
      _ ≤ t^2 := by rw [ha]; linarith only [hwa,ht4,sq_nonneg t]
  have hwplus : ‖w+a‖ ≤ 2*t^2 := by
    calc
      ‖w+a‖ ≤ ‖w‖+‖a‖ := norm_add_le _ _
      _ ≤ 2*t^2 := by rw [ha]; linarith only [hw,sq_nonneg t]
  have hwsq : ‖w^2-a^2‖ ≤ 2*t^6 := by
    rw [show w^2-a^2=(w-a)*(w+a) by ring, norm_mul]
    calc
      ‖w-a‖*‖w+a‖ ≤ t^4*(2*t^2) :=
        mul_le_mul hwa hwplus (norm_nonneg _) (pow_nonneg ht 4)
      _ = 2*t^6 := by ring
  have hwlt : ‖w‖ < 1 := by linarith only [hw,ht2]
  have hinv : (1-‖w‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (sub_pos.mpr hwlt)).2
    linarith only [hw,ht2]
  have hlog := Complex.norm_log_sub_logTaylor_le 2 hwlt
  have h1 : (1:ℂ)+w = M12ComplexMGF.csinhc z := by dsimp [w]; ring
  rw [h1, logTaylor_three] at hlog
  have hlog' : ‖Complex.log (M12ComplexMGF.csinhc z)-(w-w^2/2)‖ ≤ t^6 := by
    have hpow : ‖w‖^3 ≤ t^6 := by
      calc
        ‖w‖^3 ≤ (t^2)^3 := pow_le_pow_left₀ (norm_nonneg _) hw _
        _ = t^6 := by ring
    calc
      _ ≤ ‖w‖^3*(1-‖w‖)⁻¹/(2+1) := by simpa using hlog
      _ ≤ t^6*2/(2+1) := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul hpow hinv (by positivity) (pow_nonneg ht 6)
      _ ≤ t^6 := by nlinarith [pow_nonneg ht 6]
  have hjet : a+b-a^2/2 = z^2/6-z^4/180 := by dsimp [a,b]; ring
  rw [← hjet]
  have he : (w-w^2/2)-(a+b-a^2/2)=r-(w^2-a^2)/2 := by
    dsimp [w,r,a,b]; ring
  have hpoly : ‖(w-w^2/2)-(a+b-a^2/2)‖ ≤ 3*t^6 := by
    rw [he]
    calc
      ‖r-(w^2-a^2)/2‖ ≤ ‖r‖+‖(w^2-a^2)/2‖ := norm_sub_le _ _
      _ ≤ 3*t^6 := by
        rw [norm_div, Complex.norm_two]
        linarith only [hr,hwsq]
  calc
    ‖Complex.log (M12ComplexMGF.csinhc z)-(a+b-a^2/2)‖ ≤
        ‖Complex.log (M12ComplexMGF.csinhc z)-(w-w^2/2)‖+
        ‖(w-w^2/2)-(a+b-a^2/2)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 5*‖z‖^6 := by
      change _ ≤ 5*t^6
      linarith only [hlog',hpoly,pow_nonneg ht 6]

theorem standardized_log_sixth_remainder (z : ℂ) (hz : ‖z‖ ≤ 1/4) :
    ‖Complex.log (M12ComplexMGF.mgf z)-(z^2/2-z^4/20)‖ ≤ 320*‖z‖^6 := by
  have hs : (Real.sqrt 3)^2 = (3:ℝ) := Real.sq_sqrt (by norm_num)
  have hs' : Real.sqrt 3 ≤ 2 := by nlinarith [Real.sqrt_nonneg 3]
  have hnorm : ‖(Real.sqrt 3 : ℂ)*z‖ ≤ 2*‖z‖ := by
    rw [norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg 3)]
    exact mul_le_mul_of_nonneg_right hs' (norm_nonneg _)
  have hsmall : ‖(Real.sqrt 3 : ℂ)*z‖ ≤ 1/2 := by linarith only [hnorm,hz]
  have hc : (Real.sqrt 3 : ℂ)^2 = 3 := by exact_mod_cast hs
  have hc4 : (Real.sqrt 3 : ℂ)^4 = 9 := by
    calc
      (Real.sqrt 3 : ℂ)^4 = ((Real.sqrt 3 : ℂ)^2)^2 := by ring
      _ = 9 := by rw [hc]; norm_num
  have h := csinhc_log_sixth_remainder ((Real.sqrt 3 : ℂ)*z) hsmall
  rw [mul_pow, hc, mul_pow, hc4] at h
  have hj : 3*z^2/6-9*z^4/180 = z^2/2-z^4/20 := by ring
  rw [hj] at h
  unfold M12ComplexMGF.mgf
  calc
    _ ≤ 5*‖(Real.sqrt 3 : ℂ)*z‖^6 := h
    _ ≤ 5*(2*‖z‖)^6 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm _) (by norm_num)
    _ = 320*‖z‖^6 := by ring

end M12CriticalRemainder

#print axioms M12CriticalRemainder.hasSum_csinhc
#print axioms M12CriticalRemainder.tail_term_bound
#print axioms M12CriticalRemainder.csinhc_sixth_remainder
#print axioms M12CriticalRemainder.logTaylor_three
#print axioms M12CriticalRemainder.csinhc_log_sixth_remainder
#print axioms M12CriticalRemainder.standardized_log_sixth_remainder
