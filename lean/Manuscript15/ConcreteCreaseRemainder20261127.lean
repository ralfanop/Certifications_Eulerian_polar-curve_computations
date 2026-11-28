import Manuscript15.QuarticUniformTransfer20261127

/-! Source: M15 26 Nov, FRENCH_YEN_1992_2002(4), prop:cross-crease15.
Real-coordinate prerequisite to the concrete sixth-order remainder.
The definitions use the u-coordinate density from cor:ridge-crease.
The pointwise density estimate below still takes the elementary sinh
estimates as hypotheses. No claim that the actual phase or crease
remainder has been kernel-certified at this checkpoint. -/

noncomputable section
open MeasureTheory
namespace Manuscript15.ConcreteCreaseRemainder20261127

def density (k t : ℝ) : ℝ :=
  k / Real.sqrt (1 + (1+k^2)*(Real.sinh t)^2)

def phase (k u : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..u, density k t

def crease (k u : ℝ) : ℝ :=
  Real.cosh u * Real.cos (phase k u) - 1

theorem sqrt_reciprocal_remainder (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 1 / Real.sqrt (1+x) - 1 + x/2 ∧
    1 / Real.sqrt (1+x) - 1 + x/2 ≤ x^2 := by
  let s := Real.sqrt (1+x)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s^2 = 1+x := Real.sq_sqrt (by linarith)
  have hs : 1 ≤ s := by
    by_contra! h
    have hp := mul_pos (sub_pos.mpr h) (show 0 < 1+s by linarith)
    nlinarith
  have hspos : 0 < s := by linarith
  have hiden : 1/s - 1 + x/2 = (s-1)^2*(s+2)/(2*s) := by
    calc
      _ = 1/s - 1 + (s^2-1)/2 := by rw [show x = s^2-1 by linarith]
      _ = _ := by field_simp [hspos.ne'] <;> ring
  have hx' : x = (s-1)*(s+1) := by nlinarith
  change 0 ≤ 1/s - 1 + x/2 ∧ 1/s - 1 + x/2 ≤ x^2
  rw [hiden]
  constructor
  · positivity
  · apply (div_le_iff₀ (show 0 < 2*s by positivity)).2
    have hfour : 4 ≤ (s+1)^2 := by
      nlinarith [sq_nonneg (s-1)]
    have hfactor : s+2 ≤ 2*s*(s+1)^2 := by
      have hm := mul_nonneg hs0 (sub_nonneg.mpr hfour)
      nlinarith
    calc
      (s-1)^2*(s+2) ≤ (s-1)^2*(2*s*(s+1)^2) :=
        mul_le_mul_of_nonneg_left hfactor (sq_nonneg _)
      _ = x^2*(2*s) := by rw [hx']; ring

theorem density_continuous (k : ℝ) : Continuous (density k) := by
  unfold density
  apply continuous_const.div
  · fun_prop
  · intro t
    exact (Real.sqrt_pos.2 (by positivity)).ne'

theorem density_nonnegative_bounded (k t : ℝ) (hk : 0 ≤ k) :
    0 ≤ density k t ∧ density k t ≤ k := by
  let s := Real.sqrt (1+(1+k^2)*(Real.sinh t)^2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s^2 = 1+(1+k^2)*(Real.sinh t)^2 :=
    Real.sq_sqrt (by positivity)
  have hx : 0 ≤ (1+k^2)*(Real.sinh t)^2 := by positivity
  have hs : 1 ≤ s := by
    by_contra! h
    have hp := mul_pos (sub_pos.mpr h) (show 0 < 1+s by linarith)
    nlinarith
  change 0 ≤ k/s ∧ k/s ≤ k
  refine ⟨div_nonneg hk hs0, ?_⟩
  apply (div_le_iff₀ (show 0 < s by linarith)).2
  nlinarith [mul_nonneg hk (sub_nonneg.mpr hs)]

theorem density_quadratic_remainder_from_sinh (k t : ℝ)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 3/2)
    (hS : |Real.sinh t| ≤ 2*|t|)
    (hSt : |Real.sinh t-t| ≤ |t|^3) :
    |density k t - (k-k*(1+k^2)/2*t^2)| ≤ 300*|t|^4 := by
  let x := (1+k^2)*(Real.sinh t)^2
  let r := 1/Real.sqrt (1+x)-1+x/2
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hr := sqrt_reciprocal_remainder x hx0
  have hrabs : |r| ≤ x^2 := by
    change |1/Real.sqrt (1+x)-1+x/2| ≤ x^2
    rw [abs_of_nonneg hr.1]
    exact hr.2
  have hk2 : k^2 ≤ (3/2:ℝ)^2 := by gcongr
  have hkfac : 1+k^2 ≤ (13/4:ℝ) := by linarith
  have hs2 : (Real.sinh t)^2 ≤ 4*|t|^2 := by
    calc
      _ = |Real.sinh t|^2 := by simp
      _ ≤ (2*|t|)^2 := by gcongr
      _ = _ := by ring
  have hx1 : x ≤ 13*|t|^2 := by
    calc
      x ≤ (13/4:ℝ)*(4*|t|^2) := by dsimp [x]; gcongr
      _ = _ := by ring
  have hsum : |Real.sinh t+t| ≤ 3*|t| := by
    calc
      _ ≤ |Real.sinh t| + |t| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hsqdiff : |(Real.sinh t)^2-t^2| ≤ 3*|t|^4 := by
    rw [show (Real.sinh t)^2-t^2 = (Real.sinh t-t)*(Real.sinh t+t) by ring, abs_mul]
    calc
      _ ≤ |t|^3*(3*|t|) := by gcongr
      _ = _ := by ring
  have hcoef : k*(1+k^2)/2 ≤ (3:ℝ) := by
    calc
      _ ≤ (3/2:ℝ)*(13/4)/2 := by gcongr
      _ ≤ _ := by norm_num
  have hiden : density k t - (k-k*(1+k^2)/2*t^2) =
      k*r + (-(k*(1+k^2)/2))*((Real.sinh t)^2-t^2) := by
    dsimp [density, r, x]
    ring
  rw [hiden]
  calc
    _ ≤ |k*r| + |(-(k*(1+k^2)/2))*((Real.sinh t)^2-t^2)| := abs_add_le _ _
    _ = k*|r| + (k*(1+k^2)/2)*|(Real.sinh t)^2-t^2| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hk0, abs_neg,
        abs_of_nonneg (show 0 ≤ k*(1+k^2)/2 by positivity)]
    _ ≤ (3/2:ℝ)*(13*|t|^2)^2 + 3*(3*|t|^4) := by
      have hrbound : |r| ≤ (13*|t|^2)^2 := hrabs.trans (by gcongr)
      gcongr
    _ ≤ _ := by nlinarith [show 0 ≤ |t|^4 by positivity]


/- The exponential Taylor bound supplies the previously assumed local sinh estimates. -/
theorem sinh_local_bounds (t : ℝ) (ht : |t| ≤ 1) :
    |Real.sinh t| ≤ 2*|t| ∧ |Real.sinh t-t| ≤ |t|^3 := by
  have hp := Real.exp_bound (x := t) (n := 3) ht (by decide)
  have hm := Real.exp_bound (x := -t) (n := 3) (by simpa using ht) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hp hm
  simp only [abs_neg] at hm
  have he : Real.sinh t-t =
      ((Real.exp t-(1+t+t^2/2))-(Real.exp (-t)-(1-t+t^2/2)))/2 := by
    rw [Real.sinh_eq]
    ring
  have hr : |Real.sinh t-t| ≤ |t|^3 := by
    rw [he, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).2
    have hp' : |Real.exp t-(1+t+t^2/2)| ≤ (2/9:ℝ)*|t|^3 := by
      convert hp using 1 <;> ring_nf
    have hm' : |Real.exp (-t)-(1-t+t^2/2)| ≤ (2/9:ℝ)*|t|^3 := by
      convert hm using 1 <;> ring_nf
    calc
      _ ≤ |Real.exp t-(1+t+t^2/2)| + |Real.exp (-t)-(1-t+t^2/2)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          (abs_add_le (Real.exp t-(1+t+t^2/2)) (-(Real.exp (-t)-(1-t+t^2/2))))
      _ ≤ _ := by linarith [hp',hm',show 0 ≤ |t|^3 by positivity]
  refine ⟨?_,hr⟩
  have hc : |t|^3 ≤ |t| := by
    calc
      |t|^3 = |t| * |t| * |t| := by ring
      _ ≤ 1*1*|t| := by gcongr
      _ = _ := by ring
  calc
    |Real.sinh t| = |(Real.sinh t-t)+t| := by congr 1 <;> ring
    _ ≤ |Real.sinh t-t| + |t| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem density_quadratic_remainder_local (k t : ℝ)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 3/2) (ht : |t| ≤ 1) :
    |density k t - (k-k*(1+k^2)/2*t^2)| ≤ 300*|t|^4 := by
  obtain ⟨hS,hSt⟩ := sinh_local_bounds t ht
  exact density_quadratic_remainder_from_sinh k t hk0 hk1 hS hSt


theorem phase_cubic_remainder_nonneg (k u : ℝ)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 3/2) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |phase k u - (k*u-k*(1+k^2)*u^3/6)| ≤ 60*u^5 := by
  let a : ℝ := k*(1+k^2)/2
  let p : ℝ → ℝ := fun t => k-a*t^2
  let e : ℝ → ℝ := fun t => density k t-p t
  have hp : Continuous p := by dsimp [p]; fun_prop
  have he : Continuous e := (density_continuous k).sub hp
  have hpoly : (∫ t in (0:ℝ)..u, p t) = k*u-k*(1+k^2)*u^3/6 := by
    dsimp [p]
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      ((continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_pow]
    simp [a, smul_eq_mul] <;> ring
  have heq : (∫ t in (0:ℝ)..u, e t) =
      phase k u - (k*u-k*(1+k^2)*u^3/6) := by
    dsimp [e, phase]
    rw [intervalIntegral.integral_sub ((density_continuous k).intervalIntegrable _ _)
      (hp.intervalIntegrable _ _), hpoly]
  have hmono : (∫ t in (0:ℝ)..u, |e t|) ≤
      ∫ t in (0:ℝ)..u, 300*t^4 := by
    apply intervalIntegral.integral_mono_on hu0
      (he.abs.intervalIntegrable _ _)
      ((continuous_const.mul (continuous_id.pow 4)).intervalIntegrable _ _)
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht.2.trans hu1
    have h := density_quadratic_remainder_local k t hk0 hk1 ht1
    rw [abs_of_nonneg ht0] at h
    exact h
  rw [← heq]
  calc
    _ ≤ (∫ t in (0:ℝ)..u, |e t|) := intervalIntegral.abs_integral_le_integral_abs hu0
    _ ≤ (∫ t in (0:ℝ)..u, 300*t^4) := hmono
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num <;> ring

theorem phase_neg (k u : ℝ) : phase k (-u) = -phase k u := by
  have hd : ∀ t : ℝ, density k (-t) = density k t := by
    intro t
    simp [density, Real.sinh_neg]
  unfold phase
  have h : (∫ t in (0:ℝ)..u, density k (-t)) =
      ∫ t in -u..(0:ℝ), density k t := by
    simpa only [neg_zero] using
      (intervalIntegral.integral_comp_neg (f := density k) (a := (0:ℝ)) (b := u))
  simp only [hd] at h
  rw [intervalIntegral.integral_symm, ← h]

theorem phase_cubic_remainder_local (k u : ℝ)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 3/2) (hu : |u| ≤ 1) :
    |phase k u - (k*u-k*(1+k^2)*u^3/6)| ≤ 60*|u|^5 := by
  rcases le_or_gt 0 u with h | h
  · rw [abs_of_nonneg h] at hu ⊢
    exact phase_cubic_remainder_nonneg k u hk0 hk1 h hu
  · have hu' : 0 ≤ -u := by linarith
    rw [abs_of_neg h] at hu ⊢
    have hh := phase_cubic_remainder_nonneg k (-u) hk0 hk1 hu' hu
    rw [phase_neg] at hh
    have hid : -phase k u - (k*(-u)-k*(1+k^2)*(-u)^3/6) =
        -(phase k u - (k*u-k*(1+k^2)*u^3/6)) := by ring
    rwa [hid, abs_neg] at hh


theorem even_series_tail_bound (x : ℝ) (hx : |x| ≤ 1/2)
    (f : ℕ → ℝ) (hs : Summable f)
    (hf : ∀ n : ℕ, |f (n+3)| ≤ |x|^6*(1/4:ℝ)^n) :
    |(∑' n, f n) - (f 0+f 1+f 2)| ≤ 2*|x|^6 := by
  have hg : HasSum (fun n : ℕ => (1/4:ℝ)^n) (4/3:ℝ) := by
    convert hasSum_geometric_of_lt_one (show (0:ℝ) ≤ 1/4 by norm_num)
      (show (1/4:ℝ) < 1 by norm_num) using 1 <;> norm_num
  have hgm := hg.mul_left (|x|^6)
  have hb := tsum_of_norm_bounded (f := fun n : ℕ => f (n+3)) hgm
    (fun n => by simpa only [Real.norm_eq_abs] using hf n)
  rw [Real.norm_eq_abs] at hb
  have hsplit := hs.sum_add_tsum_nat_add 3
  norm_num [Finset.sum_range_succ] at hsplit
  have he : (∑' n, f n) - (f 0+f 1+f 2) =
      ∑' n : ℕ, f (n+3) := by linarith
  rw [he]
  linarith [hb, show 0 ≤ |x|^6 by positivity]

theorem even_power_tail_majorant (x : ℝ) (hx : |x| ≤ 1/2) (n : ℕ) :
    |x|^(2*(n+3)) ≤ |x|^6*(1/4:ℝ)^n := by
  rw [show 2*(n+3) = 6+2*n by omega, pow_add, pow_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hsq : |x|^2 ≤ (1/4:ℝ) := by
    calc
      _ ≤ (1/2:ℝ)^2 := by gcongr
      _ = _ := by norm_num
  gcongr

theorem cos_fourth_remainder (x : ℝ) (hx : |x| ≤ 1/2) :
    |Real.cos x-(1-x^2/2+x^4/24)| ≤ 2*|x|^6 := by
  let f : ℕ → ℝ := fun n => (-1)^n*x^(2*n)/((2*n).factorial : ℝ)
  have hs : HasSum f (Real.cos x) := Real.hasSum_cos x
  have ht := even_series_tail_bound x hx f hs.summable (by
    intro n
    dsimp [f]
    rw [abs_div, abs_mul, abs_pow, abs_pow]
    norm_num
    have hfac : (1:ℝ) ≤ ((2*(n+3)).factorial : ℝ) := by
      exact_mod_cast (Nat.factorial_pos (2*(n+3)))
    have hpos : (0:ℝ) < ((2*(n+3)).factorial : ℝ) := by positivity
    rw [abs_of_pos hpos]
    calc
      _ ≤ |x|^(2*(n+3)) := by
        apply (div_le_iff₀ hpos).2
        nlinarith [mul_nonneg (show 0 ≤ |x|^(2*(n+3)) by positivity)
          (sub_nonneg.mpr hfac)]
      _ ≤ _ := even_power_tail_majorant x hx n)
  rw [hs.tsum_eq] at ht
  norm_num [f] at ht
  convert ht using 1 <;> ring_nf

theorem cosh_fourth_remainder (x : ℝ) (hx : |x| ≤ 1/2) :
    |Real.cosh x-(1+x^2/2+x^4/24)| ≤ 2*|x|^6 := by
  let f : ℕ → ℝ := fun n => x^(2*n)/((2*n).factorial : ℝ)
  have hs : HasSum f (Real.cosh x) := Real.hasSum_cosh x
  have ht := even_series_tail_bound x hx f hs.summable (by
    intro n
    dsimp [f]
    rw [abs_div, abs_pow]
    have hfac : (1:ℝ) ≤ ((2*(n+3)).factorial : ℝ) := by
      exact_mod_cast (Nat.factorial_pos (2*(n+3)))
    have hpos : (0:ℝ) < ((2*(n+3)).factorial : ℝ) := by positivity
    rw [abs_of_pos hpos]
    calc
      _ ≤ |x|^(2*(n+3)) := by
        apply (div_le_iff₀ hpos).2
        nlinarith [mul_nonneg (show 0 ≤ |x|^(2*(n+3)) by positivity)
          (sub_nonneg.mpr hfac)]
      _ ≤ _ := even_power_tail_majorant x hx n)
  rw [hs.tsum_eq] at ht
  norm_num [f] at ht
  convert ht using 1 <;> ring_nf

end Manuscript15.ConcreteCreaseRemainder20261127

#print axioms Manuscript15.ConcreteCreaseRemainder20261127.sqrt_reciprocal_remainder
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.density_continuous
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.density_nonnegative_bounded
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.density_quadratic_remainder_from_sinh
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.sinh_local_bounds
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.density_quadratic_remainder_local
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.phase_cubic_remainder_nonneg
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.phase_neg
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.phase_cubic_remainder_local
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.even_series_tail_bound
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.even_power_tail_majorant
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.cos_fourth_remainder
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.cosh_fourth_remainder
