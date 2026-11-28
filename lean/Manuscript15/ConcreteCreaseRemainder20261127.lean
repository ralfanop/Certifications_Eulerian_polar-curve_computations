import Manuscript15.QuarticUniformTransfer20261127
import Manuscript15.CreaseAnalyticKernel20261127

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
  obtain ⟨h0,h1⟩ :=
    Manuscript15.CreaseAnalyticKernel20261127.inv_sqrt_first_order_remainder x hx
  exact ⟨h0,h1.trans (by nlinarith [sq_nonneg x])⟩

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
    have hconst : IntervalIntegrable (fun _ : ℝ => k) volume 0 u :=
      continuous_const.intervalIntegrable _ _
    have hpow : IntervalIntegrable (fun t : ℝ => a*t^2) volume 0 u := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_sub hconst hpow,
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
      exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos (2*(n+3))))
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
      exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos (2*(n+3))))
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


theorem concrete_crease_sixth_remainder (k u : ℝ)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 3/2) (hu : |u| ≤ 1/8) :
    |crease k u - Manuscript15.CrossQuartic20261125.creaseQuarticJet k u|
      ≤ (81920/3:ℝ)*|u|^6 := by
  let r := |u|
  let y := phase k u
  let a := k*(1+k^2)/6
  let e := y-k*u
  let b := k*a+k^4/24
  let H := 1+u^2/2+u^4/24
  let Q := 1-k^2*u^2/2+b*u^4
  have hr0 : 0 ≤ r := abs_nonneg _
  have hr : r ≤ 1/8 := hu
  have hr2 : r^2 ≤ 1/64 := by
    calc
      _ ≤ (1/8:ℝ)^2 := by gcongr
      _ = _ := by norm_num
  have hr5 : r^5 ≤ (1/64:ℝ)*r^3 := by
    calc
      r^5 = r^2*r^3 := by ring
      _ ≤ _ := by gcongr
  have hr3 : r^3 ≤ (1/64:ℝ)*r := by
    calc
      r^3 = r^2*r := by ring
      _ ≤ _ := by gcongr
  have hr4 : r^4 ≤ 1/4096 := by
    calc
      r^4 = (r^2)^2 := by ring
      _ ≤ (1/64:ℝ)^2 := by gcongr
      _ = _ := by norm_num
  have hr8 : r^8 ≤ r^6 := by
    calc
      r^8 = r^6*r^2 := by ring
      _ ≤ r^6*1 := by gcongr; linarith
      _ = _ := by ring
  have hk2 : k^2 ≤ (9/4:ℝ) := by nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hk1),
      mul_nonneg (sub_nonneg.mpr hk1) (show 0 ≤ k+3/2 by linarith)]
  have hk4 : k^4 ≤ (81/16:ℝ) := by
    calc
      k^4 = (k^2)^2 := by ring
      _ ≤ (9/4:ℝ)^2 := by gcongr
      _ = _ := by norm_num
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    calc
      a ≤ (3/2:ℝ)*(1+9/4)/6 := by dsimp [a]; gcongr
      _ ≤ _ := by norm_num
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 2 := by
    calc
      b ≤ (3/2:ℝ)*1+(81/16)/24 := by dsimp [b]; gcongr
      _ ≤ _ := by norm_num
  have hku : |k*u| ≤ (3/2:ℝ)*r := by
    rw [abs_mul, abs_of_nonneg hk0]
    gcongr
  have hjet : |e+a*u^3| ≤ 60*r^5 := by
    have hh := phase_cubic_remainder_local k u hk0 hk1 (hu.trans (by norm_num))
    convert hh using 1 <;> dsimp [e,y,a,r] <;> ring_nf
  have hau : |a*u^3| ≤ r^3 := by
    rw [abs_mul, abs_of_nonneg ha0, abs_pow]
    change a*r^3 ≤ r^3
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 (show 0 ≤ r^3 by positivity)
  have he : |e| ≤ 2*r^3 := by
    calc
      |e| = |(e+a*u^3)+(-(a*u^3))| := by congr 1 <;> ring
      _ ≤ |e+a*u^3| + |-(a*u^3)| := abs_add_le _ _
      _ ≤ 60*r^5+r^3 := by rw [abs_neg]; exact add_le_add hjet hau
      _ ≤ _ := by linarith
  have hy : |y| ≤ 2*r := by
    calc
      |y| = |e+k*u| := by dsimp [e]; congr 1 <;> ring
      _ ≤ |e| + |k*u| := abs_add_le _ _
      _ ≤ 2*r^3+(3/2:ℝ)*r := add_le_add he hku
      _ ≤ _ := by linarith
  have hsum : |y+k*u| ≤ (7/2:ℝ)*r := by
    calc
      _ ≤ |y| + |k*u| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hysq : |y^2| ≤ 4*r^2 := by
    rw [abs_pow]
    calc
      _ ≤ (2*r)^2 := by gcongr
      _ = _ := by ring
  have hkusq : |(k*u)^2| ≤ (9/4:ℝ)*r^2 := by
    rw [abs_pow]
    calc
      _ ≤ ((3/2:ℝ)*r)^2 := by gcongr
      _ = _ := by ring
  have hsumsq : |y^2+(k*u)^2| ≤ (25/4:ℝ)*r^2 := by
    calc
      _ ≤ |y^2| + |(k*u)^2| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hsq : |y^2-(k^2*u^2-2*k*a*u^4)| ≤ 184*r^6 := by
    have hid : y^2-(k^2*u^2-2*k*a*u^4) =
        2*(k*u)*(e+a*u^3)+e^2 := by dsimp [e]; ring
    rw [hid]
    calc
      _ ≤ |2*(k*u)*(e+a*u^3)| + |e^2| := abs_add_le _ _
      _ = 2*|k*u| * |e+a*u^3| + |e|^2 := by
        rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      _ ≤ 2*((3/2:ℝ)*r)*(60*r^5)+(2*r^3)^2 := by gcongr
      _ = _ := by ring
  have hfour : |y^4-k^4*u^4| ≤ 44*r^6 := by
    have hid : y^4-k^4*u^4 = e*(y+k*u)*(y^2+(k*u)^2) := by
      dsimp [e]; ring
    rw [hid, abs_mul, abs_mul]
    calc
      _ ≤ (2*r^3)*((7/2:ℝ)*r)*((25/4:ℝ)*r^2) := by gcongr
      _ ≤ _ := by nlinarith [show 0 ≤ r^6 by positivity]
  have hcos : |Real.cos y-Q| ≤ 222*r^6 := by
    have hy1 : |y| ≤ 1/2 := by linarith
    have ht := cos_fourth_remainder y hy1
    have hid : Real.cos y-Q = (Real.cos y-(1-y^2/2+y^4/24)) +
        (-(y^2-(k^2*u^2-2*k*a*u^4))/2)+(y^4-k^4*u^4)/24 := by
      dsimp [Q,b]; ring
    rw [hid]
    calc
      _ ≤ |Real.cos y-(1-y^2/2+y^4/24)| +
          |-(y^2-(k^2*u^2-2*k*a*u^4))/2| + |(y^4-k^4*u^4)/24| := by
        exact (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
      _ ≤ 2*(2*r)^6+(184*r^6)/2+(44*r^6)/24 := by
        rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0:ℝ)<2),
          abs_div, abs_of_pos (by norm_num : (0:ℝ)<24)]
        gcongr
      _ ≤ _ := by nlinarith [show 0 ≤ r^6 by positivity]
  have hH : |H| ≤ 2 := by
    have hH0 : 0 ≤ H := by dsimp [H]; positivity
    rw [abs_of_nonneg hH0]
    have hu2 : u^2 = r^2 := by dsimp [r]; simp
    have hu4 : u^4 = r^4 := by dsimp [r]; rw [← abs_pow, abs_of_nonneg (by positivity)]
    dsimp [H]
    rw [hu2,hu4]
    linarith
  have hcosh : |Real.cosh u-H| ≤ 2*r^6 :=
    cosh_fourth_remainder u (hu.trans (by norm_num))
  have hpoly : |H*Q-1-Manuscript15.CrossQuartic20261125.creaseQuarticJet k u| ≤ 3*r^6 := by
    have hid : H*Q-1-Manuscript15.CrossQuartic20261125.creaseQuarticJet k u =
        (b/2-k^2/48)*u^6+(b/24)*u^8 := by
      dsimp [H,Q,b,a,Manuscript15.CrossQuartic20261125.creaseQuarticJet]
      ring
    rw [hid]
    have hc : |b/2-k^2/48| ≤ 2 := by
      apply abs_le.mpr
      constructor <;> linarith [sq_nonneg k]
    have hd : |b/24| ≤ 1 := by
      rw [abs_of_nonneg (by positivity : 0 ≤ b/24)]
      linarith
    calc
      _ ≤ |(b/2-k^2/48)*u^6| + |(b/24)*u^8| := abs_add_le _ _
      _ = |b/2-k^2/48| * r^6 + |b/24| * r^8 := by
        rw [abs_mul, abs_mul, abs_pow, abs_pow]
      _ ≤ 2*r^6+1*r^6 := by gcongr
      _ = _ := by ring
  have hid : crease k u-Manuscript15.CrossQuartic20261125.creaseQuarticJet k u =
      (Real.cosh u-H)*Real.cos y+H*(Real.cos y-Q)+
      (H*Q-1-Manuscript15.CrossQuartic20261125.creaseQuarticJet k u) := by
    dsimp [crease,y]; ring
  rw [hid]
  calc
    _ ≤ |(Real.cosh u-H)*Real.cos y| + |H*(Real.cos y-Q)| +
        |H*Q-1-Manuscript15.CrossQuartic20261125.creaseQuarticJet k u| := by
      exact (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ (2*r^6)*1+2*(222*r^6)+3*r^6 := by
      rw [abs_mul,abs_mul]
      gcongr
      exact Real.abs_cos_le_one y
    _ ≤ _ := by nlinarith [show 0 ≤ r^6 by positivity]

theorem concrete_scaled_error_uniform_box
    (k ε v lam V L : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hk : k^2 = 1-80*lam*ε^2) (hk0 : 0 ≤ k)
    (hsmall : 80*L*ε^2 ≤ 3/4) (hbox : ε*V ≤ 1/8)
    (hv : |v| ≤ V) (hl : |lam| ≤ L) :
    |3*crease k (ε*v)/(20*ε^4)-(v^4/40+6*lam*v^2)| ≤
      ε^2*(4096*V^6+4*L*V^4+200*L^2*V^4) := by
  have hlam : -L ≤ lam := (abs_le.mp hl).1
  have hmul := mul_le_mul_of_nonneg_right hlam (show 0 ≤ 80*ε^2 by positivity)
  have hk2 : k^2 ≤ 7/4 := by linarith
  have hk1 : k ≤ 3/2 := by
    by_contra! h
    have hh := mul_pos (sub_pos.mpr h) (show 0 < k+3/2 by linarith)
    nlinarith
  have hu : |ε*v| ≤ 1/8 := by
    rw [abs_mul, abs_of_pos hε]
    exact (mul_le_mul_of_nonneg_left hv hε.le).trans hbox
  have hrem := concrete_crease_sixth_remainder k (ε*v) hk0 hk1 hu
  have hh := Manuscript15.QuarticUniformTransfer20261127.scaled_error_uniform_box
    crease k ε v lam (81920/3) V L hε hε1 hk (by norm_num) hv hl hrem
  convert hh using 1 <;> ring_nf


theorem phase_original_kernel (k u : ℝ) :
    phase k u = ∫ t in (0:ℝ)..u,
      (k/Real.sqrt (1+k^2)) /
        Real.sqrt ((Real.cosh t)^2-(k/Real.sqrt (1+k^2))^2) := by
  unfold phase
  apply intervalIntegral.integral_congr
  intro t _
  exact (Manuscript15.CreaseAnalyticKernel20261127.actual_phase_kernel_reparametrization k t).symm


theorem concrete_self_dual_remainder (u : ℝ) (hu : |u| ≤ 1/8) :
    |crease 1 u-u^4/6| ≤ (81920/3:ℝ)*|u|^6 := by
  have h := concrete_crease_sixth_remainder 1 u (by norm_num) (by norm_num) hu
  norm_num [Manuscript15.CrossQuartic20261125.creaseQuarticJet] at h
  convert h using 1 <;> ring_nf

theorem concrete_scaled_locally_uniform (V L : ℝ) (hV : 0 ≤ V) (hL : 0 ≤ L)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε lam v : ℝ, 0 < ε → ε < δ → |v| ≤ V → |lam| ≤ L →
      |3*crease (Real.sqrt (1-80*lam*ε^2)) (ε*v)/(20*ε^4)-
        (v^4/40+6*lam*v^2)| < η := by
  let K : ℝ := 4096*V^6+4*L*V^4+200*L^2*V^4
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let δ : ℝ := min 1 (min (1/(8*(V+1))) (min (1/(160*(L+1))) (η/(K+1))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ,hδ,?_⟩
  intro ε lam v hε heδ hv hl
  have he1 : ε ≤ 1 := by
    exact heδ.le.trans (min_le_left _ _)
  have heV : ε ≤ 1/(8*(V+1)) :=
    heδ.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heL : ε ≤ 1/(160*(L+1)) :=
    heδ.le.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have heK : ε < η/(K+1) :=
    heδ.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hbox : ε*V ≤ 1/8 := by
    have h := (le_div_iff₀ (show 0 < 8*(V+1) by positivity)).mp heV
    nlinarith
  have hε2 : ε^2 ≤ ε := by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr he1)]
  have hsmall : 80*L*ε^2 ≤ 3/4 := by
    have h := (le_div_iff₀ (show 0 < 160*(L+1) by positivity)).mp heL
    have hmul := mul_le_mul_of_nonneg_left hε2 (show 0 ≤ 80*L by positivity)
    nlinarith
  have hlup : lam ≤ L := (abs_le.mp hl).2
  have hmul := mul_le_mul_of_nonneg_right hlup (show 0 ≤ 80*ε^2 by positivity)
  have hrad : 0 ≤ 1-80*lam*ε^2 := by linarith
  have h := concrete_scaled_error_uniform_box (Real.sqrt (1-80*lam*ε^2))
    ε v lam V L hε he1 (Real.sq_sqrt hrad) (Real.sqrt_nonneg _)
    hsmall hbox hv hl
  have hkη := (lt_div_iff₀ (show 0 < K+1 by positivity)).mp heK
  have hmulK := mul_le_mul_of_nonneg_right hε2 hK
  exact h.trans_lt (show ε^2*K < η by nlinarith)

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
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.concrete_crease_sixth_remainder
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.concrete_scaled_error_uniform_box
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.phase_original_kernel
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.concrete_self_dual_remainder
#print axioms Manuscript15.ConcreteCreaseRemainder20261127.concrete_scaled_locally_uniform
