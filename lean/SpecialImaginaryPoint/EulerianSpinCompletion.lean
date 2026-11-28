import SpecialImaginaryPoint.EulerianSpinLaw
import SpecialImaginaryPoint.EulerianLangevinRange

namespace M14.EulerianSpinLaw
open Filter Finset MeasureTheory
open scoped BigOperators Topology Interval
noncomputable section

theorem raw_one_factor (n : ℕ) (t : ℝ) :
    rawMoment n 1 t = Real.exp (spin n*t) *
      (∑ k ∈ Finset.range (n+1), level n k*(Real.exp (-t))^k) := by
  simp only [rawMoment,pow_one,exp_level_factor,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem q_eq_mean (n : ℕ) (hn : 0 < n) (t : ℝ) :
    q n t = mean n t / spin n := by
  have hp : 0 < P n (Real.exp (-t)) :=
    lt_of_lt_of_le zero_lt_one (P_ge_one n _ (Real.exp_pos _).le)
  unfold q normalizedMean mean
  rw [raw_one_factor,raw_zero_factor]
  field_simp [(spin_pos n hn).ne',hp.ne',Real.exp_ne_zero]
  <;> ring

theorem q_hasDerivAt (n : ℕ) (hn : 0 < n) (t : ℝ) :
    HasDerivAt (q n) (variance n t/spin n) t := by
  have hf : q n = fun u => mean n u/spin n := funext (q_eq_mean n hn)
  rw [hf]
  exact (mean_hasDerivAt n t).div_const _

theorem q_strictMono (n : ℕ) (hn : 0 < n) : StrictMono (q n) := by
  apply strictMono_of_deriv_pos
  · exact continuous_iff_continuousAt.mpr (fun t => (q_hasDerivAt n hn t).continuousAt)
  · intro t
    rw [(q_hasDerivAt n hn t).deriv]
    exact div_pos (variance_positive n hn t) (spin_pos n hn)

theorem level_reflect (n k : ℕ) (hk : k ≤ n) :
    level n (n-k) = -level n k := by
  unfold level spin
  rw [Nat.cast_sub hk]
  ring

theorem raw_reflect_zero (n : ℕ) (t : ℝ) :
    rawMoment n 0 (-t) = rawMoment n 0 t := by
  unfold rawMoment
  calc
    _ = ∑ k ∈ Finset.range (n+1), (level n (n-k))^0 *
        Real.exp (level n (n-k)*t) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
      rw [level_reflect n k hk']
      ring_nf
    _ = _ := by
      first
      | simpa using (Finset.sum_range_reflect
          (fun k => (level n k)^0*Real.exp (level n k*t)) (n+1))
      | exact?

theorem raw_reflect_one (n : ℕ) (t : ℝ) :
    rawMoment n 1 (-t) = -rawMoment n 1 t := by
  unfold rawMoment
  rw [← Finset.sum_neg_distrib]
  calc
    _ = ∑ k ∈ Finset.range (n+1), -(level n (n-k)^1 *
        Real.exp (level n (n-k)*t)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
      rw [level_reflect n k hk']
      ring_nf
    _ = _ := by
      first
      | simpa using (Finset.sum_range_reflect
          (fun k => -(level n k)^1*Real.exp (level n k*t)) (n+1))
      | exact?

theorem q_odd (n : ℕ) (hn : 0 < n) (t : ℝ) : q n (-t) = -q n t := by
  rw [q_eq_mean n hn,q_eq_mean n hn,mean,mean,raw_reflect_one,raw_reflect_zero]
  ring

theorem q_upper (n : ℕ) (hn : 0 < n) (t : ℝ) : q n t < 1 := by
  have h := scaled_deficit n hn t
  have hp := mul_pos (Real.exp_pos (-t)) (ratio_positive n hn _ (Real.exp_pos _).le)
  have hq : 0 < spin n*(1-q n t) := by rw [h]; exact hp
  exact sub_pos.mp (pos_of_mul_pos_left hq (spin_pos n hn).le)

theorem q_range_bound (n : ℕ) (hn : 0 < n) (t : ℝ) : q n t ∈ Set.Ioo (-1:ℝ) 1 := by
  have h := q_upper n hn (-t)
  rw [q_odd n hn] at h
  exact ⟨by linarith,q_upper n hn t⟩

theorem q_limit_top (n : ℕ) (hn : 0 < n) :
    Tendsto (q n) atTop (𝓝 1) := by
  have hr := (ratio_limit n hn).comp exp_neg_limit
  have h := exp_neg_limit.mul hr
  have hf : q n = fun t => 1-(Real.exp (-t)*ratio n (Real.exp (-t)))/spin n := by
    funext t
    have he := scaled_deficit n hn t
    apply (eq_sub_iff_add_eq).2
    have hs : (Real.exp (-t)*ratio n (Real.exp (-t)))/spin n = 1-q n t :=
      (div_eq_iff (spin_pos n hn).ne').2 (by linarith [mul_comm (spin n) (1-q n t)])
    linarith
  rw [hf]
  simpa only [zero_mul,zero_div,sub_zero,Function.comp_def] using
    (tendsto_const_nhds.sub (h.div_const (spin n)))

theorem q_range (n : ℕ) (hn : 0 < n) : Set.range (q n) = Set.Ioo (-1:ℝ) 1 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t,rfl⟩
    exact q_range_bound n hn t
  · intro y hy
    have ha : |y| < 1 := abs_lt.mpr hy
    have he : ∀ᶠ t in atTop, |y| < q n t :=
      (q_limit_top n hn).eventually (eventually_gt_nhds ha)
    obtain ⟨t,ht⟩ := (he.and (eventually_ge_atTop (0:ℝ))).exists
    have hl : q n (-t) ≤ y := by
      rw [q_odd n hn]
      linarith [neg_abs_le y]
    have hu : y ≤ q n t := by linarith [le_abs_self y]
    have hc : Continuous (q n) :=
      continuous_iff_continuousAt.mpr (fun x => (q_hasDerivAt n hn x).continuousAt)
    rcases intermediate_value_Icc (by linarith : -t ≤ t) hc.continuousOn
      (show y ∈ Set.Icc (q n (-t)) (q n t) from ⟨hl,hu⟩) with ⟨x,hx,heq⟩
    exact ⟨x,heq⟩

def inverseSpin (n : ℕ) : ℝ → ℝ := Function.invFun (q n)

theorem inverse_left (n : ℕ) (hn : 0 < n) : Function.LeftInverse (inverseSpin n) (q n) :=
  Function.leftInverse_invFun (q_strictMono n hn).injective

theorem inverse_right (n : ℕ) (hn : 0 < n) (y : ℝ) (hy : y ∈ Set.Ioo (-1:ℝ) 1) :
    q n (inverseSpin n y) = y := by
  rw [← q_range n hn] at hy
  rcases hy with ⟨t,rfl⟩
  rw [inverse_left n hn]

theorem inverse_strictMono (n : ℕ) (hn : 0 < n) :
    StrictMonoOn (inverseSpin n) (Set.Ioo (-1:ℝ) 1) := by
  intro a ha b hb hab
  apply (q_strictMono n hn).lt_iff_lt.mp
  rw [inverse_right n hn a ha,inverse_right n hn b hb]
  exact hab

theorem pow_succ_le_self (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (k : ℕ) :
    r^(k+1) ≤ r := by
  rw [pow_succ]
  exact mul_le_of_le_one_left hr (pow_le_one₀ hr hr1)

theorem P_upper_linear (n : ℕ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    P n r ≤ 1+(n:ℝ)*r := by
  unfold P
  rw [Finset.sum_range_succ']
  simp only [pow_zero]
  have h : (∑ k ∈ Finset.range n, r^(k+1)) ≤ ∑ _k ∈ Finset.range n, r :=
    Finset.sum_le_sum (fun k hk => pow_succ_le_self r hr hr1 k)
  simpa using (add_le_add_right h 1)

theorem A_upper_linear (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    A n r ≤ 1+(n:ℝ)^2*r := by
  cases n with
  | zero => omega
  | succ n =>
    unfold A
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_one,pow_zero,one_mul]
    have h : (∑ k ∈ Finset.range n, ((k+1+1:ℕ):ℝ)*r^(k+1)) ≤
        ∑ _k ∈ Finset.range n, ((n+1:ℕ):ℝ)*r := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k+1+1 ≤ n+1 := by have := Finset.mem_range.mp hk; omega
      exact mul_le_mul (by exact_mod_cast hk') (pow_succ_le_self r hr hr1 k)
        (pow_nonneg hr _) (by positivity)
    have hh : (∑ k ∈ Finset.range n, ((k+1+1:ℕ):ℝ)*r^(k+1)) ≤
        (n:ℝ)*((n+1:ℕ):ℝ)*r := by simpa [mul_assoc] using h
    have hp : 0 ≤ ((n+1:ℕ):ℝ)*r := by positivity
    push_cast at hh hp ⊢
    nlinarith

theorem P_upper_uniform (n : ℕ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    P n r ≤ (n:ℝ)+1 := by
  have h := P_upper_linear n r hr hr1
  nlinarith [mul_nonneg (show 0 ≤ (n:ℝ) by positivity) (sub_nonneg.mpr hr1)]

theorem log_ratio_bound (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    |Real.log (ratio n r)| ≤ (n:ℝ)^2*r := by
  have ha := A_ge_one n hn r hr
  have hp := P_ge_one n r hr
  have hau := A_upper_linear n hn r hr hr1
  have hpu := P_upper_linear n r hr hr1
  have ha0 : 0 < A n r := by linarith
  have hp0 : 0 < P n r := by linarith
  have hla := Real.log_nonneg ha
  have hlp := Real.log_nonneg hp
  have hla' := Real.log_le_sub_one_of_pos ha0
  have hlp' := Real.log_le_sub_one_of_pos hp0
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (n:ℝ)*r ≤ (n:ℝ)^2*r := by
    have h : 0 ≤ (n:ℝ)*r := by positivity
    nlinarith [mul_nonneg h (sub_nonneg.mpr hn1)]
  rw [ratio,Real.log_div ha0.ne' hp0.ne',abs_le]
  constructor <;> linarith

theorem quantitative_t (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    |t+Real.log (spin n*(1-q n t))| ≤ (n:ℝ)^2*Real.exp (-t) := by
  rw [log_saturation_identity n hn]
  exact log_ratio_bound n hn _ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))

theorem exponential_deficit_bound (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t) ≤ ((n:ℝ)+1)*(spin n*(1-q n t)) := by
  let r := Real.exp (-t)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp := P_ge_one n r hr.le
  have ha := A_ge_one n hn r hr.le
  have hu := P_upper_uniform n r hr.le hr1
  have hp0 : 0 < P n r := by linarith
  have ha' : P n r ≤ ((n:ℝ)+1)*A n r := by
    have hh := mul_le_mul_of_nonneg_left ha (show 0 ≤ (n:ℝ)+1 by positivity)
    linarith
  rw [scaled_deficit n hn]
  change r ≤ ((n:ℝ)+1)*(r*(A n r/P n r))
  rw [← mul_div_assoc,← mul_div_assoc]
  apply (le_div_iff₀ hp0).2
  calc
    r*P n r ≤ r*(((n:ℝ)+1)*A n r) := mul_le_mul_of_nonneg_left ha' hr.le
    _ = _ := by ring

theorem quantitative_inverse (n : ℕ) (hn : 0 < n) (y : ℝ) (hy : 0 ≤ y) (hy1 : y < 1) :
    |inverseSpin n y+Real.log (spin n*(1-y))| ≤
      (n:ℝ)^2*((n:ℝ)+1)*(spin n*(1-y)) := by
  have hm : y ∈ Set.Ioo (-1:ℝ) 1 := ⟨by linarith,hy1⟩
  have h := inverse_right n hn y hm
  have hz : q n 0 = 0 := by
    have he := q_odd n hn 0
    simp only [neg_zero] at he
    linarith
  have ht : 0 ≤ inverseSpin n y := by
    apply (q_strictMono n hn).le_iff_le.mp
    rw [hz,h]
    exact hy
  have hq := quantitative_t n hn (inverseSpin n y) ht
  have he := exponential_deficit_bound n hn (inverseSpin n y) ht
  rw [h] at hq he
  calc
    _ ≤ (n:ℝ)^2*Real.exp (-inverseSpin n y) := hq
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left he (sq_nonneg (n:ℝ))
      simpa only [mul_assoc] using hh

/-- Squared deviation from the maximal spin dominates the variance. -/
theorem variance_center_bound (n : ℕ) (t : ℝ) :
    variance n t ≤
      (∑ k ∈ Finset.range (n+1), (k:ℝ)^2*(Real.exp (-t))^k)/P n (Real.exp (-t)) := by
  have hs : (∑ k ∈ Finset.range (n+1), (level n k-spin n)^2*Real.exp (level n k*t)) =
      rawMoment n 2 t-2*spin n*rawMoment n 1 t+(spin n)^2*rawMoment n 0 t := by
    unfold rawMoment
    simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hf : (∑ k ∈ Finset.range (n+1), (level n k-spin n)^2*Real.exp (level n k*t)) =
      Real.exp (spin n*t)*(∑ k ∈ Finset.range (n+1), (k:ℝ)^2*(Real.exp (-t))^k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [exp_level_factor]
    unfold level
    ring
  have hden := raw_zero_pos n t
  have hp : 0 < P n (Real.exp (-t)) := lt_of_lt_of_le zero_lt_one
    (P_ge_one n _ (Real.exp_pos _).le)
  have he : (∑ k ∈ Finset.range (n+1), (level n k-spin n)^2*Real.exp (level n k*t)) /
      rawMoment n 0 t =
      (∑ k ∈ Finset.range (n+1), (k:ℝ)^2*(Real.exp (-t))^k)/P n (Real.exp (-t)) := by
    rw [hf,raw_zero_factor]
    field_simp [hp.ne',Real.exp_ne_zero]
  rw [← he,hs]
  have hmean : mean n t*rawMoment n 0 t = rawMoment n 1 t := by
    unfold mean
    field_simp [hden.ne']
  have heq : (rawMoment n 2 t-2*spin n*rawMoment n 1 t+
      (spin n)^2*rawMoment n 0 t)/rawMoment n 0 t =
        variance n t+(mean n t-spin n)^2 := by
    unfold variance mean
    field_simp [hden.ne']
    <;> ring
  rw [heq]
  linarith [sq_nonneg (mean n t-spin n)]

theorem fisher_exponential_bound (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    fisher n t ≤ (n:ℝ)^3*Real.exp (-t) := by
  let r := Real.exp (-t)
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp := P_ge_one n r hr
  have hs : (∑ k ∈ Finset.range (n+1), (k:ℝ)^2*r^k) ≤ (n:ℝ)^3*r := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul,add_zero]
    have hh : (∑ k ∈ Finset.range n, ((k+1:ℕ):ℝ)^2*r^(k+1)) ≤
      ∑ _k ∈ Finset.range n, (n:ℝ)^2*r := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : ((k+1:ℕ):ℝ) ≤ n := by
        exact_mod_cast (show k+1 ≤ n from by have := Finset.mem_range.mp hk; omega)
      have hh' : ((k+1:ℕ):ℝ)^2 ≤ (n:ℝ)^2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hk') (show 0 ≤ ((k+1:ℕ):ℝ)+(n:ℝ) by positivity)]
      exact mul_le_mul hh' (pow_succ_le_self r hr hr1 k) (pow_nonneg hr _) (sq_nonneg _)
    simpa [pow_succ,mul_assoc,mul_left_comm,mul_comm] using hh
  rw [fisher_eq_variance]
  apply le_trans (variance_center_bound n t)
  change (∑ k ∈ Finset.range (n+1), (k:ℝ)^2*r^k)/P n r ≤ (n:ℝ)^3*r
  apply (div_le_iff₀ (by linarith : 0 < P n r)).2
  exact hs.trans (by nlinarith [mul_nonneg (show 0 ≤ (n:ℝ)^3*r by positivity) (sub_nonneg.mpr hp)])

def speed (n : ℕ) (t : ℝ) : ℝ := Real.sqrt (fisher n t)

theorem speed_bound (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    speed n t ≤ Real.sqrt ((n:ℝ)^3)*Real.exp (-t/2) := by
  unfold speed
  have h := Real.sqrt_le_sqrt (fisher_exponential_bound n hn t ht)
  rw [Real.sqrt_mul (by positivity : 0 ≤ (n:ℝ)^3)] at h
  have he : Real.sqrt (Real.exp (-t)) = Real.exp (-t/2) := by
    apply (Real.sqrt_eq_iff_sq_eq (Real.exp_pos _).le (Real.exp_pos _).le).2
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  simpa only [he] using h

theorem speed_continuous (n : ℕ) : Continuous (speed n) := by
  have h (j : ℕ) : Continuous (rawMoment n j) :=
    continuous_iff_continuousAt.mpr (fun t => (rawMoment_hasDerivAt n j t).continuousAt)
  have hv : Continuous (variance n) := by
    unfold variance mean
    exact ((h 2).div (h 0) (fun t => (raw_zero_pos n t).ne')).sub
      (((h 1).div (h 0) (fun t => (raw_zero_pos n t).ne')).pow 2)
  have hf : speed n = fun t => Real.sqrt (variance n t) := by
    funext t
    rw [speed,fisher_eq_variance]
  rw [hf]
  exact Real.continuous_sqrt.comp hv

/-- Length along the one-dimensional spin family, in its positive orientation. -/
def fisherLength (n : ℕ) (a b : ℝ) : ℝ := ∫ t in a..b, speed n t

theorem exponential_integral (a b : ℝ) :
    (∫ t in a..b, Real.exp (-t/2)) = 2*(Real.exp (-a/2)-Real.exp (-b/2)) := by
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => -2*Real.exp (-u/2)) (Real.exp (-t/2)) t := by
    have h := (((hasDerivAt_id t).neg.div_const 2).exp).const_mul (-2:ℝ)
    convert h using 1 <;> simp [id] <;> ring
  have hc : Continuous (fun t : ℝ => Real.exp (-t/2)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t) hc.intervalIntegrable]
  ring

theorem fisher_length_bound (n : ℕ) (hn : 0 < n) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    fisherLength n a b ≤ 2*Real.sqrt ((n:ℝ)^3)*
      (Real.exp (-a/2)-Real.exp (-b/2)) := by
  have hc : Continuous (fun t : ℝ => Real.sqrt ((n:ℝ)^3)*Real.exp (-t/2)) := by fun_prop
  have hle : (∫ t in a..b, speed n t) ≤
      ∫ t in a..b, Real.sqrt ((n:ℝ)^3)*Real.exp (-t/2) := by
    apply intervalIntegral.integral_mono_on hab (speed_continuous n).intervalIntegrable hc.intervalIntegrable
    intro t ht
    exact speed_bound n hn t (ha.trans ht.1)
  rw [intervalIntegral.integral_const_mul,exponential_integral] at hle
  unfold fisherLength
  convert hle using 1 <;> ring

/-- Completion distance to the positive saturation boundary: supremum of
    monotone arc lengths. The bound below rules out an infinite distance. -/
def saturationDistance (n : ℕ) (a : ℝ) : ℝ :=
  sSup (fisherLength n a '' Set.Ici a)

theorem saturation_distance_bound (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 ≤ a) :
    0 ≤ saturationDistance n a ∧
      saturationDistance n a ≤ 2*Real.sqrt ((n:ℝ)^3)*Real.exp (-a/2) := by
  have hB : ∀ b ∈ Set.Ici a, fisherLength n a b ≤
      2*Real.sqrt ((n:ℝ)^3)*Real.exp (-a/2) := by
    intro b hb
    have h := fisher_length_bound n hn a b ha hb
    have hp : 0 ≤ 2*Real.sqrt ((n:ℝ)^3)*Real.exp (-b/2) := by positivity
    nlinarith
  have hb : BddAbove (fisherLength n a '' Set.Ici a) := by
    refine ⟨_,?_⟩
    rintro _ ⟨b,hb,rfl⟩
    exact hB b hb
  have hzero : 0 ∈ fisherLength n a '' Set.Ici a := by
    refine ⟨a,le_rfl,?_⟩
    simp [fisherLength]
  exact ⟨le_csSup hb hzero,csSup_le ⟨0,hzero⟩ (by
    rintro _ ⟨b,hb,rfl⟩
    exact hB b hb)⟩

theorem saturation_distance_tendsto_zero (n : ℕ) (hn : 0 < n) :
    Tendsto (saturationDistance n) atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-t/2)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply tendsto_atBot.2
    intro b
    filter_upwards [eventually_ge_atTop (-2*b)] with t ht
    linarith
  have hu : Tendsto (fun t => 2*Real.sqrt ((n:ℝ)^3)*Real.exp (-t/2)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := 2*Real.sqrt ((n:ℝ)^3))).mul he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact (saturation_distance_bound n hn t ht).1
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact (saturation_distance_bound n hn t ht).2

end
end M14.EulerianSpinLaw

namespace M14.EulerianLegendre
open Filter
open scoped Topology
noncomputable section

theorem classical_cumulant_upper (x : ℝ) (hx : 0 < x) :
    cumulant x ≤ x-Real.log (2*x) := by
  have hs := sinh_pos_of_pos x hx
  have h : Real.sinh x / x ≤ Real.exp x/(2*x) := by
    rw [Real.sinh_eq]
    apply (div_le_div_iff₀ hx (by positivity : 0 < 2*x)).2
    nlinarith [mul_nonneg hx.le (Real.exp_pos (-x)).le]
  have hh := Real.log_le_log (div_pos hs hx) h
  rw [Real.log_div (Real.exp_ne_zero _) (by positivity : 2*x ≠ 0),Real.log_exp] at hh
  simpa [cumulant,profile,hx.ne'] using hh

theorem classical_conjugate_lower (m : ℝ) (hm : m ∈ Set.Ioo (-1:ℝ) 1) :
    Real.log (2/(1-m))-1 ≤ conjugate m := by
  let x : ℝ := 1/(1-m)
  have hx : 0 < x := div_pos zero_lt_one (sub_pos.mpr hm.2)
  have h := classical_cumulant_upper x hx
  have hs := cumulant_support (inverseLangevin m) x
  rw [inverseLangevin_right_on_interval m hm] at hs
  have he : m*x-x = -1 := by
    dsimp [x]
    field_simp [show 1-m ≠ 0 by linarith [hm.2]]
    <;> ring
  rw [conjugate_eq_inverse_on_interval m hm]
  have he2 : 2*x = 2/(1-m) := by dsimp [x]; ring
  rw [he2] at h
  linarith

/-- The classical endpoint supremum is unbounded, not a finite real sSup. -/
theorem classical_endpoint_unbounded :
    ¬ BddAbove (Set.range (fun x : ℝ => x-cumulant x)) := by
  rintro ⟨M,hM⟩
  let x := Real.exp (M+1)
  have hx : 0 < x := Real.exp_pos _
  have hc := classical_cumulant_upper x hx
  have hm := hM (show x-cumulant x ∈ Set.range (fun x : ℝ => x-cumulant x) from ⟨x,rfl⟩)
  have hl : Real.log x ≤ Real.log (2*x) := Real.log_le_log hx (by linarith)
  have he : Real.log x = M+1 := Real.log_exp _
  linarith

theorem classical_conjugate_diverges :
    Tendsto conjugate (𝓝[<] (1:ℝ)) atTop := by
  apply tendsto_atTop.2
  intro M
  let d : ℝ := min 1 (Real.exp (-(M+2)))
  have hd : 0 < d := lt_min zero_lt_one (Real.exp_pos _)
  have hnear : ∀ᶠ m : ℝ in 𝓝[<] (1:ℝ), 1-d < m :=
    nhdsWithin_le_nhds (eventually_gt_nhds (by linarith : 1-d < (1:ℝ)))
  filter_upwards [hnear,self_mem_nhdsWithin] with m hm hm1
  have hm1' : m < 1 := hm1
  have hd1 : d ≤ 1 := min_le_left _ _
  have hd2 : d ≤ Real.exp (-(M+2)) := min_le_right _ _
  have hgap : 0 < 1-m := by linarith
  have hmem : m ∈ Set.Ioo (-1:ℝ) 1 := ⟨by linarith,hm1'⟩
  have hl := classical_conjugate_lower m hmem
  have he : Real.exp (M+2) ≤ 2/(1-m) := by
    apply (le_div_iff₀ hgap).2
    have hp := mul_le_mul_of_nonneg_left (show 1-m ≤ Real.exp (-(M+2)) by linarith)
      (Real.exp_pos (M+2)).le
    rw [← Real.exp_add] at hp
    rw [add_neg_cancel,Real.exp_zero] at hp
    linarith
  have hlog := Real.log_le_log (Real.exp_pos (M+2)) he
  rw [Real.log_exp] at hlog
  linarith

end
end M14.EulerianLegendre

#print axioms M14.EulerianSpinLaw.raw_one_factor
#print axioms M14.EulerianSpinLaw.q_eq_mean
#print axioms M14.EulerianSpinLaw.q_hasDerivAt
#print axioms M14.EulerianSpinLaw.q_strictMono
#print axioms M14.EulerianSpinLaw.level_reflect
#print axioms M14.EulerianSpinLaw.raw_reflect_zero
#print axioms M14.EulerianSpinLaw.raw_reflect_one
#print axioms M14.EulerianSpinLaw.q_odd
#print axioms M14.EulerianSpinLaw.q_upper
#print axioms M14.EulerianSpinLaw.q_range_bound
#print axioms M14.EulerianSpinLaw.q_limit_top
#print axioms M14.EulerianSpinLaw.q_range
#print axioms M14.EulerianSpinLaw.inverse_left
#print axioms M14.EulerianSpinLaw.inverse_right
#print axioms M14.EulerianSpinLaw.inverse_strictMono
#print axioms M14.EulerianSpinLaw.pow_succ_le_self
#print axioms M14.EulerianSpinLaw.P_upper_linear
#print axioms M14.EulerianSpinLaw.A_upper_linear
#print axioms M14.EulerianSpinLaw.P_upper_uniform
#print axioms M14.EulerianSpinLaw.log_ratio_bound
#print axioms M14.EulerianSpinLaw.quantitative_t
#print axioms M14.EulerianSpinLaw.exponential_deficit_bound
#print axioms M14.EulerianSpinLaw.quantitative_inverse
#print axioms M14.EulerianSpinLaw.variance_center_bound
#print axioms M14.EulerianSpinLaw.fisher_exponential_bound
#print axioms M14.EulerianSpinLaw.speed_bound
#print axioms M14.EulerianSpinLaw.speed_continuous
#print axioms M14.EulerianSpinLaw.exponential_integral
#print axioms M14.EulerianSpinLaw.fisher_length_bound
#print axioms M14.EulerianSpinLaw.saturation_distance_bound
#print axioms M14.EulerianSpinLaw.saturation_distance_tendsto_zero
#print axioms M14.EulerianLegendre.classical_cumulant_upper
#print axioms M14.EulerianLegendre.classical_conjugate_lower
#print axioms M14.EulerianLegendre.classical_endpoint_unbounded
#print axioms M14.EulerianLegendre.classical_conjugate_diverges


end
end M14.EulerianSpinLaw
