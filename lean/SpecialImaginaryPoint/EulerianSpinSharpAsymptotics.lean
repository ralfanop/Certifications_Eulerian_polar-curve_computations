import SpecialImaginaryPoint.EulerianSpinThreshold
import SpecialImaginaryPoint.EulerianSpinCompletion

/-! Exact threshold correction and leading Fisher asymptotics.
The parameter n is twice the spin, with n > 0. -/
namespace M14.EulerianSpin
open M14.EulerianLegendre
noncomputable section

theorem langevin_exp_form (x : ℝ) (hx : 0 < x) :
    langevin x = 1 - 1/x + 2/(Real.exp (2*x)-1) := by
  have hs := sinh_pos_of_pos x hx
  have hd : 0 < Real.exp (2*x)-1 := by
    have h := Real.exp_lt_exp.mpr (show (0:ℝ) < 2*x by linarith)
    rw [Real.exp_zero] at h
    linarith
  have h1 : (Real.exp (2*x)-1)*Real.exp (-x) = Real.exp x-Real.exp (-x) := by
    rw [sub_mul,one_mul,← Real.exp_add,show 2*x + -x = x by ring]
  have h2 : Real.cosh x-Real.sinh x = Real.exp (-x) := by
    rw [Real.cosh_eq,Real.sinh_eq]
    ring
  have h3 : 2*Real.sinh x = Real.exp x-Real.exp (-x) := by
    rw [Real.sinh_eq]
    ring
  have h4 : (Real.exp (2*x)-1)*(Real.cosh x-Real.sinh x) = 2*Real.sinh x := by
    rw [h2,h3]
    exact h1
  have hc : Real.cosh x/Real.sinh x = 1+2/(Real.exp (2*x)-1) := by
    field_simp [hs.ne',hd.ne']
    nlinarith only [h4]
  rw [langevin,if_neg hx.ne',langevinRaw,hc]
  ring

def reference (eta : ℝ) : ℝ := 2/(1-1/eta)

theorem reference_pos (eta : ℝ) (he : 1 < eta) : 0 < reference eta := by
  have hp : 0 < eta := by linarith
  have h : 1/eta < 1 := (div_lt_iff₀ hp).2 (by linarith)
  exact div_pos (by norm_num) (sub_pos.mpr h)

theorem threshold_correction (eta : ℝ) (he : 1 < eta) :
    reference eta-critical eta =
      reference eta*critical eta/(Real.exp (critical eta)-1) := by
  let R := reference eta
  let H := critical eta
  have hR : 0 < R := reference_pos eta he
  have hH : 0 < H := critical_pos eta he
  have hgap : 0 < 1-1/eta := by
    have h : 1/eta < 1 := (div_lt_iff₀ (by linarith : 0 < eta)).2 (by linarith)
    linarith
  have hR' : 1/eta = 1-2/R := by
    dsimp [R,reference]
    have he0 : eta ≠ 0 := by linarith
    field_simp [hgap.ne',he0]
    <;> ring
  have hd : 0 < Real.exp H-1 := by
    have h := Real.exp_lt_exp.mpr hH
    rw [Real.exp_zero] at h
    linarith
  have hL : langevin (H/2) = 1/eta := critical_exact eta he
  rw [langevin_exp_form (H/2) (by linarith),show 2*(H/2)=H by ring,hR'] at hL
  have h1 : 2/H-2/R = 2/(Real.exp H-1) := by
    rw [show 1/(H/2)=2/H by ring] at hL
    linarith
  change R-H = R*H/(Real.exp H-1)
  apply (eq_div_iff hd.ne').2
  field_simp [hH.ne',hR.ne',hd.ne'] at h1
  nlinarith only [h1]

theorem threshold_lt_reference (eta : ℝ) (he : 1 < eta) :
    critical eta < reference eta := by
  have h := threshold_correction eta he
  have hp := critical_pos eta he
  have hd : 0 < Real.exp (critical eta)-1 := by
    have h' := Real.exp_lt_exp.mpr hp
    rw [Real.exp_zero] at h'
    linarith
  have hpos := div_pos (mul_pos (reference_pos eta he) hp) hd
  linarith

def spinReference (j : ℝ) : ℝ := 2*(j+1+Real.sqrt (j*(j+1)))

theorem reference_spin_eq (j : ℝ) (hj : 0 < j) :
    reference (spinRatio j) = spinReference j := by
  have hp : 0 < j+1 := by positivity
  have hm : spinRatio j*Real.sqrt (j/(j+1)) = 1 := by
    unfold spinRatio
    rw [← Real.sqrt_mul (by positivity : 0 ≤ (j+1)/j)]
    rw [show ((j+1)/j)*(j/(j+1))=1 by field_simp [hj.ne',hp.ne']]
    norm_num
  have hne : spinRatio j ≠ 0 := by linarith [spinRatio_gt_one j hj]
  have hi : 1/spinRatio j = Real.sqrt (j/(j+1)) := by
    apply (div_eq_iff hne).2
    linarith [mul_comm (spinRatio j) (Real.sqrt (j/(j+1)))]
  unfold reference spinReference
  rw [hi,spin_reference_exact j hj]

theorem spin_reference_gap (j : ℝ) (hj : 0 < j) :
    (4*j+3-spinReference j)*(spinReference j-1) = 1 := by
  have h := Real.sq_sqrt (show 0 ≤ j*(j+1) by positivity)
  unfold spinReference
  nlinarith only [h]

theorem spin_threshold_exact_decomposition (j : ℝ) (hj : 0 < j) :
    spinCritical j = 4*j+3-1/(spinReference j-1)-
      spinReference j*spinCritical j/(Real.exp (spinCritical j)-1) := by
  have hp : 1 < spinReference j := by
    unfold spinReference
    linarith [Real.sqrt_nonneg (j*(j+1))]
  have hg := spin_reference_gap j hj
  have he : 4*j+3-spinReference j = 1/(spinReference j-1) :=
    (eq_div_iff (sub_ne_zero.mpr (Ne.symm hp.ne))).2 hg
  have hc := threshold_correction (spinRatio j) (spinRatio_gt_one j hj)
  rw [reference_spin_eq j hj] at hc
  change spinReference j-spinCritical j = spinReference j*spinCritical j/(Real.exp (spinCritical j)-1) at hc
  linarith

end
end M14.EulerianSpin

namespace M14.EulerianSpinLaw
open Filter Finset
open scoped BigOperators Topology
noncomputable section

def C (n : ℕ) (r : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, ((k+1:ℕ):ℝ)^2*r^k

theorem C_zero (n : ℕ) (hn : 0 < n) : C n 0 = 1 := by
  cases n with
  | zero => omega
  | succ n =>
    unfold C
    rw [Finset.sum_range_succ']
    simp

theorem second_moment_factor (n : ℕ) (r : ℝ) :
    (∑ k ∈ Finset.range (n+1), (k:ℝ)^2*r^k) = r*C n r := by
  unfold C
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul,add_zero,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_succ]
  ring

theorem variance_center_identity (n : ℕ) (t : ℝ) :
    variance n t+(mean n t-spin n)^2 =
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
  have hp : 0 < P n (Real.exp (-t)) := lt_of_lt_of_le zero_lt_one
    (P_ge_one n _ (Real.exp_pos _).le)
  have he : (∑ k ∈ Finset.range (n+1), (level n k-spin n)^2*Real.exp (level n k*t)) /
      rawMoment n 0 t =
      (∑ k ∈ Finset.range (n+1), (k:ℝ)^2*(Real.exp (-t))^k)/P n (Real.exp (-t)) := by
    rw [hf,raw_zero_factor]
    field_simp [hp.ne',Real.exp_ne_zero]
  rw [← he,hs]
  unfold variance mean
  field_simp [(raw_zero_pos n t).ne']
  <;> ring

def normalizedVariance (n : ℕ) (r : ℝ) : ℝ :=
  C n r/P n r-r*(ratio n r)^2

theorem fisher_factor (n : ℕ) (hn : 0 < n) (t : ℝ) :
    fisher n t = Real.exp (-t)*normalizedVariance n (Real.exp (-t)) := by
  let r := Real.exp (-t)
  have hm : mean n t-spin n = -(r*ratio n r) := by
    have h := scaled_deficit n hn t
    rw [q_eq_mean n hn] at h
    have hq : spin n*(1-mean n t/spin n) = spin n-mean n t := by
      field_simp [(spin_pos n hn).ne']
      <;> ring
    rw [hq] at h
    change spin n-mean n t = r*ratio n r at h
    linarith
  have h := variance_center_identity n t
  rw [hm,second_moment_factor] at h
  rw [fisher_eq_variance,normalizedVariance]
  change variance n t = r*(C n r/P n r-r*(ratio n r)^2)
  change variance n t+(-(r*ratio n r))^2 = r*C n r/P n r at h
  rw [mul_div_assoc] at h
  linear_combination h

theorem normalizedVariance_limit (n : ℕ) (hn : 0 < n) :
    Tendsto (normalizedVariance n) (𝓝 0) (𝓝 1) := by
  have hc : Continuous (C n) := by
    unfold C
    fun_prop
  have hp : P n 0 ≠ 0 := by rw [P_zero]; norm_num
  have hd := (hc.continuousAt (x := (0:ℝ))).div
    ((P_cont n).continuousAt (x := (0:ℝ))) hp
  have h1 : Tendsto (fun r => C n r/P n r) (𝓝 0) (𝓝 1) := by
    have he : (C n / P n) = (fun r => C n r / P n r) := by
      funext r
      rfl
    have ht := hd.tendsto
    rw [he] at ht
    change Tendsto (fun r => C n r / P n r) (𝓝 0) (𝓝 (C n 0 / P n 0)) at ht
    rw [C_zero n hn, P_zero, one_div_one] at ht
    exact ht
  have h2 : Tendsto (fun r : ℝ => r*(ratio n r)^2) (𝓝 0) (𝓝 0) := by
    simpa using (show Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0) from tendsto_id).mul ((ratio_limit n hn).pow 2)
  have ht := h1.sub h2
  change Tendsto (fun r => C n r / P n r - r * (ratio n r)^2) (𝓝 0) (𝓝 ((1:ℝ)-0)) at ht
  rw [sub_zero] at ht
  exact ht

theorem fisher_scaled_limit (n : ℕ) (hn : 0 < n) :
    Tendsto (fun t => Real.exp t*fisher n t) atTop (𝓝 1) := by
  have hf : (fun t => Real.exp t*fisher n t) =
      fun t => normalizedVariance n (Real.exp (-t)) := by
    funext t
    rw [fisher_factor n hn,← mul_assoc,← Real.exp_add]
    simp
  rw [hf]
  exact (normalizedVariance_limit n hn).comp exp_neg_limit

theorem speed_scaled_limit (n : ℕ) (hn : 0 < n) :
    Tendsto (fun t => Real.exp (t/2)*speed n t) atTop (𝓝 1) := by
  have hf : (fun t => Real.exp (t/2)*speed n t) =
      fun t => Real.sqrt (Real.exp t*fisher n t) := by
    funext t
    have he : Real.sqrt (Real.exp t) = Real.exp (t/2) := by
      have hs : (Real.exp (t/2))^2 = Real.exp t := by
        rw [pow_two,← Real.exp_add]
        congr 1
        ring
      rw [← hs,Real.sqrt_sq_eq_abs,abs_of_pos (Real.exp_pos _)]
    rw [speed,Real.sqrt_mul (Real.exp_pos t).le,he]
  rw [hf]
  simpa only [Function.comp_def,Real.sqrt_one] using
    (Real.continuous_sqrt.continuousAt (x := (1:ℝ))).tendsto.comp (fisher_scaled_limit n hn)

/-- Comparison of the actual intrinsic tail length with scaled speed bounds. -/
theorem saturation_scaled_bounds (n : ℕ) (hn : 0 < n) (a c d : ℝ)
    (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hlo : ∀ s ≥ a, c ≤ Real.exp (s/2)*speed n s)
    (hhi : ∀ s ≥ a, Real.exp (s/2)*speed n s ≤ d) :
    2*c ≤ Real.exp (a/2)*saturationDistance n a ∧
      Real.exp (a/2)*saturationDistance n a ≤ 2*d := by
  have hex (s : ℝ) : Real.exp (s/2)*Real.exp (-s/2)=1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hpoint (s : ℝ) (hs : a ≤ s) :
      c*Real.exp (-s/2) ≤ speed n s ∧
      speed n s ≤ d*Real.exp (-s/2) := by
    have he : (Real.exp (s/2)*speed n s)*Real.exp (-s/2)=speed n s := by
      calc
        _ = (Real.exp (s/2)*Real.exp (-s/2))*speed n s := by ring
        _ = _ := by rw [hex,one_mul]
    constructor
    · have h := mul_le_mul_of_nonneg_right (hlo s hs) (Real.exp_pos (-s/2)).le
      rwa [he] at h
    · have h := mul_le_mul_of_nonneg_right (hhi s hs) (Real.exp_pos (-s/2)).le
      rwa [he] at h
  have hlen (b : ℝ) (hb : a ≤ b) :
      2*c*(Real.exp (-a/2)-Real.exp (-b/2)) ≤ fisherLength n a b ∧
      fisherLength n a b ≤ 2*d*(Real.exp (-a/2)-Real.exp (-b/2)) := by
    have hc : Continuous (fun s : ℝ => c*Real.exp (-s/2)) := by fun_prop
    have hd' : Continuous (fun s : ℝ => d*Real.exp (-s/2)) := by fun_prop
    have h1 := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hb
      (hc.intervalIntegrable a b) ((speed_continuous n).intervalIntegrable a b)
      (fun s hs => (hpoint s hs.1).1)
    have h2 := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hb
      ((speed_continuous n).intervalIntegrable a b) (hd'.intervalIntegrable a b)
      (fun s hs => (hpoint s hs.1).2)
    rw [intervalIntegral.integral_const_mul,exponential_integral] at h1 h2
    unfold fisherLength
    constructor
    · convert h1 using 1 <;> ring
    · convert h2 using 1 <;> ring
  have hupper (b : ℝ) (hb : a ≤ b) :
      fisherLength n a b ≤ 2*d*Real.exp (-a/2) := by
    have h := (hlen b hb).2
    nlinarith [mul_nonneg hd (Real.exp_pos (-b/2)).le]
  have hB : BddAbove (fisherLength n a '' Set.Ici a) := by
    refine ⟨2*d*Real.exp (-a/2),?_⟩
    rintro _ ⟨b,hb,rfl⟩
    exact hupper b hb
  have hne : (fisherLength n a '' Set.Ici a).Nonempty :=
    ⟨fisherLength n a a,⟨a,Set.mem_Ici.mpr (le_refl a),rfl⟩⟩
  have hu : saturationDistance n a ≤ 2*d*Real.exp (-a/2) := by
    unfold saturationDistance
    apply csSup_le hne
    rintro _ ⟨b,hb,rfl⟩
    exact hupper b hb
  have he : Tendsto (fun b : ℝ => Real.exp (-b/2)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply tendsto_atBot.2
    intro b
    filter_upwards [eventually_ge_atTop (-2*b)] with t ht
    linarith
  have hlim : Tendsto (fun b : ℝ => 2*c*(Real.exp (-a/2)-Real.exp (-b/2)))
      atTop (𝓝 (2*c*Real.exp (-a/2))) := by
    simpa using (tendsto_const_nhds (x := 2*c)).mul
      ((tendsto_const_nhds (x := Real.exp (-a/2))).sub he)
  have hl : 2*c*Real.exp (-a/2) ≤ saturationDistance n a := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop a] with b hb
    exact (hlen b hb).1.trans (le_csSup hB ⟨b,Set.mem_Ici.mpr hb,rfl⟩)
  constructor
  · have h := mul_le_mul_of_nonneg_left hl (Real.exp_pos (a/2)).le
    calc
      2*c = 2*c*(Real.exp (a/2)*Real.exp (-a/2)) := by rw [hex,mul_one]
      _ = Real.exp (a/2)*(2*c*Real.exp (-a/2)) := by ring
      _ ≤ _ := h
  · have h := mul_le_mul_of_nonneg_left hu (Real.exp_pos (a/2)).le
    calc
      _ ≤ Real.exp (a/2)*(2*d*Real.exp (-a/2)) := h
      _ = 2*d*(Real.exp (a/2)*Real.exp (-a/2)) := by ring
      _ = _ := by rw [hex,mul_one]

theorem saturation_distance_scaled_limit (n : ℕ) (hn : 0 < n) :
    Tendsto (fun a => Real.exp (a/2)*saturationDistance n a) atTop (𝓝 2) := by
  apply tendsto_order.2
  constructor
  · intro l hl
    let c : ℝ := (l+2)/4
    have hc : c < 1 := by dsimp [c]; linarith
    obtain ⟨A,hA⟩ := eventually_atTop.1 ((tendsto_order.1 (speed_scaled_limit n hn)).1 c hc)
    obtain ⟨B,hB⟩ := eventually_atTop.1 ((tendsto_order.1 (speed_scaled_limit n hn)).2 2 (by norm_num))
    filter_upwards [eventually_ge_atTop (max (max A B) 0)] with a ha
    have ha0 : 0 ≤ a := (le_max_right _ _).trans ha
    have haA : A ≤ a := (le_max_left A B).trans ((le_max_left (max A B) 0).trans ha)
    have haB : B ≤ a := (le_max_right A B).trans ((le_max_left (max A B) 0).trans ha)
    have hh := (saturation_scaled_bounds n hn a c 2 ha0 (by norm_num)
      (fun s hs => (hA s (haA.trans hs)).le)
      (fun s hs => (hB s (haB.trans hs)).le)).1
    dsimp [c] at hh
    linarith
  · intro u hu
    let d : ℝ := (u+2)/4
    have hd : 1 < d := by dsimp [d]; linarith
    obtain ⟨A,hA⟩ := eventually_atTop.1 ((tendsto_order.1 (speed_scaled_limit n hn)).2 d hd)
    filter_upwards [eventually_ge_atTop (max A 0)] with a ha
    have ha0 : 0 ≤ a := (le_max_right A 0).trans ha
    have hhi (s : ℝ) (hs : a ≤ s) : Real.exp (s/2)*speed n s ≤ d :=
      (hA s ((le_max_left A 0).trans (ha.trans hs))).le
    have hlo (s : ℝ) (_ : a ≤ s) : 0 ≤ Real.exp (s/2)*speed n s := by
      unfold speed
      positivity
    have hh := (saturation_scaled_bounds n hn a 0 d ha0 (by linarith) hlo hhi).2
    dsimp [d] at hh
    linarith
end
end M14.EulerianSpinLaw

namespace M14.Quartic
noncomputable section
def quartic (v z l : ℝ) : ℝ := v^4/40+6*l*v^2+z^2
theorem completed_square (v z l : ℝ) :
    quartic v z l = (v^2+120*l)^2/40+z^2-360*l^2 := by
  unfold quartic
  ring
theorem perfect_square_locus (z l : ℝ) :
    z^2 = 360*l^2 ↔ z = 6*Real.sqrt 10*l ∨ z = -(6*Real.sqrt 10*l) := by
  have h : (6*Real.sqrt 10*l)^2 = 360*l^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 10)]
    ring
  rw [← h]
  constructor
  · intro he
    have hm : (z-6*Real.sqrt 10*l)*(z+6*Real.sqrt 10*l)=0 := by nlinarith only [he]
    rcases mul_eq_zero.mp hm with h1 | h2
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h1|h2)
    · rw [h1]
    · rw [h2]
      ring
theorem perfect_square (v z l : ℝ) (h : z^2 = 360*l^2) :
    quartic v z l = ((v^2+120*l)/(2*Real.sqrt 10))^2 := by
  rw [completed_square,h]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 10)
  rw [div_pow,mul_pow,hs]
  ring
theorem gerono_zero_locus (v z a : ℝ) :
    quartic v z (-a) = 0 ↔ 40*z^2 = v^2*(240*a-v^2) := by
  unfold quartic
  constructor <;> intro h <;> nlinarith only [h]

theorem double_well_minimum (v z a : ℝ) :
    -360*a^2 ≤ quartic v z (-a) ∧
      (quartic v z (-a) = -360*a^2 ↔ v^2 = 120*a ∧ z=0) := by
  rw [completed_square]
  have h := sq_nonneg (v^2+120*(-a))
  have hz := sq_nonneg z
  constructor
  · nlinarith only [h,hz]
  · constructor
    · intro he
      have h1 : (v^2+120*(-a))^2=0 := by nlinarith only [he,h,hz]
      have h2 : z^2=0 := by nlinarith only [he,h,hz]
      have h3 : v^2+120*(-a)=0 := by simpa using h1
      have h4 : z=0 := by simpa using h2
      exact ⟨by linarith,h4⟩
    · rintro ⟨hv,hz'⟩
      rw [hz',show v^2+120*(-a)=0 by linarith]
      ring

theorem selfdual_energy (a w E : ℝ) (ha : 0 < a)
    (hw : 0 ≤ w) (hE : w^2 = 40*(E+360*a^2)) :
    2*w/(120*a+w) = 1/2 ↔ E = -320*a^2 := by
  have hp : 0 < 120*a+w := by linarith
  constructor
  · intro h
    have h' := (div_eq_iff hp.ne').mp h
    have hw' : w=40*a := by linarith
    rw [hw'] at hE
    nlinarith only [hE]
  · intro h
    rw [h] at hE
    have hh : w^2=(40*a)^2 := by nlinarith only [hE]
    have hw' : w=40*a := by
      have hfac : (w-40*a)*(w+40*a)=0 := by nlinarith only [hh]
      rcases mul_eq_zero.mp hfac with h1 | h2
      · linarith
      · linarith
    apply (div_eq_iff hp.ne').2
    linarith
end
end M14.Quartic

#print axioms M14.EulerianSpin.langevin_exp_form
#print axioms M14.EulerianSpin.reference_pos
#print axioms M14.EulerianSpin.threshold_correction
#print axioms M14.EulerianSpin.threshold_lt_reference
#print axioms M14.EulerianSpin.reference_spin_eq
#print axioms M14.EulerianSpin.spin_reference_gap
#print axioms M14.EulerianSpin.spin_threshold_exact_decomposition
#print axioms M14.EulerianSpinLaw.C_zero
#print axioms M14.EulerianSpinLaw.second_moment_factor
#print axioms M14.EulerianSpinLaw.variance_center_identity
#print axioms M14.EulerianSpinLaw.fisher_factor
#print axioms M14.EulerianSpinLaw.normalizedVariance_limit
#print axioms M14.EulerianSpinLaw.fisher_scaled_limit
#print axioms M14.EulerianSpinLaw.speed_scaled_limit
#print axioms M14.Quartic.completed_square
#print axioms M14.Quartic.perfect_square_locus
#print axioms M14.Quartic.perfect_square

#print axioms M14.EulerianSpinLaw.saturation_scaled_bounds
#print axioms M14.EulerianSpinLaw.saturation_distance_scaled_limit
#print axioms M14.Quartic.gerono_zero_locus
#print axioms M14.Quartic.double_well_minimum
#print axioms M14.Quartic.selfdual_energy
