import Mathlib

/-! Finite spin Gibbs law, saturation singularity, endpoint conjugate and
Fisher curvature. No asymptotic ansatz is assumed. -/
namespace M14.EulerianSpinLaw
open Filter Finset
open scoped BigOperators Topology
noncomputable section

def spin (n : ℕ) : ℝ := (n : ℝ)/2
def level (n k : ℕ) : ℝ := spin n - k
def P (n : ℕ) (r : ℝ) : ℝ := ∑ k ∈ Finset.range (n+1), r^k
def A (n : ℕ) (r : ℝ) : ℝ := ∑ k ∈ Finset.range n, ((k+1 : ℕ) : ℝ)*r^k
def moment (n : ℕ) (r : ℝ) : ℝ := ∑ k ∈ Finset.range (n+1), (k:ℝ)*r^k
def ratio (n : ℕ) (r : ℝ) : ℝ := A n r / P n r
def normalizedMean (n : ℕ) (r : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (n+1), level n k*r^k)/(spin n*P n r)
def q (n : ℕ) (t : ℝ) : ℝ := normalizedMean n (Real.exp (-t))

theorem spin_pos (n : ℕ) (hn : 0 < n) : 0 < spin n := by
  unfold spin
  positivity

theorem P_zero (n : ℕ) : P n 0 = 1 := by
  unfold P
  rw [Finset.sum_range_succ']
  simp

theorem A_zero (n : ℕ) (hn : 0 < n) : A n 0 = 1 := by
  cases n with
  | zero => omega
  | succ n =>
    unfold A
    rw [Finset.sum_range_succ']
    simp

theorem P_ge_one (n : ℕ) (r : ℝ) (hr : 0 ≤ r) : 1 ≤ P n r := by
  unfold P
  have h := Finset.single_le_sum (f := fun k : ℕ => r^k)
    (fun k hk => pow_nonneg hr k) (Finset.mem_range.mpr (Nat.zero_lt_succ n))
  simpa using h

theorem A_ge_one (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 ≤ r) : 1 ≤ A n r := by
  unfold A
  have h := Finset.single_le_sum
    (f := fun k : ℕ => ((k+1 : ℕ) : ℝ)*r^k)
    (fun k hk => mul_nonneg (by positivity) (pow_nonneg hr k))
    (Finset.mem_range.mpr hn)
  simpa using h

theorem moment_factor (n : ℕ) (r : ℝ) : moment n r = r*A n r := by
  unfold moment A
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_succ]
  ring

theorem mean_numerator (n : ℕ) (r : ℝ) :
    (∑ k ∈ Finset.range (n+1), level n k*r^k) =
      spin n*P n r-moment n r := by
  simp only [level,P,moment,sub_mul,Finset.sum_sub_distrib,Finset.mul_sum]

theorem normalized_deficit (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 ≤ r) :
    1-normalizedMean n r = r*A n r/(spin n*P n r) := by
  have hp : 0 < P n r := lt_of_lt_of_le zero_lt_one (P_ge_one n r hr)
  have hj := spin_pos n hn
  rw [normalizedMean,mean_numerator,moment_factor]
  field_simp [hj.ne',hp.ne']
  <;> ring

theorem scaled_deficit (n : ℕ) (hn : 0 < n) (t : ℝ) :
    spin n*(1-q n t) = Real.exp (-t)*ratio n (Real.exp (-t)) := by
  have hp : 0 < P n (Real.exp (-t)) :=
    lt_of_lt_of_le zero_lt_one (P_ge_one n _ (Real.exp_pos _).le)
  have hj := spin_pos n hn
  rw [q,normalized_deficit n hn _ (Real.exp_pos _).le]
  unfold ratio
  field_simp [hj.ne',hp.ne']
  <;> ring

theorem ratio_positive (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 ≤ r) :
    0 < ratio n r := by
  exact div_pos (lt_of_lt_of_le zero_lt_one (A_ge_one n hn r hr))
    (lt_of_lt_of_le zero_lt_one (P_ge_one n r hr))

theorem P_cont (n : ℕ) : Continuous (P n) := by
  unfold P
  fun_prop

theorem A_cont (n : ℕ) : Continuous (A n) := by
  unfold A
  fun_prop

theorem ratio_limit (n : ℕ) (hn : 0 < n) :
    Tendsto (ratio n) (𝓝 0) (𝓝 1) := by
  have hp : P n 0 ≠ 0 := by rw [P_zero]; norm_num
  have h := ((A_cont n).continuousAt (x := (0:ℝ))).div
    ((P_cont n).continuousAt (x := (0:ℝ))) hp
  have hf : ratio n = A n / P n := rfl
  rw [hf]
  simpa [A_zero n hn,P_zero] using h.tendsto

theorem exp_neg_limit : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot

theorem scaled_deficit_limit (n : ℕ) (hn : 0 < n) :
    Tendsto (fun t : ℝ => Real.exp t*(spin n*(1-q n t))) atTop (𝓝 1) := by
  have h : (fun t : ℝ => Real.exp t*(spin n*(1-q n t))) =
      fun t => ratio n (Real.exp (-t)) := by
    funext t
    rw [scaled_deficit n hn]
    rw [← mul_assoc, ← Real.exp_add]
    simp
  rw [h]
  exact (ratio_limit n hn).comp exp_neg_limit

theorem log_saturation_identity (n : ℕ) (hn : 0 < n) (t : ℝ) :
    t+Real.log (spin n*(1-q n t)) = Real.log (ratio n (Real.exp (-t))) := by
  rw [scaled_deficit n hn, Real.log_mul (Real.exp_ne_zero _)
    (ratio_positive n hn _ (Real.exp_pos _).le).ne',Real.log_exp]
  ring

theorem log_saturation_limit (n : ℕ) (hn : 0 < n) :
    Tendsto (fun t => t+Real.log (spin n*(1-q n t))) atTop (𝓝 0) := by
  have h := (Real.continuousAt_log (show (1:ℝ) ≠ 0 by norm_num)).tendsto.comp
    ((ratio_limit n hn).comp exp_neg_limit)
  simpa only [Function.comp_def,Real.log_one,log_saturation_identity n hn] using h

/-- Log of the uniform-reference finite spin partition function. -/
def logPartition (n : ℕ) (t : ℝ) : ℝ :=
  spin n*t+Real.log (P n (Real.exp (-t)))-Real.log ((n:ℝ)+1)

theorem exp_level_factor (n k : ℕ) (t : ℝ) :
    Real.exp (level n k*t) = Real.exp (spin n*t)*(Real.exp (-t))^k := by
  have hp (k : ℕ) : Real.exp (-(k:ℝ)*t) = (Real.exp (-t))^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ,show -((k:ℝ)+1)*t = -(k:ℝ)*t + (-t) by ring,
        Real.exp_add,ih,pow_succ]
  rw [level,show (spin n-(k:ℝ))*t = spin n*t+(-(k:ℝ)*t) by ring,
    Real.exp_add,hp]

def rawMoment (n j : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), (level n k)^j * Real.exp (level n k*t)

theorem raw_zero_factor (n : ℕ) (t : ℝ) :
    rawMoment n 0 t = Real.exp (spin n*t)*P n (Real.exp (-t)) := by
  simp only [rawMoment,pow_zero,one_mul,exp_level_factor,P,Finset.mul_sum]

theorem raw_zero_pos (n : ℕ) (t : ℝ) : 0 < rawMoment n 0 t := by
  rw [raw_zero_factor]
  exact mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one
    (P_ge_one n _ (Real.exp_pos _).le))

theorem actual_partition (n : ℕ) (t : ℝ) :
    logPartition n t = Real.log (rawMoment n 0 t / ((n:ℝ)+1)) := by
  rw [raw_zero_factor,Real.log_div (mul_ne_zero (Real.exp_ne_zero _)
    (lt_of_lt_of_le zero_lt_one (P_ge_one n _ (Real.exp_pos _).le)).ne')
    (by positivity : (n:ℝ)+1 ≠ 0),
    Real.log_mul (Real.exp_ne_zero _)
    (lt_of_lt_of_le zero_lt_one (P_ge_one n _ (Real.exp_pos _).le)).ne',
    Real.log_exp]
  rfl

theorem endpoint_bound (n : ℕ) (t : ℝ) :
    spin n*t-logPartition n t ≤ Real.log ((n:ℝ)+1) := by
  have h := Real.log_nonneg (P_ge_one n _ (Real.exp_pos (-t)).le)
  unfold logPartition
  linarith

theorem endpoint_limit (n : ℕ) :
    Tendsto (fun t => spin n*t-logPartition n t) atTop
      (𝓝 (Real.log ((n:ℝ)+1))) := by
  have hP : Tendsto (fun t => P n (Real.exp (-t))) atTop (𝓝 1) := by
    simpa only [P_zero,Function.comp_def] using
      ((P_cont n).continuousAt (x := (0:ℝ))).tendsto.comp exp_neg_limit
  have hlog : Tendsto (fun t => Real.log (P n (Real.exp (-t)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.log_one] using
      (Real.continuousAt_log (show (1:ℝ) ≠ 0 by norm_num)).tendsto.comp hP
  have heq : (fun t => spin n*t-logPartition n t) =
      fun t => Real.log ((n:ℝ)+1)-Real.log (P n (Real.exp (-t))) := by
    funext t
    unfold logPartition
    ring
  rw [heq]
  simpa only [sub_zero] using tendsto_const_nhds.sub hlog

theorem endpoint_conjugate (n : ℕ) :
    sSup (Set.range (fun t => spin n*t-logPartition n t)) =
      Real.log ((n:ℝ)+1) := by
  have hb : BddAbove (Set.range (fun t => spin n*t-logPartition n t)) := by
    refine ⟨Real.log ((n:ℝ)+1),?_⟩
    rintro _ ⟨t,rfl⟩
    exact endpoint_bound n t
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_,⟨0,rfl⟩⟩
    · rintro _ ⟨t,rfl⟩
      exact endpoint_bound n t
  · apply le_of_tendsto (endpoint_limit n)
    exact Filter.Eventually.of_forall (fun t => le_csSup hb ⟨t,rfl⟩)

/-- Differentiation of the actual finite Gibbs moments. -/
theorem rawMoment_hasDerivAt (n j : ℕ) (t : ℝ) :
    HasDerivAt (rawMoment n j) (rawMoment n (j+1) t) t := by
  unfold rawMoment
  have h (s : Finset ℕ) :
      HasDerivAt (fun u : ℝ => ∑ k ∈ s, (level n k)^j*Real.exp (level n k*u))
        (∑ k ∈ s, (level n k)^(j+1)*Real.exp (level n k*t)) t := by
    induction s using Finset.induction_on with
    | empty => simpa using (hasDerivAt_const t (0:ℝ))
    | @insert k s hk ih =>
      have hl : HasDerivAt (fun u : ℝ => level n k*u) (level n k) t := by
        simpa only [mul_one,id_eq] using (hasDerivAt_id t).const_mul (level n k)
      have hh := (hl.exp.const_mul ((level n k)^j)).add ih
      convert hh using 1
      · funext u
        simp only [Finset.sum_insert hk,Pi.add_apply]
      · rw [Finset.sum_insert hk,pow_succ]
        ring
  exact h _

def mean (n : ℕ) (t : ℝ) : ℝ := rawMoment n 1 t / rawMoment n 0 t
def variance (n : ℕ) (t : ℝ) : ℝ :=
  rawMoment n 2 t/rawMoment n 0 t-(mean n t)^2

theorem logPartition_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (logPartition n) (mean n t) t := by
  have hfun : logPartition n = fun u =>
      Real.log (rawMoment n 0 u)-Real.log ((n:ℝ)+1) := by
    funext u
    rw [actual_partition,Real.log_div (raw_zero_pos n u).ne' (by positivity : (n:ℝ)+1 ≠ 0)]
  rw [hfun]
  exact ((rawMoment_hasDerivAt n 0 t).log (raw_zero_pos n t).ne').sub_const _

theorem mean_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (mean n) (variance n t) t := by
  have hne := (raw_zero_pos n t).ne'
  have h := (rawMoment_hasDerivAt n 1 t).div (rawMoment_hasDerivAt n 0 t) hne
  have hf : mean n = rawMoment n 1 / rawMoment n 0 := rfl
  rw [hf]
  convert h using 1
  unfold variance mean
  norm_num
  field_simp [hne]
  <;> ring

theorem variance_weighted (n : ℕ) (t : ℝ) :
    variance n t =
      (∑ k ∈ Finset.range (n+1), (level n k-mean n t)^2*Real.exp (level n k*t))
        /rawMoment n 0 t := by
  have hs : (∑ k ∈ Finset.range (n+1),
        (level n k-mean n t)^2*Real.exp (level n k*t)) =
        rawMoment n 2 t-2*mean n t*rawMoment n 1 t+(mean n t)^2*rawMoment n 0 t := by
    unfold rawMoment
    simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hs]
  unfold variance mean
  field_simp [(raw_zero_pos n t).ne']
  <;> ring

theorem variance_positive (n : ℕ) (hn : 0 < n) (t : ℝ) :
    0 < variance n t := by
  rw [variance_weighted]
  apply div_pos _ (raw_zero_pos n t)
  have hpos (k : ℕ) (hk : k ∈ Finset.range (n+1)) (h : level n k ≠ mean n t) :
      0 < ∑ i ∈ Finset.range (n+1), (level n i-mean n t)^2*Real.exp (level n i*t) := by
    have hle := Finset.single_le_sum
      (f := fun i : ℕ => (level n i-mean n t)^2*Real.exp (level n i*t))
      (fun i hi => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hk
    exact lt_of_lt_of_le (mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr h)) (Real.exp_pos _)) hle
  by_cases h : level n 0 = mean n t
  · apply hpos 1 (Finset.mem_range.mpr (by omega))
    intro hh
    unfold level at h hh
    norm_num at h hh
    linarith
  · exact hpos 0 (Finset.mem_range.mpr (Nat.zero_lt_succ n)) h

def logProbability (n k : ℕ) (t : ℝ) : ℝ :=
  Real.log (Real.exp (level n k*t)/rawMoment n 0 t)

theorem logProbability_hasDerivAt (n k : ℕ) (t : ℝ) :
    HasDerivAt (logProbability n k) (level n k-mean n t) t := by
  have hf : logProbability n k = fun u => level n k*u-Real.log (rawMoment n 0 u) := by
    funext u
    rw [logProbability,Real.log_div (Real.exp_ne_zero _) (raw_zero_pos n u).ne',Real.log_exp]
  rw [hf]
  have hl : HasDerivAt (fun u : ℝ => level n k*u) (level n k) t := by
    simpa only [mul_one,id_eq] using (hasDerivAt_id t).const_mul (level n k)
  exact hl.sub ((rawMoment_hasDerivAt n 0 t).log (raw_zero_pos n t).ne')

def fisher (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), (deriv (logProbability n k) t)^2 *
    (Real.exp (level n k*t)/rawMoment n 0 t)

theorem fisher_eq_variance (n : ℕ) (t : ℝ) : fisher n t = variance n t := by
  unfold fisher
  simp only [(logProbability_hasDerivAt n _ t).deriv]
  rw [variance_weighted,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem fisher_positive (n : ℕ) (hn : 0 < n) (t : ℝ) : 0 < fisher n t := by
  rw [fisher_eq_variance]
  exact variance_positive n hn t

#print axioms spin_pos
#print axioms P_zero
#print axioms A_zero
#print axioms P_ge_one
#print axioms A_ge_one
#print axioms moment_factor
#print axioms mean_numerator
#print axioms normalized_deficit
#print axioms scaled_deficit
#print axioms ratio_positive
#print axioms P_cont
#print axioms A_cont
#print axioms ratio_limit
#print axioms exp_neg_limit
#print axioms scaled_deficit_limit
#print axioms log_saturation_identity
#print axioms log_saturation_limit
#print axioms exp_level_factor
#print axioms raw_zero_factor
#print axioms raw_zero_pos
#print axioms actual_partition
#print axioms endpoint_bound
#print axioms endpoint_limit
#print axioms endpoint_conjugate
#print axioms rawMoment_hasDerivAt
#print axioms logPartition_hasDerivAt
#print axioms mean_hasDerivAt
#print axioms variance_weighted
#print axioms variance_positive
#print axioms logProbability_hasDerivAt
#print axioms fisher_eq_variance
#print axioms fisher_positive
end
end M14.EulerianSpinLaw
