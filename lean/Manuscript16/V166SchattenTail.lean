import Mathlib

open Filter Finset
open scoped Topology BigOperators

namespace Manuscript16.V166Tail

noncomputable def H (p N : ℕ) : ℝ :=
  ∑' n : ℕ, 1 / ((n : ℝ) + (N : ℝ) + 1)^p

theorem h_summable (p N : ℕ) (hp : 1 < p) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + (N : ℝ) + 1)^p) := by
  have hs := Real.summable_one_div_nat_pow.mpr hp
  have ht := (summable_nat_add_iff (N+1)).2 hs
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using ht

theorem H_nonneg (p N : ℕ) : 0 ≤ H p N := by
  unfold H
  exact tsum_nonneg (fun n => by positivity)

theorem delta_hasSum (a : ℝ) (ha : 0 < a) :
    HasSum (fun n : ℕ => 1/(a+(n:ℝ)) - 1/(a+(n:ℝ)+1)) (1/a) := by
  have hn (n : ℕ) : 0 ≤ 1/(a+(n:ℝ)) - 1/(a+(n:ℝ)+1) := by
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  refine (hasSum_iff_tendsto_nat_of_nonneg hn _).2 ?_
  have ht : Tendsto (fun n : ℕ => a+(n:ℝ)) atTop atTop :=
    tendsto_atTop_mono (f := fun n : ℕ => (n:ℝ)) (fun n => by linarith) tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun n : ℕ => 1/(a+(n:ℝ))) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp ht
  have hl : Tendsto (fun n : ℕ => 1/a-1/(a+(n:ℝ))) atTop (𝓝 (1/a)) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 1/a) atTop (𝓝 (1/a))).sub hz)
  convert hl using 1
  funext n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.cast_succ]
    ring

theorem square_sandwich (x : ℝ) (hx : 0 < x) :
    1/(x+1)-1/(x+2) ≤ 1/(x+1)^2 ∧
    1/(x+1)^2 ≤ 1/x-1/(x+1) := by
  have h₁ : 1/(x+1)-1/(x+2) = 1/((x+1)*(x+2)) := by
    field_simp [show x+1 ≠ 0 by positivity, show x+2 ≠ 0 by positivity] <;> ring
  have h₂ : 1/x-1/(x+1) = 1/(x*(x+1)) := by
    field_simp [ne_of_gt hx, show x+1 ≠ 0 by positivity] <;> ring
  rw [h₁, h₂]
  constructor
  · exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  · exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)

theorem H_two_bounds (N : ℕ) (hN : 0 < N) :
    1/((N:ℝ)+1) ≤ H 2 N ∧ H 2 N ≤ 1/(N:ℝ) := by
  have hN' : 0 < (N:ℝ) := by exact_mod_cast hN
  have hL := delta_hasSum ((N:ℝ)+1) (by positivity)
  have hU := delta_hasSum (N:ℝ) hN'
  have hS := h_summable 2 N (by decide)
  constructor
  · unfold H
    rw [← hL.tsum_eq]
    refine Summable.tsum_le_tsum (fun n => ?_) hL.summable hS
    have h := (square_sandwich ((n:ℝ)+(N:ℝ)) (by positivity)).1
    convert h using 1 <;> ring
  · unfold H
    rw [← hU.tsum_eq]
    refine Summable.tsum_le_tsum (fun n => ?_) hS hU.summable
    have h := (square_sandwich ((n:ℝ)+(N:ℝ)) (by positivity)).2
    convert h using 1 <;> ring

theorem H_high_le (N q : ℕ) (hN : 0 < N) :
    H (q+2) N ≤ (1/(N:ℝ)^q) * H 2 N := by
  have hN' : 0 < (N:ℝ) := by exact_mod_cast hN
  have hS := h_summable (q+2) N (by omega)
  have hM := ((h_summable 2 N (by decide)).hasSum.mul_left (1/(N:ℝ)^q))
  unfold H
  rw [← hM.tsum_eq]
  refine Summable.tsum_le_tsum (fun n => ?_) hS hM.summable
  let x : ℝ := (n:ℝ)+(N:ℝ)+1
  change 1/x^(q+2) ≤ (1/(N:ℝ)^q)*(1/x^2)
  have hx : 0 < x := by dsimp [x]; positivity
  have hnx : (N:ℝ) ≤ x := by
    change (N:ℝ) ≤ (n:ℝ)+(N:ℝ)+1
    have hn : 0 ≤ (n:ℝ) := by positivity
    linarith only [hn]
  have hd : (N:ℝ)^q*x^2 ≤ x^(q+2) := by
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hN'.le hnx q) (by positivity)
  calc
    1/x^(q+2) ≤ 1/((N:ℝ)^q*x^2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hd
    _ = (1/(N:ℝ)^q)*(1/x^2) := by ring

theorem scaled_H_two :
    Tendsto (fun N : ℕ => (N:ℝ)*H 2 N) atTop (𝓝 1) := by
  have ht : Tendsto (fun N : ℕ => (N:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun N : ℕ => 1/((N:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp ht
  have hl : Tendsto (fun N : ℕ => 1-1/((N:ℝ)+1)) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub hz)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    have hN' : 0 < (N:ℝ) := by exact_mod_cast hN
    have h := mul_le_mul_of_nonneg_left (H_two_bounds N hN).1 hN'.le
    calc
      1-1/((N:ℝ)+1) = (N:ℝ)*(1/((N:ℝ)+1)) := by
        field_simp [show (N:ℝ)+1 ≠ 0 by positivity] <;> ring
      _ ≤ (N:ℝ)*H 2 N := h
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    have hN' : 0 < (N:ℝ) := by exact_mod_cast hN
    calc
      (N:ℝ)*H 2 N ≤ (N:ℝ)*(1/(N:ℝ)) :=
        mul_le_mul_of_nonneg_left (H_two_bounds N hN).2 hN'.le
      _ = 1 := by field_simp [ne_of_gt hN']

theorem scaled_H_high (q : ℕ) (hq : q ≠ 0) :
    Tendsto (fun N : ℕ => (N:ℝ)*H (q+2) N) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_div_pow 1 q hq) ?_ ?_
  · exact Eventually.of_forall (fun N => mul_nonneg (by positivity) (H_nonneg (q+2) N))
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    have hN' : 0 < (N:ℝ) := by exact_mod_cast hN
    calc
      (N:ℝ)*H (q+2) N ≤ (N:ℝ)*((1/(N:ℝ)^q)*H 2 N) :=
        mul_le_mul_of_nonneg_left (H_high_le N q hN) hN'.le
      _ = (1/(N:ℝ)^q)*((N:ℝ)*H 2 N) := by ring
      _ ≤ (1/(N:ℝ)^q)*((N:ℝ)*(1/(N:ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (H_two_bounds N hN).2 hN'.le
      _ = 1/(N:ℝ)^q := by field_simp [ne_of_gt hN']

noncomputable def shell (z2 z4 L : ℝ) : ℝ :=
  2*(L^2-1)*(z4/(64*L^4)+5*z2/(32*L^6)-35/(128*L^8))

theorem shell_formula (z2 z4 L : ℝ) (hL : L ≠ 0) :
    shell z2 z4 L =
      z4/32*(1/L^2-1/L^4)+5*z2/16*(1/L^4-1/L^6)-35/64*(1/L^6-1/L^8) := by
  unfold shell
  field_simp [hL] <;> ring

noncomputable def T (z2 z4 : ℝ) (N : ℕ) : ℝ :=
  z4/32*(H 2 N-H 4 N)+5*z2/16*(H 4 N-H 6 N)-35/64*(H 6 N-H 8 N)

theorem tail_hasSum (z2 z4 : ℝ) (N : ℕ) :
    HasSum (fun n : ℕ => shell z2 z4 ((n:ℝ)+(N:ℝ)+1)) (T z2 z4 N) := by
  have h2 := (h_summable 2 N (by decide)).hasSum
  have h4 := (h_summable 4 N (by decide)).hasSum
  have h6 := (h_summable 6 N (by decide)).hasSum
  have h8 := (h_summable 8 N (by decide)).hasSum
  have h := (((h2.sub h4).mul_left (z4/32)).add ((h4.sub h6).mul_left (5*z2/16))).sub
    ((h6.sub h8).mul_left (35/64:ℝ))
  unfold T H
  convert h using 1
  funext n
  exact shell_formula z2 z4 _ (by positivity)

theorem tail_asymptotic (z2 z4 : ℝ) :
    Tendsto (fun N : ℕ => (N:ℝ)*T z2 z4 N) atTop (𝓝 (z4/32)) := by
  have h4 : Tendsto (fun N : ℕ => (N:ℝ)*H 4 N) atTop (𝓝 0) :=
    scaled_H_high 2 (by decide)
  have h6 : Tendsto (fun N : ℕ => (N:ℝ)*H 6 N) atTop (𝓝 0) :=
    scaled_H_high 4 (by decide)
  have h8 : Tendsto (fun N : ℕ => (N:ℝ)*H 8 N) atTop (𝓝 0) :=
    scaled_H_high 6 (by decide)
  have h := (((scaled_H_two.sub h4).const_mul (z4/32)).add
      ((h4.sub h6).const_mul (5*z2/16))).sub
      ((h6.sub h8).const_mul (35/64:ℝ))
  convert h using 1
  · funext N
    unfold T
    ring
  · ring

#print axioms Manuscript16.V166Tail.H_two_bounds
#print axioms Manuscript16.V166Tail.H_high_le
#print axioms Manuscript16.V166Tail.tail_hasSum
#print axioms Manuscript16.V166Tail.tail_asymptotic

end Manuscript16.V166Tail
