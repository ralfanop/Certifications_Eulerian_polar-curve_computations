import Mathlib

open Filter Finset
open scoped Topology BigOperators

namespace Manuscript16.V166PairedPole

/-- A single telescoping difference; no summability of f is assumed. -/
theorem step_hasSum (f : ℕ → ℝ) (hf : Antitone f)
    (hz : Tendsto f atTop (𝓝 0)) :
    HasSum (fun n => f n - f (n+1)) (f 0) := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun n => sub_nonneg.mpr
    (hf (Nat.le_succ n))) _).2 ?_
  have hl : Tendsto (fun n => f 0 - f n) atTop (𝓝 (f 0)) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => f 0) atTop (𝓝 (f 0))).sub hz)
  convert hl using 1
  funext n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- The paired difference remains summable at the harmonic exponent. -/
theorem shift_hasSum (f : ℕ → ℝ) (hf : Antitone f)
    (hz : Tendsto f atTop (𝓝 0)) (L : ℕ) :
    HasSum (fun n => f n - f (n+L)) (∑ j ∈ range L, f j) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have ht : Tendsto (fun n : ℕ => n+L) atTop atTop :=
      tendsto_atTop_mono (f := fun n : ℕ => n) (fun n => by omega) tendsto_id
    have hzero : Tendsto (fun n : ℕ => f (n+L)) atTop (𝓝 0) := by
      simpa only [Function.comp_def] using hz.comp ht
    have hanti : Antitone (fun n : ℕ => f (n+L)) := by
      intro a b hab
      exact hf (Nat.add_le_add_right hab L)
    have hs := step_hasSum (fun n : ℕ => f (n+L)) hanti hzero
    have h := ih.add hs
    rw [Finset.sum_range_succ]
    convert h using 1
    funext n
    change f n - f (n+(L+1)) = (f n-f (n+L)) + (f (n+L)-f (n+1+L))
    rw [show n+1+L = n+(L+1) by omega]
    ring

theorem external_hasSum (f : ℕ → ℝ) (hf : Antitone f)
    (hz : Tendsto f atTop (𝓝 0)) (L : ℕ) :
    HasSum (fun n => 2*(f (n+L)-f n)) (-2*(∑ j ∈ range L, f j)) := by
  have h := (shift_hasSum f hf hz L).mul_left (-2 : ℝ)
  convert h using 1
  funext n
  ring

/-- Two exterior half-lines and the reflected finite interior. -/
theorem paired_poles (f : ℕ → ℝ) (hf : Antitone f)
    (hz : Tendsto f atTop (𝓝 0)) (m : ℕ) :
    (∑' n : ℕ, 2*(f (n+(m+1))-f n)) +
      (∑ j ∈ range m, (f j + f (m-1-j))) = -2*f m := by
  rw [(external_hasSum f hf hz (m+1)).tsum_eq, Finset.sum_add_distrib,
    Finset.sum_range_reflect, Finset.sum_range_succ]
  ring

noncomputable def reciprocal (p n : ℕ) : ℝ := 1/((n:ℝ)+1)^p

theorem reciprocal_antitone (p : ℕ) : Antitone (reciprocal p) := by
  intro a b hab
  have h : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
  unfold reciprocal
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by linarith) p

theorem reciprocal_tendsto (p : ℕ) (hp : p ≠ 0) :
    Tendsto (reciprocal p) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => n+1) atTop atTop :=
    tendsto_atTop_mono (f := fun n : ℕ => n) (fun n => by omega) tendsto_id
  simpa only [reciprocal, Function.comp_def, Nat.cast_add, Nat.cast_one] using
    (tendsto_const_div_pow 1 p hp).comp ht

/-- Applies in particular to p=1 and p=3 (odd partial fractions). -/
theorem reciprocal_paired_poles (p : ℕ) (hp : p ≠ 0) (m : ℕ) :
    (∑' n : ℕ, 2*(reciprocal p (n+(m+1))-reciprocal p n)) +
      (∑ j ∈ range m, (reciprocal p j + reciprocal p (m-1-j))) =
        -2/((m:ℝ)+1)^p := by
  have h := paired_poles (reciprocal p) (reciprocal_antitone p)
    (reciprocal_tendsto p hp) m
  simpa only [reciprocal, mul_one_div, neg_mul, neg_div] using h

/-- Rational identity behind the fourth-power convolution. -/
theorem fourth_partial_fraction (x L : ℝ) (hx : x ≠ 0)
    (hL : L ≠ 0) (hxl : x+L ≠ 0) :
    1/(x^4*(x+L)^4) =
      (1/x^4+1/(x+L)^4)/L^4 +
      4*(1/(x+L)^3-1/x^3)/L^5 +
      10*(1/x^2+1/(x+L)^2)/L^6 +
      20*(1/(x+L)-1/x)/L^7 := by
  field_simp [hx, hL, hxl] <;> ring

#print axioms Manuscript16.V166PairedPole.shift_hasSum
#print axioms Manuscript16.V166PairedPole.external_hasSum
#print axioms Manuscript16.V166PairedPole.paired_poles
#print axioms Manuscript16.V166PairedPole.reciprocal_paired_poles
#print axioms Manuscript16.V166PairedPole.fourth_partial_fraction

end Manuscript16.V166PairedPole
