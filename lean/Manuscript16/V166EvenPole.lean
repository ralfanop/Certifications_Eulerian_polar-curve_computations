import Mathlib

open Filter Finset
open scoped Topology BigOperators

namespace Manuscript16.V166EvenPole

/-- Even paired pole contributions, with the two outer half-lines and
    the reflected finite interval treated by convergent sums. -/
theorem even_paired_sum (f : ℕ → ℝ) (hf : Summable f) (m : ℕ) :
    (∑' n : ℕ, 2 * (f n + f (n+(m+1)))) +
      (∑ j ∈ range m, (f j + f (m-1-j))) =
        4 * (∑' n : ℕ, f n) - 2 * f m := by
  have hs := (summable_nat_add_iff (m+1)).2 hf
  have h := (hf.hasSum.add hs.hasSum).mul_left (2 : ℝ)
  rw [h.tsum_eq, Finset.sum_add_distrib, Finset.sum_range_reflect]
  have hsplit := hf.sum_add_tsum_nat_add (m+1)
  rw [Finset.sum_range_succ] at hsplit
  linarith

noncomputable def reciprocal (p n : ℕ) : ℝ := 1 / ((n:ℝ)+1)^p

theorem reciprocal_summable (p : ℕ) (hp : 1 < p) :
    Summable (reciprocal p) := by
  change Summable (fun n : ℕ => 1/((n:ℝ)+1)^p)
  have h : Summable (fun n : ℕ => 1/(n:ℝ)^p) :=
    Real.summable_one_div_nat_pow.mpr hp
  simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 h

/-- The positive-index series equals the standard real p-series,
    whose zero-index summand is zero in Mathlib. -/
theorem reciprocal_zeta_sum (p : ℕ) (hp : 1 < p) :
    (∑' n : ℕ, reciprocal p n) = ∑' n : ℕ, 1/(n:ℝ)^p := by
  have h : Summable (fun n : ℕ => 1/(n:ℝ)^p) :=
    Real.summable_one_div_nat_pow.mpr hp
  have hp0 : p ≠ 0 := by omega
  have hs := h.sum_add_tsum_nat_add 1
  simpa only [Finset.sum_range_one, Nat.cast_zero, zero_pow hp0, div_zero,
    zero_add, Nat.cast_add, Nat.cast_one, reciprocal] using hs

/-- This specializes to p=2 and p=4 in the fourth-power partial fraction
    identity. No separation of a harmonic p=1 sum is allowed. -/
theorem even_reciprocal_poles (p : ℕ) (hp : 1 < p) (m : ℕ) :
    (∑' n : ℕ, 2*(reciprocal p n + reciprocal p (n+(m+1)))) +
      (∑ j ∈ range m, (reciprocal p j + reciprocal p (m-1-j))) =
        4*(∑' n : ℕ, 1/(n:ℝ)^p) - 2/((m:ℝ)+1)^p := by
  calc
    _ = 4*(∑' n : ℕ, reciprocal p n)-2*reciprocal p m :=
      even_paired_sum (reciprocal p) (reciprocal_summable p hp) m
    _ = _ := by rw [reciprocal_zeta_sum p hp, reciprocal, mul_one_div]

#print axioms Manuscript16.V166EvenPole.even_paired_sum
#print axioms Manuscript16.V166EvenPole.reciprocal_summable
#print axioms Manuscript16.V166EvenPole.reciprocal_zeta_sum
#print axioms Manuscript16.V166EvenPole.even_reciprocal_poles

end Manuscript16.V166EvenPole