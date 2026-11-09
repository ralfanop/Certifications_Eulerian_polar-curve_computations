import Mathlib

/-!
# Manuscript 14.119 — rigorous positive-series tail comparison

A universal theorem for a summable positive series whose tails have a
geometric majorant. It gives *strict* lower and upper bounds, including
the strict inequality when one step of the tail is strictly below the
geometric estimate.

This lemma is independent of any Eulerian analytic or numerical oracle.
Its specialization to the factorial series in Corollary 2.2 will be a
separate proof obligation.
-/

namespace SpecialImaginaryPoint.V14119Tail

/-- A strictly positive summable series admits a sharp geometric tail
comparison if all later ratios are at most q, with a strict inequality
at the second step. -/
theorem positive_series_tail_strict
    (f : ℕ → ℝ) (k : ℕ) (q : ℝ)
    (hpos : ∀ n, 0 < f n)
    (hsum : Summable f)
    (hqnonneg : 0 ≤ q) (hqlt : q < 1)
    (hstep : ∀ n, k ≤ n → f (n + 1) ≤ q * f n)
    (hstrict : f (k + 2) < q * f (k + 1)) :
    (∑ n ∈ Finset.range k, f n) < ∑' n, f n ∧
      (∑' n, f n) <
        (∑ n ∈ Finset.range k, f n) + f k / (1 - q) := by
  have hshift : Summable (fun n : ℕ => f (n + k)) :=
    (summable_nat_add_iff k).2 hsum
  have hbound (n : ℕ) : f (n + k) ≤ f k * q ^ n := by
    induction n with
    | zero =>
      simp
    | succ n ih =>
      have hs := hstep (n + k) (by omega)
      calc
        f ((n + 1) + k) = f ((n + k) + 1) := by congr 1 <;> omega
        _ ≤ q * f (n + k) := hs
        _ ≤ q * (f k * q ^ n) :=
          mul_le_mul_of_nonneg_left ih hqnonneg
        _ = f k * q ^ (n + 1) := by rw [pow_succ]; ring
  have hbound_strict : f (2 + k) < f k * q ^ 2 := by
    have hs := hstep k (by omega)
    calc
      f (2 + k) = f (k + 2) := by congr 1 <;> omega
      _ < q * f (k + 1) := hstrict
      _ ≤ q * (q * f k) := mul_le_mul_of_nonneg_left hs hqnonneg
      _ = f k * q ^ 2 := by ring
  have hgeosum : Summable (fun n : ℕ => f k * q ^ n) :=
    (summable_geometric_of_lt_one hqnonneg hqlt).mul_left (f k)
  have hlefun :
      (fun n : ℕ => f (n + k)) ≤ (fun n : ℕ => f k * q ^ n) :=
    fun n => hbound n
  have htail_lt :
      (∑' n : ℕ, f (n + k)) < (∑' n : ℕ, f k * q ^ n) :=
    Summable.tsum_lt_tsum (i := 2) hlefun hbound_strict hshift hgeosum
  have hgeo :
      (∑' n : ℕ, f k * q ^ n) = f k / (1 - q) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hqnonneg hqlt]
    ring
  have hpositive_tail : 0 < (∑' n : ℕ, f (n + k)) := by
    have hle : f (0 + k) ≤ ∑' n : ℕ, f (n + k) :=
      hshift.le_tsum 0 (fun n _ => le_of_lt (hpos (n + k)))
    simpa only [zero_add] using (lt_of_lt_of_le (hpos k) hle)
  have hdecomp := Summable.sum_add_tsum_nat_add k hsum
  constructor
  · linarith
  · rw [← hdecomp]
    exact add_lt_add_left (lt_of_lt_of_eq htail_lt hgeo) _

#print axioms SpecialImaginaryPoint.V14119Tail.positive_series_tail_strict

end SpecialImaginaryPoint.V14119Tail
