import GegenbauerFock.RationalTrace
import Mathlib

/-!
# V007 — rigorous real-series remainder for the fifteen-term trace enclosure

We establish a *genuine infinite-series* bound for
  ∑ n, 1/(4^n n! (2n+1)).
The proof uses only factorial monotonicity and the geometric sum;
no floating-point evaluation and no unproved claim about exp(1/4).
The link to the actual Gaussian Hilbert–Schmidt integral is a separately
certified moment/Kummer identity and must be audited at its actual SHA.
-/

noncomputable section

namespace GegenbauerFock.RationalTrace

private def realTerm (n : ℕ) : ℝ :=
  1 / ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) * ((2*n+1 : ℕ) : ℝ))

private def geometricMajorant (k : ℕ) : ℝ :=
  (1 / ((4 : ℝ)^15 * (Nat.factorial 15 : ℝ) * 31)) * ((1 / 4 : ℝ)^k)

private theorem realTerm_nonneg (n : ℕ) : 0 ≤ realTerm n := by
  unfold realTerm
  positivity

private theorem realTerm_pos (n : ℕ) : 0 < realTerm n := by
  unfold realTerm
  positivity

private theorem realTerm_le_exponential (n : ℕ) :
    realTerm n ≤ (1 / 4 : ℝ)^n / (Nat.factorial n : ℝ) := by
  have hodd : (1 : ℝ) ≤ (((2*n+1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 1 ≤ 2*n+1 by omega)
  have hden :
      (4 : ℝ)^n * (Nat.factorial n : ℝ) ≤
        (4 : ℝ)^n * (Nat.factorial n : ℝ) * (((2*n+1 : ℕ) : ℝ)) := by
    calc
      (4 : ℝ)^n * (Nat.factorial n : ℝ) =
          (4 : ℝ)^n * (Nat.factorial n : ℝ) * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hodd (by positivity)
  have h := one_div_le_one_div_of_le
    (by positivity : 0 < (4 : ℝ)^n * (Nat.factorial n : ℝ)) hden
  unfold realTerm
  calc
    1 / ((4 : ℝ)^n * (Nat.factorial n : ℝ) * (((2*n+1 : ℕ) : ℝ))) ≤
      1 / ((4 : ℝ)^n * (Nat.factorial n : ℝ)) := h
    _ = (1 / 4 : ℝ)^n / (Nat.factorial n : ℝ) := by
      rw [one_div_pow]
      ring

private theorem realTerm_summable : Summable realTerm := by
  apply Summable.of_nonneg_of_le
  · exact realTerm_nonneg
  · exact realTerm_le_exponential
  · exact Real.summable_pow_div_factorial (1 / 4)

private theorem realTerm_tail_le_geometric (k : ℕ) :
    realTerm (15+k) ≤ geometricMajorant k := by
  have hf : (Nat.factorial 15 : ℝ) ≤
      (Nat.factorial (15+k) : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : 15 ≤ 15+k)
  have ho : (31 : ℝ) ≤ (((2*(15+k)+1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 31 ≤ 2*(15+k)+1 by omega)
  have hd :
      (4 : ℝ)^(15+k) * (Nat.factorial 15 : ℝ) * 31 ≤
        (4 : ℝ)^(15+k) * (Nat.factorial (15+k) : ℝ) *
          (((2*(15+k)+1 : ℕ) : ℝ)) := by
    gcongr
  have hi := one_div_le_one_div_of_le
    (by positivity :
      0 < (4 : ℝ)^(15+k) * (Nat.factorial 15 : ℝ) * 31) hd
  calc
    realTerm (15+k) =
      1 / ((4 : ℝ)^(15+k) * (Nat.factorial (15+k) : ℝ) *
        (((2*(15+k)+1 : ℕ) : ℝ))) := rfl
    _ ≤ 1 / ((4 : ℝ)^(15+k) * (Nat.factorial 15 : ℝ) * 31) := hi
    _ = geometricMajorant k := by
      unfold geometricMajorant
      rw [pow_add, one_div_pow]
      field_simp
      <;> ring

private theorem geometricMajorant_summable : Summable geometricMajorant := by
  unfold geometricMajorant
  exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)).mul_left
        (1 / ((4 : ℝ)^15 * (Nat.factorial 15 : ℝ) * 31))

/-- The actual infinite sum of the positive Taylor-tail terms has an
explicit upper bound which is strictly smaller than the published
(4/3)/(4^15·15!) majorant. -/
theorem fifteen_tail_strict_bound :
    (∑' k : ℕ, realTerm (15+k)) <
      (1 : ℝ) / 1053078495820775424000 := by
  have hs : Summable (fun k : ℕ => realTerm (15+k)) :=
    (summable_nat_add_iff 15).2 (by
      simpa only [add_comm] using realTerm_summable)
  have hle := hs.tsum_le_tsum realTerm_tail_le_geometric
    geometricMajorant_summable
  have hgeo :
      (∑' k : ℕ, geometricMajorant k) =
        (1 / ((4 : ℝ)^15 * (Nat.factorial 15 : ℝ) * 31)) * (4 / 3) := by
    unfold geometricMajorant
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)]
    norm_num
  have hstrict :
      (1 / ((4 : ℝ)^15 * (Nat.factorial 15 : ℝ) * 31)) * (4 / 3) <
        (1 : ℝ) / 1053078495820775424000 := by
    norm_num
  exact lt_of_le_of_lt (hle.trans_eq hgeo) hstrict

/-- Finite rational arithmetic supplies certified outward-rounded
24-decimal endpoints, independently of the infinite tail estimate. -/
theorem fifteen_rational_endpoints :
    ((1089974208367244447324816 : ℚ) / 10^24) <
      tracePartialSum 15 ∧
    tracePartialSum 15 + (1 : ℚ)/1053078495820775424000 <
      ((1089974208367244447325767 : ℚ) / 10^24) := by
  constructor
  · rw [partial_fifteen]
    norm_num
  · rw [partial_fifteen_plus_bound]
    norm_num

#print axioms GegenbauerFock.RationalTrace.fifteen_tail_strict_bound
#print axioms GegenbauerFock.RationalTrace.fifteen_rational_endpoints

end GegenbauerFock.RationalTrace
