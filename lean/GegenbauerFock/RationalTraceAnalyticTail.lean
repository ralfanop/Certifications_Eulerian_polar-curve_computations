import GegenbauerFock.RationalTrace
import GegenbauerFock.UltrasphericalKummerBridge
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
  have hs' : Summable (fun k : ℕ => realTerm (k + 15)) :=
    (summable_nat_add_iff 15).2 realTerm_summable
  have hs : Summable (fun k : ℕ => realTerm (15+k)) := by
    simpa only [add_comm] using hs'
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


/-- The λ=1/2 normalized ultraspherical even-moment ratio is exactly
1/(2n+1), as required for the Eulerian uniform-law specialization. -/
theorem kummer_ratio_half (n : ℕ) :
    KummerCoefficients.ratio (1 / 2 : ℝ) n =
      1 / (((2*n+1 : ℕ) : ℝ)) := by
  induction n with
  | zero =>
      norm_num [KummerCoefficients.ratio]
  | succ n ih =>
      rw [KummerCoefficients.ratio_succ, ih]
      have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      have h2 : (n : ℝ) + (1 / 2 : ℝ) + 1 ≠ 0 := by positivity
      have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
      push_cast
      field_simp
      <;> ring

/-- Identify the exact scalar Taylor series with the actual
unregularized Kummer series at the Eulerian parameter. -/
theorem kummer_half_quarter_eq_realTraceSeries :
    KummerCoefficients.kummerSeries (1 / 2) (1 / 4) =
      ∑' n : ℕ, realTerm n := by
  unfold KummerCoefficients.kummerSeries
  apply tsum_congr
  intro n
  rw [kummer_ratio_half]
  unfold realTerm
  rw [one_div_pow]
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hp : (4 : ℝ)^n ≠ 0 := by positivity
  have ho : (((2*n+1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp
  <;> ring

/-- The full Eulerian special integral equals the genuine positive
trace-coefficient series; no asymptotic or floating-point assumption. -/
theorem legendre_exp_integral_eq_realTraceSeries :
    (∫ u : ℝ, Real.exp (u ^ 2 / 4)
      ∂(GegenbauerFock.Ultraspherical.measure (1 / 2))) =
      ∑' n : ℕ, realTerm n := by
  have h :=
    GegenbauerFock.GeneralUltrasphericalFock.exp_integral_eq_kummerSeries
      (1 / 2) 1 (by norm_num) (by norm_num)
  simpa only [mul_one] using h.trans kummer_half_quarter_eq_realTraceSeries

private theorem fifteen_real_partial_exact :
    (∑ n ∈ Finset.range 15, realTerm n) =
      (337212679483569969430703669 : ℝ) /
        309376751206532288348160000 := by
  norm_num [realTerm, Finset.sum_range_succ]

/-- The two printed decimal bounds hold for the actual normalized
ultraspherical exponential integral in the Eulerian case. -/
theorem legendre_exp_integral_decimal_enclosure :
    ((1089974208367244447324816 : ℝ) / 10^24) <
       (∫ u : ℝ, Real.exp (u ^ 2 / 4)
         ∂(GegenbauerFock.Ultraspherical.measure (1 / 2))) ∧
       (∫ u : ℝ, Real.exp (u ^ 2 / 4)
         ∂(GegenbauerFock.Ultraspherical.measure (1 / 2))) <
      ((1089974208367244447325767 : ℝ) / 10^24) := by
  have hs : Summable realTerm := realTerm_summable
  have hdecomp :
      (∑' n : ℕ, realTerm n) =
        (∑ n ∈ Finset.range 15, realTerm n) +
          (∑' k : ℕ, realTerm (15+k)) := by
    simpa only [Nat.add_comm] using
      (hs.sum_add_tsum_nat_add 15).symm
  have htail_nonneg :
      0 ≤ ∑' k : ℕ, realTerm (15+k) :=
    tsum_nonneg (fun k => realTerm_nonneg (15+k))
  have htail_small := fifteen_tail_strict_bound
  rw [legendre_exp_integral_eq_realTraceSeries]
  rw [hdecomp, fifteen_real_partial_exact]
  constructor
  · have hlo :
        ((1089974208367244447324816 : ℝ) / 10^24) <
          (337212679483569969430703669 : ℝ) /
            309376751206532288348160000 := by norm_num
    linarith
  · have hhi :
        (337212679483569969430703669 : ℝ) /
            309376751206532288348160000 +
          (1 : ℝ) / 1053078495820775424000 <
          ((1089974208367244447325767 : ℝ) / 10^24) := by norm_num
    linarith

#print axioms GegenbauerFock.RationalTrace.kummer_ratio_half
#print axioms GegenbauerFock.RationalTrace.kummer_half_quarter_eq_realTraceSeries
#print axioms GegenbauerFock.RationalTrace.legendre_exp_integral_eq_realTraceSeries
#print axioms GegenbauerFock.RationalTrace.legendre_exp_integral_decimal_enclosure

end GegenbauerFock.RationalTrace
