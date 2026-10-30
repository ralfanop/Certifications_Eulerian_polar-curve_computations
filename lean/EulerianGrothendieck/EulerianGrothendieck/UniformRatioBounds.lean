import EulerianGrothendieck.CumulantBounds
import EulerianGrothendieck.PolynomialAbsoluteBounds

/-! Bounds for the actual normalized uniform-moment polynomials, uniformly
in their moment index. -/
noncomputable section
open scoped BigOperators
open Finset Polynomial
namespace EulerianGrothendieck

def ratioRecurrenceCoefficient (n j : ℕ) : ℝ :=
  2^(j+1)*(n.descFactorial j:ℝ)*standardUniformCumulant j

theorem uniformRatioPolynomial_zero : uniformRatioPolynomial 0 = 1 := by
  simp [uniformRatioPolynomial, V033.UniformSum.normalizedEGFPolynomial]

theorem ratioRecurrenceCoefficient_zero (n : ℕ) : ratioRecurrenceCoefficient n 0 = 1 := by
  simp [ratioRecurrenceCoefficient, standardUniformCumulant_zero]

theorem ratioRecurrenceCoefficient_bound (n j : ℕ) :
    |ratioRecurrenceCoefficient n j| ≤ 2*(4*(n:ℝ))^j := by
  have hf : (n.descFactorial j:ℝ) ≤ (n:ℝ)^j := by
    exact_mod_cast Nat.descFactorial_le_pow n j
  unfold ratioRecurrenceCoefficient
  rw [abs_mul, abs_of_nonneg (by positivity)]
  calc
    (2^(j+1)*(n.descFactorial j:ℝ))*|standardUniformCumulant j| ≤
        (2^(j+1)*(n:ℝ)^j)*2^j := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hf (by positivity))
        (standardUniformCumulant_bound j) (abs_nonneg _) (by positivity)
    _ = 2*(4*(n:ℝ))^j := by
      rw [pow_succ, mul_pow, show (4:ℝ)^j = 2^j*2^j by rw [← mul_pow]; norm_num]
      ring

theorem uniformRatioPolynomial_recurrence (n : ℕ) :
    uniformRatioPolynomial (n+1) =
      ∑ j ∈ range (n+1), C (ratioRecurrenceCoefficient n j)*X^j*
        uniformRatioPolynomial (n-j) := by
  rw [uniformRatioPolynomial, V033.UniformSum.normalizedEGFPolynomial, ← mul_assoc,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hf : ((n-j).factorial:ℝ)*(n.descFactorial j:ℝ) = (n.factorial:ℝ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial hjn
  have hp : (2:ℝ)^(j+1)*2^(n-j) = 2^(n+1) := by
    rw [← pow_add, show j+1+(n-j)=n+1 by omega]
  have hn : (n+1:ℝ) ≠ 0 := by positivity
  have hnorm : (2^(n+1)*((n+1).factorial:ℝ))*(n+1:ℝ)⁻¹ = 2^(n+1)*(n.factorial:ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  have hc : (2^(n+1)*((n+1).factorial:ℝ))*(n+1:ℝ)⁻¹*
      (12^(j+1)*V033.UniformSum.cumulantCoefficient j) =
      ratioRecurrenceCoefficient n j*(2^(n-j)*((n-j).factorial:ℝ)) := by
    unfold ratioRecurrenceCoefficient standardUniformCumulant
    rw [hnorm]
    calc
      _ = (2^(j+1)*2^(n-j))*(((n-j).factorial:ℝ)*(n.descFactorial j:ℝ))*
          (12^(j+1)*V033.UniformSum.cumulantCoefficient j) := by rw [hp, hf]
      _ = _ := by ring
  unfold uniformRatioPolynomial
  calc
    _ = C ((2^(n+1)*((n+1).factorial:ℝ))*(n+1:ℝ)⁻¹*
        (12^(j+1)*V033.UniformSum.cumulantCoefficient j))*X^j*
        V033.UniformSum.normalizedEGFPolynomial (n-j) := by simp only [map_mul]; ring
    _ = _ := by rw [hc]; simp only [map_mul]; ring

theorem uniformRatio_abs_recurrence (n : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    polyAbsEval (uniformRatioPolynomial (n+1)) h ≤
      polyAbsEval (uniformRatioPolynomial n) h +
      ∑ j ∈ range n, |ratioRecurrenceCoefficient n (j+1)| * h^(j+1)*
        polyAbsEval (uniformRatioPolynomial (n-(j+1))) h := by
  rw [uniformRatioPolynomial_recurrence]
  calc
    _ ≤ ∑ j ∈ range (n+1), polyAbsEval
        (C (ratioRecurrenceCoefficient n j)*X^j*uniformRatioPolynomial (n-j)) h :=
      polyAbsEval_sum_le _ _ _ hh
    _ = ∑ j ∈ range (n+1), |ratioRecurrenceCoefficient n j| * h^j*
        polyAbsEval (uniformRatioPolynomial (n-j)) h := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_assoc, polyAbsEval_C_mul, polyAbsEval_X_pow_mul]
      ring
    _ = _ := by rw [Finset.sum_range_succ']; simp [ratioRecurrenceCoefficient_zero]; ring

theorem finite_geometric_positive_tail_bound (s : ℝ) (n : ℕ)
    (hs : 0 ≤ s) (hs1 : s < 1) :
    (∑ j ∈ range n, s^(j+1)) ≤ s/(1-s) := by
  have hsum := (hasSum_geometric_of_lt_one hs hs1).mul_left s
  have h := hsum.summable.sum_le_tsum (range n) (fun j hj => by positivity)
  rw [hsum.tsum_eq] at h
  simpa [pow_succ, mul_comm, div_eq_mul_inv] using h

/-- The radius is deliberately conservative; it proves the required polynomial
coefficient growth without Bernoulli-number or analytic Cauchy estimates. -/
theorem uniformRatio_small_radius_bound (K n : ℕ) (hK : 1 ≤ K) (hn : n ≤ K) :
    polyAbsEval (uniformRatioPolynomial n) (1/(128*(K:ℝ)^2)) ≤ 1+(n:ℝ)/(K:ℝ) := by
  have hK0 : (0:ℝ) < K := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hK)
  have hK1 : (1:ℝ) ≤ K := by exact_mod_cast hK
  let h : ℝ := 1/(128*(K:ℝ)^2)
  let s : ℝ := 4*(K:ℝ)*h
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hs_eq : s = 1/(32*(K:ℝ)) := by dsimp [s, h]; field_simp; ring
  have hs1 : s < 1 := by rw [hs_eq]; apply (div_lt_one (by positivity)).2; linarith
  have ht : 4*(s/(1-s)) ≤ 1/(K:ℝ) := by
    rw [hs_eq]
    have hd : 0 < 32*(K:ℝ)-1 := by linarith
    calc
      4*(1/(32*(K:ℝ))/(1-1/(32*(K:ℝ)))) = 4/(32*(K:ℝ)-1) := by field_simp
      _ ≤ 1/(K:ℝ) := (div_le_div_iff₀ hd hK0).2 (by linarith)
  change polyAbsEval (uniformRatioPolynomial n) h ≤ _
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [uniformRatioPolynomial_zero, polyAbsEval_one]
    | succ n =>
      have hnK : n ≤ K := by omega
      have hnreal : (n:ℝ) ≤ K := by exact_mod_cast hnK
      have hbase := ih n (by omega) hnK
      have htail : (∑ j ∈ range n, |ratioRecurrenceCoefficient n (j+1)| * h^(j+1)*
          polyAbsEval (uniformRatioPolynomial (n-(j+1))) h) ≤ 1/(K:ℝ) := by
        calc
          _ ≤ ∑ j ∈ range n, 4*s^(j+1) := by
            apply Finset.sum_le_sum
            intro j hj
            have hi := ih (n-(j+1)) (by omega) (by omega)
            have hi2 : polyAbsEval (uniformRatioPolynomial (n-(j+1))) h ≤ 2 := by
              have hsub : ((n-(j+1):ℕ):ℝ) ≤ K := by exact_mod_cast (show n-(j+1) ≤ K by omega)
              have := (div_le_one hK0).2 hsub
              linarith
            have hb : |ratioRecurrenceCoefficient n (j+1)| * h^(j+1) ≤ 2*s^(j+1) := by
              calc
                _ ≤ (2*(4*(n:ℝ))^(j+1))*h^(j+1) :=
                  mul_le_mul_of_nonneg_right (ratioRecurrenceCoefficient_bound n (j+1))
                    (pow_nonneg hh _)
                _ = 2*(4*(n:ℝ)*h)^(j+1) := by rw [mul_pow]; ring
                _ ≤ 2*s^(j+1) := by
                  apply mul_le_mul_of_nonneg_left _ (by norm_num)
                  apply pow_le_pow_left₀ (by positivity)
                  dsimp [s]
                  exact mul_le_mul_of_nonneg_right (by linarith) hh
            calc
              _ ≤ (2*s^(j+1))*2 := mul_le_mul hb hi2
                (polyAbsEval_nonneg _ h hh) (by positivity)
              _ = 4*s^(j+1) := by ring
          _ = 4*∑ j ∈ range n, s^(j+1) := by rw [Finset.mul_sum]
          _ ≤ 4*(s/(1-s)) := mul_le_mul_of_nonneg_left
            (finite_geometric_positive_tail_bound s n hs hs1) (by norm_num)
          _ ≤ 1/(K:ℝ) := ht
      have hr := uniformRatio_abs_recurrence n h hh
      push_cast
      rw [add_div]
      linarith

theorem uniformRatio_coefficient_bound (k r : ℕ) :
    |(uniformRatioPolynomial k).coeff r| ≤ 2*(128*(k+1:ℝ)^2)^r := by
  apply polyAbsEval_coeff_bound _ _ (by positivity)
  have h := uniformRatio_small_radius_bound (k+1) k (by omega) (by omega)
  have hk : (k:ℝ)/(k+1:ℝ) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  push_cast at h
  linarith

end EulerianGrothendieck
