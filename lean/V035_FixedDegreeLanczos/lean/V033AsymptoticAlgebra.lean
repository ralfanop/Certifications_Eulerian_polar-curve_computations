import V033Core

namespace V033

/-- Exact algebraic remainder, valid for every real j, hence every fixed natural j.
    u,v are the bounded second-order remainders of the adjacent squared norms.
    Their existence for the uniform-sum measure is proved in the accompanying
    mathematical report, not assumed to have been formalised by this lemma. -/
theorem two_term_exact_remainder (j M u v : ℝ) (hM : M ≠ 0)
    (hd : 1 - (3*(j-1)*(j-2)/10)/M + v/M^2 ≠ 0) :
    (j*M/12) *
       ((1 - (3*j*(j-1)/10)/M + u/M^2) /
        (1 - (3*(j-1)*(j-2)/10)/M + v/M^2))
    - (j*M/12 - j*(j-1)/20) =
    (j/(12*M)) *
      ((u-v - (3*(j-1)/5)*(3*(j-1)*(j-2)/10) + (3*(j-1)/5)*v/M) /
       (1 - (3*(j-1)*(j-2)/10)/M + v/M^2)) := by
  generalize hddef : (1 - (3*(j-1)*(j-2)/10)/M + v/M^2) = d at hd ⊢
  field_simp [hM, hd]
  rw [← hddef]
  field_simp
  <;> ring

/-- A quantitative O(1/M) transfer; all hypotheses are explicit. -/
theorem remainder_bound (j M R d C : ℝ)
    (hM : 0 < M) (hR : |R| ≤ C) (hd : (1:ℝ)/2 ≤ |d|) :
    |(j/(12*M))*(R/d)| ≤ (|j| * C/6)/M := by
  have hC : 0 ≤ C := le_trans (abs_nonneg R) hR
  have hd0 : 0 < |d| := by linarith
  have h12 : 0 < 12*M := by positivity
  rw [abs_mul, abs_div, abs_div, abs_of_pos h12]
  have hfrac : |R| / |d| ≤ 2*C := (div_le_iff₀ hd0).2 (by nlinarith)
  calc
    |j| / (12*M) * (|R| / |d|) ≤ |j| / (12*M) * (2*C) :=
      mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = (|j| * C/6)/M := by ring

theorem norm_first_order_difference (j : ℝ) :
    (3*j*(j-1)/10) - (3*(j-1)*(j-2)/10) = 3*(j-1)/5 := by ring

theorem original_scale_second_term (j : ℝ) :
    (j/12) * (-(3*(j-1)/5)) = -(j*(j-1)/20) := by ring

#print axioms two_term_exact_remainder
#print axioms remainder_bound
#print axioms norm_first_order_difference
#print axioms original_scale_second_term
end V033
