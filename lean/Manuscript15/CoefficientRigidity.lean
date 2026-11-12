/-
Manuscript 15 — coefficient uniqueness, 10 November 2026.

For an even entire characteristic function f(t) = sum c_n t^(2n),
the differential equation
  1 - f(2t) - 2t f'(2t) = t² f(t)²/2
formally yields
  (2n+3) 4^(n+1) c_(n+1) =
    - (1/2) sum_(j=0)^n c_j c_(n-j).

This module proves uniqueness of a sequence satisfying this recurrence and c_0=1.
Extraction of the recurrence from analytic Taylor coefficients, and the
characteristic-function uniqueness theorem, are NOT certified in this module.
-/
import Mathlib

namespace Manuscript15

/-- The exact recurrence extracted from the proposed cycloidal kinematics,
written using n+1 so all coefficients on the right have smaller index. -/
def CoefficientRule (c : ℕ → ℝ) : Prop :=
  c 0 = 1 ∧
    ∀ n : ℕ,
      (((2 * (n + 1) + 1 : ℕ) : ℝ) * (4 : ℝ) ^ (n + 1)) * c (n + 1) =
        - ((1 / 2 : ℝ) * ∑ j ∈ Finset.range (n + 1), c j * c (n - j))

/-- Once c_0=1, the cycloidal coefficient recurrence has at most one solution. -/
theorem coefficientRule_unique (c d : ℕ → ℝ)
    (hc : CoefficientRule c) (hd : CoefficientRule d) : c = d := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      exact hc.1.trans hd.1.symm
    | succ k =>
      have hsum :
          (∑ j ∈ Finset.range (k + 1), c j * c (k - j)) =
          (∑ j ∈ Finset.range (k + 1), d j * d (k - j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < k + 1 := Finset.mem_range.mp hj
        have hleft : c j = d j := ih j (by omega)
        have hright : c (k - j) = d (k - j) := ih (k - j) (by omega)
        rw [hleft, hright]
      have hfactor :
          (((2 * (k + 1) + 1 : ℕ) : ℝ) * (4 : ℝ) ^ (k + 1)) ≠ 0 := by
        positivity
      have heq :
          (((2 * (k + 1) + 1 : ℕ) : ℝ) * (4 : ℝ) ^ (k + 1)) * c (k + 1) =
          (((2 * (k + 1) + 1 : ℕ) : ℝ) * (4 : ℝ) ^ (k + 1)) * d (k + 1) := by
        calc
          _ = - ((1 / 2 : ℝ) *
              ∑ j ∈ Finset.range (k + 1), c j * c (k - j)) := hc.2 k
          _ = - ((1 / 2 : ℝ) *
              ∑ j ∈ Finset.range (k + 1), d j * d (k - j)) := by rw [hsum]
          _ = _ := (hd.2 k).symm
      exact (mul_left_cancel₀ hfactor) heq


/-! ### First forced coefficients of the two-scale rigidity recurrence -/

/-- The coefficient of t² is uniquely forced by the rule. -/
theorem coefficientRule_c_one (c : ℕ → ℝ) (hc : CoefficientRule c) :
    c 1 = -(1 / 24 : ℝ) := by
  have h := hc.2 0
  norm_num [Finset.sum_range_succ, hc.1] at h
  linarith

/-- The coefficient of t⁴ is uniquely forced by the rule. -/
theorem coefficientRule_c_two (c : ℕ → ℝ) (hc : CoefficientRule c) :
    c 2 = (1 / 1920 : ℝ) := by
  have h := hc.2 1
  have h1 := coefficientRule_c_one c hc
  norm_num [Finset.sum_range_succ, hc.1, h1] at h
  linarith

/-- The coefficient of t⁶ is uniquely forced by the rule. -/
theorem coefficientRule_c_three (c : ℕ → ℝ) (hc : CoefficientRule c) :
    c 3 = -(1 / 322560 : ℝ) := by
  have h := hc.2 2
  have h1 := coefficientRule_c_one c hc
  have h2 := coefficientRule_c_two c hc
  norm_num [Finset.sum_range_succ, hc.1, h1, h2] at h
  linarith


/-! ### Higher forced coefficients, matching the seven explicit manuscript values -/

/-- The recurrence forces c_4 without numerical approximation. -/
theorem coefficientRule_c_four (c : ℕ → ℝ) (hc : CoefficientRule c) :
    c 4 = (1 / 92897280 : ℝ) := by
  have h := hc.2 3
  have h1 := coefficientRule_c_one c hc
  have h2 := coefficientRule_c_two c hc
  have h3 := coefficientRule_c_three c hc
  norm_num [Finset.sum_range_succ, hc.1, h1, h2, h3] at h
  linarith

/-- The recurrence forces c_5 without numerical approximation. -/
theorem coefficientRule_c_five (c : ℕ → ℝ) (hc : CoefficientRule c) :
    c 5 = -(1 / 40874803200 : ℝ) := by
  have h := hc.2 4
  have h1 := coefficientRule_c_one c hc
  have h2 := coefficientRule_c_two c hc
  have h3 := coefficientRule_c_three c hc
  have h4 := coefficientRule_c_four c hc
  norm_num [Finset.sum_range_succ, hc.1, h1, h2, h3, h4] at h
  linarith

/-- The recurrence forces c_6 without numerical approximation. -/
theorem coefficientRule_c_six (c : ℕ → ℝ) (hc : CoefficientRule c) :
    c 6 = (1 / 25505877196800 : ℝ) := by
  have h := hc.2 5
  have h1 := coefficientRule_c_one c hc
  have h2 := coefficientRule_c_two c hc
  have h3 := coefficientRule_c_three c hc
  have h4 := coefficientRule_c_four c hc
  have h5 := coefficientRule_c_five c hc
  norm_num [Finset.sum_range_succ, hc.1, h1, h2, h3, h4, h5] at h
  linarith

/-- The recurrence forces c_7 without numerical approximation. -/
theorem coefficientRule_c_seven (c : ℕ → ℝ) (hc : CoefficientRule c) :
    c 7 = -(1 / 21424936845312000 : ℝ) := by
  have h := hc.2 6
  have h1 := coefficientRule_c_one c hc
  have h2 := coefficientRule_c_two c hc
  have h3 := coefficientRule_c_three c hc
  have h4 := coefficientRule_c_four c hc
  have h5 := coefficientRule_c_five c hc
  have h6 := coefficientRule_c_six c hc
  norm_num [Finset.sum_range_succ, hc.1, h1, h2, h3, h4, h5, h6] at h
  linarith


/-! ### Further exact Taylor coefficient consequences, c₈–c₁₀ -/

/-- Exact c_8 coefficient forced by the conditional cycloidal
CoefficientRule, with no floating-point input or arbitrary assumptions. -/
theorem coefficientRule_c_eight (c : ℕ → ℝ) (hc : CoefficientRule c) :
    c 8 = (1 / 23310331287699456000 : ℝ) := by
  have h := hc.2 7
  have h1 := coefficientRule_c_one c hc
  have h2 := coefficientRule_c_two c hc
  have h3 := coefficientRule_c_three c hc
  have h4 := coefficientRule_c_four c hc
  have h5 := coefficientRule_c_five c hc
  have h6 := coefficientRule_c_six c hc
  have h7 := coefficientRule_c_seven c hc
  norm_num [Finset.sum_range_succ, hc.1, h1, h2, h3, h4, h5, h6, h7] at h
  linarith

/-- Exact c_9 coefficient forced by the conditional cycloidal
CoefficientRule, with no floating-point input or arbitrary assumptions. -/
theorem coefficientRule_c_nine (c : ℕ → ℝ) (hc : CoefficientRule c) :
    c 9 = -(1 / 31888533201572855808000 : ℝ) := by
  have h := hc.2 8
  have h1 := coefficientRule_c_one c hc
  have h2 := coefficientRule_c_two c hc
  have h3 := coefficientRule_c_three c hc
  have h4 := coefficientRule_c_four c hc
  have h5 := coefficientRule_c_five c hc
  have h6 := coefficientRule_c_six c hc
  have h7 := coefficientRule_c_seven c hc
  have h8 := coefficientRule_c_eight c hc
  norm_num [Finset.sum_range_succ, hc.1, h1, h2, h3, h4, h5, h6, h7, h8] at h
  linarith

/-- Exact c_10 coefficient forced by the conditional cycloidal
CoefficientRule, with no floating-point input or arbitrary assumptions. -/
theorem coefficientRule_c_ten (c : ℕ → ℝ) (hc : CoefficientRule c) :
    c 10 = (1 / 53572735778642397757440000 : ℝ) := by
  have h := hc.2 9
  have h1 := coefficientRule_c_one c hc
  have h2 := coefficientRule_c_two c hc
  have h3 := coefficientRule_c_three c hc
  have h4 := coefficientRule_c_four c hc
  have h5 := coefficientRule_c_five c hc
  have h6 := coefficientRule_c_six c hc
  have h7 := coefficientRule_c_seven c hc
  have h8 := coefficientRule_c_eight c hc
  have h9 := coefficientRule_c_nine c hc
  norm_num [Finset.sum_range_succ, hc.1, h1, h2, h3, h4, h5, h6, h7, h8, h9] at h
  linarith

/-! ### Further exact forced rigidity coefficients c₁₁–c₁₃ -/

/-- Exact c_11 forced by the conditional cycloidal two-scale coefficient rule. -/
theorem coefficientRule_c_eleven (c : ℕ → ℝ) (hc : CoefficientRule c) :
    c 11 = -(1 / 108431217215972213061058560000 : ℝ) := by
  have h := hc.2 10
  have h1 := coefficientRule_c_one c hc
  have h2 := coefficientRule_c_two c hc
  have h3 := coefficientRule_c_three c hc
  have h4 := coefficientRule_c_four c hc
  have h5 := coefficientRule_c_five c hc
  have h6 := coefficientRule_c_six c hc
  have h7 := coefficientRule_c_seven c hc
  have h8 := coefficientRule_c_eight c hc
  have h9 := coefficientRule_c_nine c hc
  have h10 := coefficientRule_c_ten c hc
  norm_num [Finset.sum_range_succ, hc.1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10] at h
  linarith

/-- Exact c_12 forced by the conditional cycloidal two-scale coefficient rule. -/
theorem coefficientRule_c_twelve (c : ℕ → ℝ) (hc : CoefficientRule c) :
    c 12 = (1 / 260234921318333311346540544000000 : ℝ) := by
  have h := hc.2 11
  have h1 := coefficientRule_c_one c hc
  have h2 := coefficientRule_c_two c hc
  have h3 := coefficientRule_c_three c hc
  have h4 := coefficientRule_c_four c hc
  have h5 := coefficientRule_c_five c hc
  have h6 := coefficientRule_c_six c hc
  have h7 := coefficientRule_c_seven c hc
  have h8 := coefficientRule_c_eight c hc
  have h9 := coefficientRule_c_nine c hc
  have h10 := coefficientRule_c_ten c hc
  have h11 := coefficientRule_c_eleven c hc
  norm_num [Finset.sum_range_succ, hc.1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] at h
  linarith

/-- Exact c_13 forced by the conditional cycloidal two-scale coefficient rule. -/
theorem coefficientRule_c_thirteen (c : ℕ → ℝ) (hc : CoefficientRule c) :
    c 13 = -(1 / 730739659061879938261085847552000000 : ℝ) := by
  have h := hc.2 12
  have h1 := coefficientRule_c_one c hc
  have h2 := coefficientRule_c_two c hc
  have h3 := coefficientRule_c_three c hc
  have h4 := coefficientRule_c_four c hc
  have h5 := coefficientRule_c_five c hc
  have h6 := coefficientRule_c_six c hc
  have h7 := coefficientRule_c_seven c hc
  have h8 := coefficientRule_c_eight c hc
  have h9 := coefficientRule_c_nine c hc
  have h10 := coefficientRule_c_ten c hc
  have h11 := coefficientRule_c_eleven c hc
  have h12 := coefficientRule_c_twelve c hc
  norm_num [Finset.sum_range_succ, hc.1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12] at h
  linarith

#print axioms Manuscript15.coefficientRule_c_eleven
#print axioms Manuscript15.coefficientRule_c_twelve
#print axioms Manuscript15.coefficientRule_c_thirteen

#print axioms Manuscript15.coefficientRule_c_eight
#print axioms Manuscript15.coefficientRule_c_nine
#print axioms Manuscript15.coefficientRule_c_ten

#print axioms Manuscript15.coefficientRule_c_four
#print axioms Manuscript15.coefficientRule_c_five
#print axioms Manuscript15.coefficientRule_c_six
#print axioms Manuscript15.coefficientRule_c_seven

#print axioms Manuscript15.coefficientRule_c_one
#print axioms Manuscript15.coefficientRule_c_two
#print axioms Manuscript15.coefficientRule_c_three

#print axioms Manuscript15.coefficientRule_unique

end Manuscript15
