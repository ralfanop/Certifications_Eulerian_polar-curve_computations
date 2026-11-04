import Mathlib

/-!
# Manuscript 14, Section 11 — rational Parry-threshold certificates

Kernel checks for rational polynomial signs and transport of inequalities.
The analytic identification with the Eulerian sinc/hyperbolic-sine value,
and the invariant-density theorem, remain separate proof obligations.
-/

namespace Manuscript14Section11

private def leftBracket : ℚ := 10854 / 10000
private def rightBracket : ℚ := 1085445 / 1000000

theorem f32_left_positive :
    (1 : ℚ) < leftBracket ^ 31 * (leftBracket - 1) := by
  norm_num [leftBracket]

theorem f31_right_negative :
    rightBracket ^ 30 * (rightBracket - 1) < (1 : ℚ) := by
  norm_num [rightBracket]

theorem delta_left_exact :
    (313240 : ℚ) / 10^9 <
      1 - (1085441641273 : ℚ) ^ 30 / (10^12)^30 *
            ((1085441641273 : ℚ) / 10^12 - 1) := by
  norm_num

theorem delta_right_exact :
    1 - (1085441641272 : ℚ) ^ 30 / (10^12)^30 *
            ((1085441641272 : ℚ) / 10^12 - 1) <
      (313241 : ℚ) / 10^9 := by
  norm_num

theorem strict_parry_return (x : ℝ)
    (hx_lower : (10854 : ℝ) / 10000 < x)
    (hx_upper : x < (1085445 : ℝ) / 1000000) :
    1 < x ^ 31 * (x - 1) ∧ x ^ 30 * (x - 1) < 1 := by
  have hp : (0 : ℝ) ≤ x := by
    linarith
  have hlo : (1 : ℝ) <
      ((10854 : ℝ) / 10000)^31 * ((10854 : ℝ) / 10000 - 1) := by
    norm_num
  have hhi : ((1085445 : ℝ) / 1000000)^30 *
        ((1085445 : ℝ) / 1000000 - 1) < 1 := by
    norm_num
  constructor
  · have hpow : ((10854 : ℝ) / 10000)^31 ≤ x^31 := by
      gcongr
    have hmul : ((10854 : ℝ) / 10000)^31 *
        ((10854 : ℝ) / 10000 - 1) ≤ x^31 * (x-1) := by
      calc
        _ ≤ x^31 * ((10854 : ℝ) / 10000 - 1) :=
          mul_le_mul_of_nonneg_right hpow (by norm_num)
        _ ≤ x^31 * (x - 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · have hpow : x^30 ≤ ((1085445 : ℝ) / 1000000)^30 := by
      gcongr
    have hpos : (0 : ℝ) ≤ x - 1 := by
      linarith
    have hmul : x^30 * (x-1) ≤
        ((1085445 : ℝ) / 1000000)^30 *
        ((1085445 : ℝ) / 1000000 - 1) := by
      calc
        _ ≤ ((1085445 : ℝ) / 1000000)^30 * (x - 1) :=
          mul_le_mul_of_nonneg_right hpow hpos
        _ ≤ ((1085445 : ℝ) / 1000000)^30 *
            ((1085445 : ℝ) / 1000000 - 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith


/-- The defining trinomial of beta_31 gives the exact finite
Parry digit value 1/beta + 1/beta^31 = 1, without decimals. -/
theorem parry31_two_digit_identity (beta : ℝ)
    (hbeta : beta ≠ 0)
    (hpoly : beta ^ 31 - beta ^ 30 - 1 = 0) :
    (1 : ℝ) = 1 / beta + 1 / beta ^ 31 := by
  have hp : beta ^ 31 ≠ 0 := pow_ne_zero _ hbeta
  have heq : beta ^ 31 = beta ^ 30 + 1 := by
    linarith
  calc
    (1 : ℝ) = beta ^ 31 / beta ^ 31 := (div_self hp).symm
    _ = (beta ^ 30 + 1) / beta ^ 31 := by rw [heq]
    _ = 1 / beta + 1 / beta ^ 31 := by
      field_simp [hbeta]

#print axioms Manuscript14Section11.parry31_two_digit_identity


/-- All the precritical powers remain in [0,1), providing the zero-digit
inequalities for the greedy beta expansion after its initial digit 1. -/
theorem precritical_zero_digit_bounds (beta : ℝ)
    (hbeta : 1 < beta) (hfirst : beta ^ 30 * (beta - 1) < 1)
    (k : ℕ) (hk : k ≤ 30) :
    0 ≤ beta ^ k * (beta - 1) ∧ beta ^ k * (beta - 1) < 1 := by
  have hpow : beta ^ k ≤ beta ^ 30 := by
    gcongr <;> linarith
  have hm : beta ^ k * (beta - 1) ≤ beta ^ 30 * (beta - 1) :=
    mul_le_mul_of_nonneg_right hpow (by linarith)
  constructor
  · exact mul_nonneg (pow_nonneg (by linarith) _) (by linarith)
  · linarith

/-- At the next digit, the greedy remainder lies strictly between 1 and 2:
its integer part is 1, and not 0 or 2. -/
theorem next_one_digit_bounds (beta : ℝ)
    (hbeta : 1 < beta) (hlt2 : beta < 2)
    (hfirst : beta ^ 30 * (beta - 1) < 1)
    (hnext : 1 < beta ^ 31 * (beta - 1)) :
    1 < beta ^ 31 * (beta - 1) ∧ beta ^ 31 * (beta - 1) < 2 := by
  constructor
  · exact hnext
  · have hmul := mul_lt_mul_of_pos_left hfirst (by linarith : 0 < beta)
    calc
      beta ^ 31 * (beta - 1) = beta * (beta ^ 30 * (beta - 1)) := by ring
      _ < beta := by nlinarith
      _ < 2 := hlt2

/-- All inequalities needed for the initial greedy beta digit block
1 0^30 1, assuming the certified rational bracket for the parameter. -/
theorem eulerian_initial_greedy_block (beta : ℝ)
    (hlo : (10854 : ℝ) / 10000 < beta)
    (hhi : beta < (1085445 : ℝ) / 1000000) :
    (∀ k : ℕ, k ≤ 30 →
      0 ≤ beta ^ k * (beta - 1) ∧ beta ^ k * (beta - 1) < 1) ∧
    (1 < beta ^ 31 * (beta - 1) ∧ beta ^ 31 * (beta - 1) < 2) := by
  have hb : 1 < beta := by linarith
  have hb2 : beta < 2 := by linarith
  obtain ⟨hn, hf⟩ := strict_parry_return beta hlo hhi
  exact ⟨fun k hk => precritical_zero_digit_bounds beta hb hf k hk,
         next_one_digit_bounds beta hb hb2 hf hn⟩

#print axioms Manuscript14Section11.precritical_zero_digit_bounds
#print axioms Manuscript14Section11.next_one_digit_bounds
#print axioms Manuscript14Section11.eulerian_initial_greedy_block

#print axioms Manuscript14Section11.f32_left_positive
#print axioms Manuscript14Section11.f31_right_negative
#print axioms Manuscript14Section11.delta_left_exact
#print axioms Manuscript14Section11.delta_right_exact
#print axioms Manuscript14Section11.strict_parry_return

/-!
## The actual floor-based greedy map (as opposed to conditional digit inequalities)

We use the same endpoint convention as Manuscript 14.10:
T_beta(x) = beta*x - floor(beta*x), including x=1.
The digits are indexed from 0, so digit 0 is the first greedy digit.
-/

noncomputable def greedyMap (beta : ℝ) (x : ℝ) : ℝ :=
  beta * x - (⌊beta * x⌋ : ℤ)

noncomputable def greedyRemainder (beta : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => greedyMap beta (greedyRemainder beta n)

noncomputable def greedyDigit (beta : ℝ) (n : ℕ) : ℤ :=
  ⌊beta * greedyRemainder beta n⌋

private theorem floor_one_of_mem (x : ℝ) (hx1 : 1 ≤ x) (hx2 : x < 2) :
    ⌊x⌋ = (1 : ℤ) := by
  apply (Int.floor_eq_iff).2
  constructor
  · simpa using hx1
  · change x < 2
    exact hx2

private theorem floor_zero_of_mem (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ⌊x⌋ = (0 : ℤ) := by
  apply (Int.floor_eq_iff).2
  constructor
  · simpa using hx0
  · simpa using hx1

theorem greedyDigit_first (beta : ℝ) (h1 : 1 ≤ beta) (h2 : beta < 2) :
    greedyDigit beta 0 = 1 := by
  simpa [greedyDigit, greedyRemainder] using floor_one_of_mem beta h1 h2

theorem greedyRemainder_first (beta : ℝ) (h1 : 1 ≤ beta) (h2 : beta < 2) :
    greedyRemainder beta 1 = beta - 1 := by
  have hd : ⌊beta⌋ = (1 : ℤ) := floor_one_of_mem beta h1 h2
  simp [greedyRemainder, greedyMap, hd]

/-- The recursive remainders agree with iterates of the actual beta transformation. -/
theorem greedyRemainder_eq_iterate (beta : ℝ) (n : ℕ) :
    greedyRemainder beta n = (greedyMap beta)^[n] 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [greedyRemainder, Function.iterate_succ_apply', ← ih]

/-- A block of zero digits gives the exact polynomial remainder formula. -/
theorem greedy_remainder_zero_run (beta : ℝ)
    (h1 : 1 ≤ beta) (h2 : beta < 2) (N : ℕ)
    (hzeros : ∀ k : ℕ, 1 ≤ k → k ≤ N →
      0 ≤ beta ^ k * (beta - 1) ∧ beta ^ k * (beta - 1) < 1)
    (k : ℕ) (hk : k ≤ N) :
    greedyRemainder beta (k + 1) = beta ^ k * (beta - 1) := by
  induction k with
  | zero =>
      simpa using (greedyRemainder_first beta h1 h2)
  | succ k ih =>
      have hkprev : k ≤ N := by omega
      have hz := hzeros (k + 1) (by omega) hk
      have heq : beta * (beta ^ k * (beta - 1)) =
          beta ^ (k + 1) * (beta - 1) := by
        rw [pow_succ]
        ring
      have hd : ⌊beta * (beta ^ k * (beta - 1))⌋ = (0 : ℤ) := by
        rw [heq]
        exact floor_zero_of_mem _ hz.1 hz.2
      change greedyMap beta (greedyRemainder beta (k + 1)) =
        beta ^ (k + 1) * (beta - 1)
      rw [ih hkprev]
      rw [greedyMap, hd, heq]
      simp

/-- All the intermediate digits are literally the floor of the iterate, and zero. -/
theorem greedyDigit_zero_run (beta : ℝ)
    (h1 : 1 ≤ beta) (h2 : beta < 2) (N : ℕ)
    (hzeros : ∀ k : ℕ, 1 ≤ k → k ≤ N →
      0 ≤ beta ^ k * (beta - 1) ∧ beta ^ k * (beta - 1) < 1)
    (k : ℕ) (hk : k < N) :
    greedyDigit beta (k + 1) = 0 := by
  have hrem := greedy_remainder_zero_run beta h1 h2 N hzeros k (by omega)
  have hz := hzeros (k + 1) (by omega) (by omega)
  have heq : beta * (beta ^ k * (beta - 1)) =
      beta ^ (k + 1) * (beta - 1) := by
    rw [pow_succ]
    ring
  unfold greedyDigit
  rw [hrem, heq]
  exact floor_zero_of_mem _ hz.1 hz.2

/-- The next digit is 1 once the polynomial remainder crosses the integer boundary. -/
theorem greedyDigit_next_one (beta : ℝ)
    (h1 : 1 ≤ beta) (h2 : beta < 2) (N : ℕ)
    (hzeros : ∀ k : ℕ, 1 ≤ k → k ≤ N →
      0 ≤ beta ^ k * (beta - 1) ∧ beta ^ k * (beta - 1) < 1)
    (hnext : 1 ≤ beta ^ (N + 1) * (beta - 1))
    (hnext2 : beta ^ (N + 1) * (beta - 1) < 2) :
    greedyDigit beta (N + 1) = 1 := by
  have hrem := greedy_remainder_zero_run beta h1 h2 N hzeros N le_rfl
  have heq : beta * (beta ^ N * (beta - 1)) =
      beta ^ (N + 1) * (beta - 1) := by
    rw [pow_succ]
    ring
  unfold greedyDigit
  rw [hrem, heq]
  exact floor_one_of_mem _ hnext hnext2

/-- The strict Eulerian rational bracket yields the actual greedy prefix
1, thirty zero digits, 1. -/
theorem eulerian_greedy_prefix_floor (beta : ℝ)
    (hlo : (10854 : ℝ) / 10000 < beta)
    (hhi : beta < (1085445 : ℝ) / 1000000) :
    greedyDigit beta 0 = 1 ∧
    (∀ k : ℕ, k < 30 → greedyDigit beta (k + 1) = 0) ∧
    greedyDigit beta 31 = 1 := by
  have hb : 1 ≤ beta := by linarith
  have hb2 : beta < 2 := by linarith
  obtain ⟨hzero, hnext⟩ := eulerian_initial_greedy_block beta hlo hhi
  have hz : ∀ k : ℕ, 1 ≤ k → k ≤ 30 →
      0 ≤ beta ^ k * (beta - 1) ∧ beta ^ k * (beta - 1) < 1 :=
    fun k _ hk => hzero k hk
  refine ⟨greedyDigit_first beta hb hb2, ?_, ?_⟩
  · intro k hk
    exact greedyDigit_zero_run beta hb hb2 30 hz k hk
  · exact greedyDigit_next_one beta hb hb2 30 hz hnext.1.le hnext.2

#print axioms Manuscript14Section11.greedyRemainder_eq_iterate
#print axioms Manuscript14Section11.greedy_remainder_zero_run
#print axioms Manuscript14Section11.greedyDigit_zero_run
#print axioms Manuscript14Section11.greedyDigit_next_one
#print axioms Manuscript14Section11.eulerian_greedy_prefix_floor

end Manuscript14Section11
