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
  · exact lt_of_lt_of_le hx2 (by norm_num)

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

/-!
## Exact endpoint: the simple-Parry trinomial root

At a real root beta of beta^31-beta^30-1 the first 31 digits terminate
with 1, and the 31st genuine floor iterate is zero.
-/

theorem parry31_endpoint_greedy (beta : ℝ)
    (hb : 1 < beta) (hlt2 : beta < 2)
    (hpoly : beta ^ 31 - beta ^ 30 - 1 = 0) :
    (∀ k : ℕ, k < 29 → greedyDigit beta (k + 1) = 0) ∧
      greedyDigit beta 30 = 1 ∧
      (greedyMap beta)^[31] 1 = 0 := by
  have hboundary : beta ^ 30 * (beta - 1) = 1 := by
    calc
      beta ^ 30 * (beta - 1) = beta ^ 31 - beta ^ 30 := by
        rw [pow_succ]
        ring
      _ = 1 := by linarith
  have hz (k : ℕ) (_hk1 : 1 ≤ k) (hk29 : k ≤ 29) :
      0 ≤ beta ^ k * (beta - 1) ∧ beta ^ k * (beta - 1) < 1 := by
    constructor
    · exact mul_nonneg (pow_nonneg (by linarith) _) (by linarith)
    · have hp : beta ^ k < beta ^ 30 :=
        pow_lt_pow_right₀ hb (by omega)
      have hmul := mul_lt_mul_of_pos_right hp (by linarith : 0 < beta - 1)
      rwa [hboundary] at hmul
  have hrem : greedyRemainder beta 30 = beta ^ 29 * (beta - 1) :=
    greedy_remainder_zero_run beta hb.le hlt2 29 hz 29 le_rfl
  have hproduct : beta * (beta ^ 29 * (beta - 1)) = 1 := by
    calc
      _ = beta ^ 30 * (beta - 1) := by
        rw [pow_succ]
        ring
      _ = 1 := hboundary
  have hdigit : greedyDigit beta 30 = 1 := by
    unfold greedyDigit
    rw [hrem, hproduct]
    norm_num
  have hreturn : greedyRemainder beta 31 = 0 := by
    change greedyMap beta (greedyRemainder beta 30) = 0
    rw [hrem]
    unfold greedyMap
    rw [hproduct]
    norm_num
  refine ⟨?_, hdigit, ?_⟩
  · intro k hk
    exact greedyDigit_zero_run beta hb.le hlt2 29 hz k hk
  · simpa only [greedyRemainder_eq_iterate] using hreturn

#print axioms Manuscript14Section11.parry31_endpoint_greedy

/-!
## Exact Fourier-to-hyperbolic identification at the companion point

This is an exact analytic identity (not a decimal enclosure).  The
certified 12-place strict rational enclosure is a separate obligation.
-/

/-- Restricting the Eulerian complex sine-cardinal profile to an
imaginary argument agrees with the real hyperbolic-sine normalization. -/
theorem eulerian_fourier_imaginary_sinh (b : ℝ) (hb : b ≠ 0) :
    (2 : ℂ) * Complex.sin (((b : ℂ) * Complex.I) / 2) /
        ((b : ℂ) * Complex.I) =
      ((2 * Real.sinh (b / 2) / b : ℝ) : ℂ) := by
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  have harg : ((b : ℂ) * Complex.I) / 2 =
      ((b : ℂ) / 2) * Complex.I := by ring
  rw [harg, Complex.sin_mul_I]
  have hsinh : Complex.sinh ((b : ℂ) / 2) =
      (Real.sinh (b / 2) : ℂ) := by
    simpa using (Complex.ofReal_sinh (b / 2)).symm
  rw [hsinh]
  push_cast
  field_simp [hbC, Complex.I_ne_zero]

/-- The Eulerian Fourier profile at i*sqrt(2) is exactly
sqrt(2)*sinh(1/sqrt(2)), the scalar in Manuscript 14.10. -/
theorem eulerian_fourier_companion_exact :
    (2 : ℂ) * Complex.sin (((Real.sqrt 2 : ℂ) * Complex.I) / 2) /
        ((Real.sqrt 2 : ℂ) * Complex.I) =
      ((Real.sqrt 2 * Real.sinh (1 / Real.sqrt 2) : ℝ) : ℂ) := by
  have hb : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
  have hhalf : Real.sqrt (2 : ℝ) / 2 = 1 / Real.sqrt 2 := by
    field_simp [hb]
    nlinarith [hs]
  have heq : (2 : ℝ) * Real.sinh (Real.sqrt 2 / 2) / Real.sqrt 2 =
      Real.sqrt 2 * Real.sinh (1 / Real.sqrt 2) := by
    rw [hhalf]
    field_simp [hb]
    nlinarith [hs]
  rw [eulerian_fourier_imaginary_sinh (Real.sqrt 2) hb]
  exact congrArg (fun t : ℝ => (t : ℂ)) heq

#print axioms Manuscript14Section11.eulerian_fourier_imaginary_sinh
#print axioms Manuscript14Section11.eulerian_fourier_companion_exact

/-!
## Exact interval transport to the critical-orbit defect

The input interval is presently established by the independent Arb/rational
certificate.  These kernel proofs show that every real parameter in that
interval satisfies the stated strict rational defect bounds, and that the
defect is computed from the genuine floor-map iterate.
-/

/-- Monotone transfer of the tight Eulerian bracket to the exact defect. -/
theorem parry_defect_tight_interval (beta : ℝ)
    (hlo : (1085441641272 : ℝ) / 10 ^ 12 < beta)
    (hhi : beta < (1085441641273 : ℝ) / 10 ^ 12) :
    (313240 : ℝ) / 10 ^ 9 < 1 - beta ^ 30 * (beta - 1) ∧
      1 - beta ^ 30 * (beta - 1) < (313241 : ℝ) / 10 ^ 9 := by
  let L : ℝ := (1085441641272 : ℝ) / 10 ^ 12
  let U : ℝ := (1085441641273 : ℝ) / 10 ^ 12
  have hpupper : beta ^ 30 ≤ U ^ 30 := by
    dsimp [U]
    gcongr <;> linarith
  have hplower : L ^ 30 ≤ beta ^ 30 := by
    dsimp [L]
    gcongr <;> linarith
  have hbeta : 0 ≤ beta - 1 := by linarith
  have hlpos : 0 ≤ L - 1 := by norm_num [L]
  have hbetaUpper : beta ^ 30 * (beta - 1) ≤ U ^ 30 * (U - 1) := by
    calc
      _ ≤ U ^ 30 * (beta - 1) :=
        mul_le_mul_of_nonneg_right hpupper hbeta
      _ ≤ U ^ 30 * (U - 1) :=
        mul_le_mul_of_nonneg_left (by dsimp [U]; linarith) (by positivity)
  have hbetaLower : L ^ 30 * (L - 1) ≤ beta ^ 30 * (beta - 1) := by
    calc
      _ ≤ beta ^ 30 * (L - 1) :=
        mul_le_mul_of_nonneg_right hplower hlpos
      _ ≤ beta ^ 30 * (beta - 1) :=
        mul_le_mul_of_nonneg_left (by dsimp [L]; linarith) (by positivity)
  have hnumLower : (313240 : ℝ) / 10 ^ 9 <
      1 - U ^ 30 * (U - 1) := by norm_num [U]
  have hnumUpper : 1 - L ^ 30 * (L - 1) <
      (313241 : ℝ) / 10 ^ 9 := by norm_num [L]
  constructor
  · exact lt_of_lt_of_le hnumLower (sub_le_sub_left hbetaUpper 1)
  · exact lt_of_le_of_lt (sub_le_sub_left hbetaLower 1) hnumUpper

/-- The 31st iterate, using the actual floor map, has the
strictly enclosed critical-orbit defect on the tight rational interval. -/
theorem parry_real_orbit_defect_tight_interval (beta : ℝ)
    (hlo : (1085441641272 : ℝ) / 10 ^ 12 < beta)
    (hhi : beta < (1085441641273 : ℝ) / 10 ^ 12) :
    1 - (greedyMap beta)^[31] 1 =
      1 - beta ^ 30 * (beta - 1) ∧
    (313240 : ℝ) / 10 ^ 9 < 1 - (greedyMap beta)^[31] 1 ∧
    1 - (greedyMap beta)^[31] 1 < (313241 : ℝ) / 10 ^ 9 := by
  have hlo6 : (10854 : ℝ) / 10000 < beta := by linarith
  have hhi6 : beta < (1085445 : ℝ) / 1000000 := by linarith
  obtain ⟨hzero, _⟩ := eulerian_initial_greedy_block beta hlo6 hhi6
  have hz : ∀ k : ℕ, 1 ≤ k → k ≤ 30 →
      0 ≤ beta ^ k * (beta - 1) ∧ beta ^ k * (beta - 1) < 1 :=
    fun k _ hk => hzero k hk
  have hrem : greedyRemainder beta 31 = beta ^ 30 * (beta - 1) :=
    greedy_remainder_zero_run beta (by linarith) (by linarith) 30 hz 30 le_rfl
  have horbit : 1 - (greedyMap beta)^[31] 1 =
      1 - beta ^ 30 * (beta - 1) := by
    simpa only [greedyRemainder_eq_iterate] using
      congrArg (fun x : ℝ => 1 - x) hrem
  obtain ⟨hl, hu⟩ := parry_defect_tight_interval beta hlo hhi
  refine ⟨horbit, ?_, ?_⟩
  · rwa [horbit]
  · rwa [horbit]

#print axioms Manuscript14Section11.parry_defect_tight_interval
#print axioms Manuscript14Section11.parry_real_orbit_defect_tight_interval

/-!
## Left-hand jump at the simple Parry threshold

For every beta strictly below the root, the first 30 greedy digits
after the leading one vanish; the 31st orbit coordinate is the
continuous polynomial beta^30 * (beta - 1).  At the root the floor
takes the exact integer 1, so the iterate returns to zero.
-/

open scoped Topology

/-- On the entire open interval (1, beta31), not merely on a small
numerical neighborhood, the 31st beta-orbit coordinate is polynomial. -/
theorem parry31_orbit_left_formula (root beta : ℝ)
    (hroot : 1 < root) (hroot2 : root < 2)
    (hpoly : root ^ 31 - root ^ 30 - 1 = 0)
    (hbeta : 1 < beta) (hbelow : beta < root) :
    (greedyMap beta)^[31] 1 = beta ^ 30 * (beta - 1) := by
  have hrootval : root ^ 30 * (root - 1) = 1 := by
    calc
      root ^ 30 * (root - 1) = root ^ 31 - root ^ 30 := by
        rw [pow_succ]
        ring
      _ = 1 := by linarith
  have hpow : beta ^ 30 ≤ root ^ 30 := by
    gcongr
  have hprod : beta ^ 30 * (beta - 1) < 1 := by
    calc
      _ ≤ root ^ 30 * (beta - 1) :=
        mul_le_mul_of_nonneg_right hpow (by linarith)
      _ < root ^ 30 * (root - 1) :=
        mul_lt_mul_of_pos_left (sub_lt_sub_right hbelow 1) (by positivity)
      _ = 1 := hrootval
  have hz (k : ℕ) (_hk1 : 1 ≤ k) (hk : k ≤ 30) :
      0 ≤ beta ^ k * (beta - 1) ∧ beta ^ k * (beta - 1) < 1 := by
    have hpowk : beta ^ k ≤ beta ^ 30 :=
      pow_le_pow_right₀ hbeta.le hk
    have hproductk : beta ^ k * (beta - 1) ≤ beta ^ 30 * (beta - 1) :=
      mul_le_mul_of_nonneg_right hpowk (by linarith)
    exact ⟨mul_nonneg (pow_nonneg (by linarith) _) (by linarith),
      lt_of_le_of_lt hproductk hprod⟩
  have hrem : greedyRemainder beta 31 = beta ^ 30 * (beta - 1) :=
    greedy_remainder_zero_run beta hbeta.le (hbelow.trans hroot2) 30 hz 30 le_rfl
  simpa only [greedyRemainder_eq_iterate] using hrem

/-- Genuine left-hand discontinuity of the 31st iterate, with
the floor convention used for the terminating greedy expansion. -/
theorem parry31_left_jump (root : ℝ)
    (hroot : 1 < root) (hroot2 : root < 2)
    (hpoly : root ^ 31 - root ^ 30 - 1 = 0) :
    Filter.Tendsto (fun beta : ℝ => (greedyMap beta)^[31] 1)
      (𝓝[<] root) (𝓝 (1 : ℝ)) ∧
    (greedyMap root)^[31] 1 = 0 := by
  have hrootval : root ^ 30 * (root - 1) = 1 := by
    calc
      root ^ 30 * (root - 1) = root ^ 31 - root ^ 30 := by
        rw [pow_succ]
        ring
      _ = 1 := by linarith
  have hcont : ContinuousAt (fun b : ℝ => b ^ 30 * (b - 1)) root := by
    fun_prop
  have hpoly_tendsto : Filter.Tendsto
      (fun b : ℝ => b ^ 30 * (b - 1))
      (𝓝[<] root) (𝓝 (1 : ℝ)) := by
    simpa only [hrootval] using
      (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  have heventually :
      (fun b : ℝ => (greedyMap b)^[31] 1) =ᶠ[𝓝[<] root]
        (fun b => b ^ 30 * (b - 1)) := by
    filter_upwards [Ioo_mem_nhdsLT hroot] with b hb
    exact parry31_orbit_left_formula root b hroot hroot2 hpoly hb.1 hb.2
  refine ⟨?_, (parry31_endpoint_greedy root hroot hroot2 hpoly).2.2⟩
  exact hpoly_tendsto.congr' heventually.symm

#print axioms Manuscript14Section11.parry31_orbit_left_formula
#print axioms Manuscript14Section11.parry31_left_jump

/-!
## Existence and uniqueness of the algebraic endpoint itself

The preceding discontinuity theorem takes the trinomial root as an
assumption.  This section produces the actual unique root in (1,2)
by the intermediate value theorem and strict polynomial monotonicity.
-/

/-- The Parry trinomial factor x^n (x-1) is strictly increasing on
[1,+infinity). -/
theorem parry_power_strict_mono (n : ℕ) (x y : ℝ)
    (hx : 1 ≤ x) (hxy : x < y) :
    x ^ n * (x - 1) < y ^ n * (y - 1) := by
  have hp : x ^ n ≤ y ^ n := by
    gcongr
  calc
    _ ≤ y ^ n * (x - 1) :=
      mul_le_mul_of_nonneg_right hp (by linarith)
    _ < y ^ n * (y - 1) :=
      mul_lt_mul_of_pos_left (sub_lt_sub_right hxy 1) (pow_pos (by linarith) n)

/-- There is exactly one Parry threshold beta_31 in the interval
(1,2), solving beta^31-beta^30-1=0. -/
theorem parry31_exists_unique_root :
    ∃! beta : ℝ, 1 < beta ∧ beta < 2 ∧
      beta ^ 31 - beta ^ 30 - 1 = 0 := by
  let f : ℝ → ℝ := fun b => b ^ 30 * (b - 1)
  have hcont : ContinuousOn f (Set.Icc (1 : ℝ) 2) := by
    dsimp [f]
    fun_prop
  have hmem : (1 : ℝ) ∈ Set.Icc (f 1) (f 2) := by
    norm_num [f, Set.mem_Icc]
  obtain ⟨beta, hbeta, hval⟩ :
      ∃ beta ∈ Set.Icc (1 : ℝ) 2, f beta = 1 :=
    (intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hcont) hmem
  have hb1 : 1 < beta := by
    rcases lt_or_eq_of_le hbeta.1 with h | h
    · exact h
    · subst beta
      norm_num [f] at hval
  have hb2 : beta < 2 := by
    rcases lt_or_eq_of_le hbeta.2 with h | h
    · exact h
    · subst beta
      norm_num [f] at hval
  change beta ^ 30 * (beta - 1) = 1 at hval
  have hp : beta ^ 31 - beta ^ 30 - 1 = 0 := by
    calc
      beta ^ 31 - beta ^ 30 - 1 =
          beta ^ 30 * (beta - 1) - 1 := by
        rw [pow_succ]
        ring
      _ = 0 := by rw [hval]; ring
  refine ⟨beta, ⟨hb1, hb2, hp⟩, ?_⟩
  intro y hy
  obtain ⟨hy1, hy2, hyP⟩ := hy
  have hyval : y ^ 30 * (y - 1) = 1 := by
    calc
      y ^ 30 * (y - 1) = y ^ 31 - y ^ 30 := by
        rw [pow_succ]
        ring
      _ = 1 := by linarith
  rcases lt_trichotomy beta y with hlt | heq | hgt
  · have hh := parry_power_strict_mono 30 beta y hb1.le hlt
    linarith
  · exact heq.symm
  · have hh := parry_power_strict_mono 30 y beta hy1.le hgt
    linarith

#print axioms Manuscript14Section11.parry_power_strict_mono
#print axioms Manuscript14Section11.parry31_exists_unique_root


/-!
## The adjacent trinomial endpoint and a unified exact comparison

This closes the *root-existence and interval-order* part of Section 11
for an arbitrary real parameter in the already-certified rational bracket.
The separate identification of the *actual* Eulerian sinh value with
that bracket is not assumed to have been kernel-proved.
-/

/-- The next member of the trinomial family has exactly one root in (1,2). -/
theorem parry32_exists_unique_root :
    ∃! beta : ℝ, 1 < beta ∧ beta < 2 ∧
      beta ^ 32 - beta ^ 31 - 1 = 0 := by
  let f : ℝ → ℝ := fun b => b ^ 31 * (b - 1)
  have hcont : ContinuousOn f (Set.Icc (1 : ℝ) 2) := by
    dsimp [f]
    fun_prop
  have hmem : (1 : ℝ) ∈ Set.Icc (f 1) (f 2) := by
    norm_num [f, Set.mem_Icc]
  obtain ⟨beta, hbeta, hval⟩ :
      ∃ beta ∈ Set.Icc (1 : ℝ) 2, f beta = 1 :=
    (intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hcont) hmem
  have hb1 : 1 < beta := by
    rcases lt_or_eq_of_le hbeta.1 with h | h
    · exact h
    · subst beta
      norm_num [f] at hval
  have hb2 : beta < 2 := by
    rcases lt_or_eq_of_le hbeta.2 with h | h
    · exact h
    · subst beta
      norm_num [f] at hval
  change beta ^ 31 * (beta - 1) = 1 at hval
  have hp : beta ^ 32 - beta ^ 31 - 1 = 0 := by
    calc
      beta ^ 32 - beta ^ 31 - 1 =
          beta ^ 31 * (beta - 1) - 1 := by
        rw [pow_succ]
        ring
      _ = 0 := by rw [hval]; ring
  refine ⟨beta, ⟨hb1, hb2, hp⟩, ?_⟩
  intro y hy
  obtain ⟨hy1, hy2, hyP⟩ := hy
  have hyval : y ^ 31 * (y - 1) = 1 := by
    calc
      y ^ 31 * (y - 1) = y ^ 32 - y ^ 31 := by
        rw [pow_succ]
        ring
      _ = 1 := by linarith
  rcases lt_trichotomy beta y with hlt | heq | hgt
  · have hh := parry_power_strict_mono 31 beta y hb1.le hlt
    linarith
  · exact heq.symm
  · have hh := parry_power_strict_mono 31 y beta hy1.le hgt
    linarith

/-- The two actual, uniquely defined trinomial roots straddle every
parameter satisfying the certified six-decimal bracket. -/
theorem parry_adjacent_roots_straddle (x : ℝ)
    (hlo : (10854 : ℝ) / 10000 < x)
    (hhi : x < (1085445 : ℝ) / 1000000) :
    ∃ beta32 beta31 : ℝ,
      (1 < beta32 ∧ beta32 < 2 ∧ beta32 ^ 32 - beta32 ^ 31 - 1 = 0) ∧
      (1 < beta31 ∧ beta31 < 2 ∧ beta31 ^ 31 - beta31 ^ 30 - 1 = 0) ∧
      beta32 < x ∧ x < beta31 := by
  obtain ⟨beta32, h32, _⟩ := parry32_exists_unique_root
  obtain ⟨beta31, h31, _⟩ := parry31_exists_unique_root
  have hx : 1 < x := by linarith
  obtain ⟨hgreater, hless⟩ := strict_parry_return x hlo hhi
  have h32value : beta32 ^ 31 * (beta32 - 1) = 1 := by
    calc
      beta32 ^ 31 * (beta32 - 1) = beta32 ^ 32 - beta32 ^ 31 := by
        rw [pow_succ]
        ring
      _ = 1 := by linarith [h32.2.2]
  have h31value : beta31 ^ 30 * (beta31 - 1) = 1 := by
    calc
      beta31 ^ 30 * (beta31 - 1) = beta31 ^ 31 - beta31 ^ 30 := by
        rw [pow_succ]
        ring
      _ = 1 := by linarith [h31.2.2]
  have h32lt : beta32 < x := by
    by_contra h
    have hle : x ≤ beta32 := le_of_not_gt h
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hm := parry_power_strict_mono 31 x beta32 hx.le hlt
      linarith
    · subst x
      linarith
  have h31gt : x < beta31 := by
    by_contra h
    have hle : beta31 ≤ x := le_of_not_gt h
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hm := parry_power_strict_mono 30 beta31 x h31.1.le hlt
      linarith
    · subst x
      linarith
  exact ⟨beta32, beta31, h32, h31, h32lt, h31gt⟩

/-- The distinguished *actual* Eulerian scalar (not a free real variable).
The tight rational enclosure is a distinct pending kernel obligation. -/
noncomputable def eulerianParameter : ℝ :=
  Real.sqrt 2 * Real.sinh (1 / Real.sqrt 2)

/-- Integrates the genuine floor recursion, both adjacent unique roots,
the exact defect and the discontinuity at the algebraic endpoint,
conditional only on an explicit rational enclosure of the actual
Eulerian scalar. -/
theorem eulerian_parry_theorem_conditional
    (hlo : (1085441641272 : ℝ) / 10 ^ 12 < eulerianParameter)
    (hhi : eulerianParameter < (1085441641273 : ℝ) / 10 ^ 12) :
    (greedyDigit eulerianParameter 0 = 1 ∧
      (∀ k : ℕ, k < 30 → greedyDigit eulerianParameter (k + 1) = 0) ∧
      greedyDigit eulerianParameter 31 = 1) ∧
    ((313240 : ℝ) / 10 ^ 9 <
      1 - (greedyMap eulerianParameter)^[31] 1 ∧
      1 - (greedyMap eulerianParameter)^[31] 1 <
        (313241 : ℝ) / 10 ^ 9) ∧
    (∃ beta32 beta31 : ℝ,
      (1 < beta32 ∧ beta32 < 2 ∧ beta32 ^ 32 - beta32 ^ 31 - 1 = 0) ∧
      (1 < beta31 ∧ beta31 < 2 ∧ beta31 ^ 31 - beta31 ^ 30 - 1 = 0) ∧
      beta32 < eulerianParameter ∧ eulerianParameter < beta31 ∧
      (greedyMap beta31)^[31] 1 = 0 ∧
      Filter.Tendsto (fun beta : ℝ => (greedyMap beta)^[31] 1)
        (𝓝[<] beta31) (𝓝 (1 : ℝ))) := by
  have hlo6 : (10854 : ℝ) / 10000 < eulerianParameter := by linarith
  have hhi6 : eulerianParameter < (1085445 : ℝ) / 1000000 := by linarith
  have hprefix := eulerian_greedy_prefix_floor eulerianParameter hlo6 hhi6
  have hdelta := parry_real_orbit_defect_tight_interval eulerianParameter hlo hhi
  obtain ⟨beta32, beta31, h32, h31, hbetween32, hbetween31⟩ :=
    parry_adjacent_roots_straddle eulerianParameter hlo6 hhi6
  obtain ⟨hlimit, hreturn⟩ :=
    parry31_left_jump beta31 h31.1 h31.2.1 h31.2.2
  exact ⟨hprefix, ⟨hdelta.2.1, hdelta.2.2⟩,
    ⟨beta32, beta31, h32, h31, hbetween32, hbetween31, hreturn, hlimit⟩⟩

#print axioms Manuscript14Section11.parry32_exists_unique_root
#print axioms Manuscript14Section11.parry_adjacent_roots_straddle
#print axioms Manuscript14Section11.eulerian_parry_theorem_conditional


end Manuscript14Section11
