import Mathlib
import SpecialImaginaryPoint.ParryThresholds

/-!
# Algebraicity forced by a repeated affine greedy remainder

A generic mathematical step toward the non-eventual-periodicity portion
of Manuscript 14.10, Theorem 11.1.

A real orbit generated from 1 by x_{n+1} = beta*x_n - d_n,
where the digits d_n are rational, has a monic polynomial expression
of degree n in beta. If distinct orbit indices coincide, beta is
algebraic over the rationals. This is not yet the assertion that
eventually periodic *digits* force repeated orbit states.
No transcendence theorem is imported or assumed here.
-/

namespace Manuscript14Section11

/-- Exact monic polynomial representing a finite affine orbit. -/
noncomputable def affineOrbitPolynomial (d : ℕ → ℚ) : ℕ → Polynomial ℚ
  | 0 => 1
  | n + 1 => Polynomial.X * affineOrbitPolynomial d n -
      Polynomial.C (d n)

/-- Finite affine orbit polynomials are monic of the exact expected degree. -/
theorem affineOrbitPolynomial_monic_degree (d : ℕ → ℚ) (n : ℕ) :
    (affineOrbitPolynomial d n).Monic ∧
      (affineOrbitPolynomial d n).natDegree = n := by
  induction n with
  | zero => simp [affineOrbitPolynomial]
  | succ n ih =>
      have hX : (Polynomial.X * affineOrbitPolynomial d n).Monic :=
        Polynomial.monic_X.mul ih.1
      have hdeg :
          (Polynomial.C (d n)).degree <
            (Polynomial.X * affineOrbitPolynomial d n).degree := by
        calc
          _ ≤ 0 := Polynomial.degree_C_le
          _ < _ := by
            rw [Polynomial.degree_eq_natDegree hX.ne_zero,
              Polynomial.natDegree_X_mul ih.1.ne_zero, ih.2]
            positivity
      constructor
      · change (Polynomial.X * affineOrbitPolynomial d n -
            Polynomial.C (d n)).Monic
        exact hX.sub_of_left hdeg
      · change (Polynomial.X * affineOrbitPolynomial d n -
            Polynomial.C (d n)).natDegree = n + 1
        rw [Polynomial.natDegree_sub_C,
          Polynomial.natDegree_X_mul ih.1.ne_zero, ih.2]

/-- The real values of the finite affine orbit are evaluations
of their exact monic rational polynomials. -/
theorem affineOrbitPolynomial_aeval (d : ℕ → ℚ) (beta : ℝ)
    (r : ℕ → ℝ) (hzero : r 0 = 1)
    (hstep : ∀ n, r (n + 1) = beta * r n - (d n : ℝ))
    (n : ℕ) :
    Polynomial.aeval beta (affineOrbitPolynomial d n) = r n := by
  induction n with
  | zero => simpa [affineOrbitPolynomial] using hzero.symm
  | succ n ih =>
      rw [hstep n]
      change Polynomial.aeval beta
        (Polynomial.X * affineOrbitPolynomial d n -
          Polynomial.C (d n)) = _
      simp only [map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [ih]
      simp

/-- Two different positions have different monic polynomial forms. -/
theorem affineOrbitPolynomial_ne_of_lt (d : ℕ → ℚ)
    (i j : ℕ) (hij : i < j) :
    affineOrbitPolynomial d i ≠ affineOrbitPolynomial d j := by
  intro heq
  have hdeg := congrArg (fun p : Polynomial ℚ => p.natDegree) heq
  rw [(affineOrbitPolynomial_monic_degree d i).2,
    (affineOrbitPolynomial_monic_degree d j).2] at hdeg
  omega

/-- A rational-digit affine orbit starting at one cannot repeat two
different states unless its real multiplier is algebraic over Q. -/
theorem algebraic_of_affine_orbit_repeat (d : ℕ → ℚ) (beta : ℝ)
    (r : ℕ → ℝ) (hzero : r 0 = 1)
    (hstep : ∀ n, r (n + 1) = beta * r n - (d n : ℝ))
    (i j : ℕ) (hij : i < j) (hrepeat : r i = r j) :
    IsAlgebraic ℚ beta := by
  rw [isAlgebraic_iff_not_injective]
  intro hinj
  have heval :
      Polynomial.aeval beta (affineOrbitPolynomial d i) =
      Polynomial.aeval beta (affineOrbitPolynomial d j) := by
    rw [affineOrbitPolynomial_aeval d beta r hzero hstep i,
      affineOrbitPolynomial_aeval d beta r hzero hstep j]
    exact hrepeat
  exact affineOrbitPolynomial_ne_of_lt d i j hij (hinj heval)

#print axioms Manuscript14Section11.affineOrbitPolynomial_monic_degree
#print axioms Manuscript14Section11.affineOrbitPolynomial_aeval
#print axioms Manuscript14Section11.affineOrbitPolynomial_ne_of_lt
#print axioms Manuscript14Section11.algebraic_of_affine_orbit_repeat


/-!
## Eventual digit periodicity forces a repeated orbit state

The key dynamical argument avoids a second infinite-series construction.
When the digits agree after a shift p, the difference of the two shifted
remainders evolves by multiplication by beta at every step. For beta > 1
this is incompatible with the fact that both remainders remain in [0,1],
unless the difference vanishes identically. We then invoke the
kernel-checked monic-polynomial lemma above.
-/

/-- Shifted remainders under an eventually periodic rational digit sequence
satisfy an exact homogeneous linear recurrence. -/
theorem affine_shift_difference (d : ℕ → ℚ) (beta : ℝ)
    (r : ℕ → ℝ)
    (hstep : ∀ n, r (n + 1) = beta * r n - (d n : ℝ))
    (m p : ℕ)
    (hperiod : ∀ n, m ≤ n → d (n + p) = d n) (n : ℕ) :
    r (m + p + n) - r (m + n) =
      beta ^ n * (r (m + p) - r m) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hd : d (m + p + n) = d (m + n) := by
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          using hperiod (m + n) (by omega)
      calc
        r (m + p + (n + 1)) - r (m + (n + 1)) =
            (beta * r (m + p + n) - (d (m + p + n) : ℝ)) -
              (beta * r (m + n) - (d (m + n) : ℝ)) := by
                rw [show m + p + (n + 1) = (m + p + n) + 1 by omega,
                    show m + (n + 1) = (m + n) + 1 by omega]
                rw [hstep, hstep]
        _ = beta * (r (m + p + n) - r (m + n)) := by
          rw [hd]
          ring
        _ = beta ^ (n + 1) * (r (m + p) - r m) := by
          rw [ih, pow_succ]
          ring

/-- Bounded remainders imply that a periodic digit tail forces the
actual remainder to repeat after one full period. -/
theorem affine_remainder_repeat_of_eventually_periodic_digits
    (d : ℕ → ℚ) (beta : ℝ) (hbeta : 1 < beta)
    (r : ℕ → ℝ)
    (hbound : ∀ n, 0 ≤ r n ∧ r n ≤ 1)
    (hstep : ∀ n, r (n + 1) = beta * r n - (d n : ℝ))
    (m p : ℕ) (hp : 0 < p)
    (hperiod : ∀ n, m ≤ n → d (n + p) = d n) :
    r m = r (m + p) := by
  let delta : ℝ := r (m + p) - r m
  by_contra hneq
  have hdeltane : delta ≠ 0 := by
    dsimp [delta]
    exact sub_ne_zero.mpr (Ne.symm hneq)
  have hdelta : 0 < |delta| := abs_pos.mpr hdeltane
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / |delta|) hbeta
  have hlarge : 1 < beta ^ n * |delta| :=
    (div_lt_iff₀ hdelta).mp hn
  have hrem := affine_shift_difference d beta r hstep m p hperiod n
  have hleft := hbound (m + p + n)
  have hright := hbound (m + n)
  have hsmall :
      |r (m + p + n) - r (m + n)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hleft.1, hleft.2, hright.1, hright.2]
  rw [hrem, abs_mul, abs_of_pos (pow_pos (by linarith) n)] at hsmall
  exact (not_lt_of_ge hsmall) hlarge

/-- Eventual periodicity of the digits of a bounded affine orbit
forces algebraicity of its base, not merely an assumed repeated state. -/
theorem algebraic_of_eventually_periodic_affine_digits
    (d : ℕ → ℚ) (beta : ℝ) (hbeta : 1 < beta)
    (r : ℕ → ℝ) (hzero : r 0 = 1)
    (hbound : ∀ n, 0 ≤ r n ∧ r n ≤ 1)
    (hstep : ∀ n, r (n + 1) = beta * r n - (d n : ℝ))
    (m p : ℕ) (hp : 0 < p)
    (hperiod : ∀ n, m ≤ n → d (n + p) = d n) :
    IsAlgebraic ℚ beta := by
  have hrepeat :
      r m = r (m + p) :=
    affine_remainder_repeat_of_eventually_periodic_digits
      d beta hbeta r hbound hstep m p hp hperiod
  exact algebraic_of_affine_orbit_repeat d beta r hzero hstep
    m (m + p) (by omega) hrepeat

#print axioms Manuscript14Section11.affine_shift_difference
#print axioms Manuscript14Section11.affine_remainder_repeat_of_eventually_periodic_digits
#print axioms Manuscript14Section11.algebraic_of_eventually_periodic_affine_digits



/-!
## Applying the theorem to the actual greedy beta transformation

All digits below are *the literal integer floors* of beta times
the actual iterated remainders. There is no abstract digit hypothesis.
-/

/-- Every genuine greedy remainder is in the closed unit interval. -/
theorem greedyRemainder_unit_interval (beta : ℝ) (n : ℕ) :
    0 ≤ greedyRemainder beta n ∧ greedyRemainder beta n ≤ 1 := by
  cases n with
  | zero => simp [greedyRemainder]
  | succ n =>
      change 0 ≤ greedyMap beta (greedyRemainder beta n) ∧
        greedyMap beta (greedyRemainder beta n) ≤ 1
      have hnonneg :
          0 ≤ Int.fract (beta * greedyRemainder beta n) :=
        Int.fract_nonneg _
      have hlt :
          Int.fract (beta * greedyRemainder beta n) < 1 :=
        Int.fract_lt_one _
      constructor
      · simpa only [greedyMap, Int.fract] using hnonneg
      · simpa only [greedyMap, Int.fract] using hlt.le

/-- The actual floor-based map satisfies a rational-digit affine
recurrence; the digit is an integer, hence rational. -/
theorem greedyRemainder_affine_step (beta : ℝ) (n : ℕ) :
    greedyRemainder beta (n + 1) =
      beta * greedyRemainder beta n -
        ((((greedyDigit beta n : ℤ) : ℚ) : ℝ)) := by
  simp [greedyRemainder, greedyMap, greedyDigit]

/-- Eventual periodicity of the genuine greedy floor digits forces
algebraicity of the actual beta parameter. -/
theorem algebraic_of_eventually_periodic_greedy_digits
    (beta : ℝ) (hbeta : 1 < beta)
    (m p : ℕ) (hp : 0 < p)
    (hperiod : ∀ n, m ≤ n →
      greedyDigit beta (n + p) = greedyDigit beta n) :
    IsAlgebraic ℚ beta := by
  let d : ℕ → ℚ := fun n => ((greedyDigit beta n : ℤ) : ℚ)
  have hd : ∀ n, m ≤ n → d (n + p) = d n := by
    intro n hn
    dsimp [d]
    exact_mod_cast hperiod n hn
  have hzero : greedyRemainder beta 0 = 1 := rfl
  have hstep : ∀ n,
      greedyRemainder beta (n + 1) =
        beta * greedyRemainder beta n - (d n : ℝ) := by
    intro n
    simpa only [d] using greedyRemainder_affine_step beta n
  exact algebraic_of_eventually_periodic_affine_digits
    d beta hbeta (greedyRemainder beta) hzero
    (greedyRemainder_unit_interval beta) hstep m p hp hd

/-- A transcendental beta in (1,2) cannot have an eventually periodic
greedy digit expansion, even though the digits themselves are integers. -/
theorem greedy_digits_not_eventually_periodic_of_transcendental
    (beta : ℝ) (hbeta : 1 < beta) (htrans : ¬ IsAlgebraic ℚ beta) :
    ¬ ∃ m p : ℕ, 0 < p ∧
      ∀ n, m ≤ n → greedyDigit beta (n + p) = greedyDigit beta n := by
  rintro ⟨m, p, hp, hperiod⟩
  exact htrans (algebraic_of_eventually_periodic_greedy_digits
    beta hbeta m p hp hperiod)

#print axioms Manuscript14Section11.greedyRemainder_unit_interval
#print axioms Manuscript14Section11.greedyRemainder_affine_step
#print axioms Manuscript14Section11.algebraic_of_eventually_periodic_greedy_digits
#print axioms Manuscript14Section11.greedy_digits_not_eventually_periodic_of_transcendental


end Manuscript14Section11
