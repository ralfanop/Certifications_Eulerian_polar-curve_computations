import GegenbauerFock.KummerCoefficients
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# V007: Kummer recurrence equals the genuine Mathlib Pochhammer quotient

This establishes the precise rising-factorial coefficient identity,
not merely the definition of a formally similar recursive sequence.
The further identification with integrals of the ultraspherical
Beta-pushforward law remains an independent analytic theorem.
-/

namespace GegenbauerFock.KummerCoefficients

open Polynomial

/-- The denominator (λ+1)_n is strictly positive for λ>0. -/
theorem denominatorPochhammer_pos (lam : ℝ) (hlam : 0 < lam)
    (n : ℕ) :
    0 < (ascPochhammer ℝ n).eval (lam + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_eval]
      exact mul_pos ih (by positivity)

/-- The numerator (1/2)_n is strictly positive. -/
theorem numeratorPochhammer_pos (n : ℕ) :
    0 < (ascPochhammer ℝ n).eval (1 / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_eval]
      exact mul_pos ih (by positivity)

/-- Our Kummer series uses exactly (1/2)_n / (λ+1)_n,
with Mathlib's Pochhammer convention (not a shifted or regularized coefficient). -/
theorem ratio_eq_pochhammer (lam : ℝ) (hlam : 0 < lam)
    (n : ℕ) :
    ratio lam n =
      (ascPochhammer ℝ n).eval (1 / 2) /
        (ascPochhammer ℝ n).eval (lam + 1) := by
  induction n with
  | zero =>
      simp [ratio]
  | succ n ih =>
      rw [ratio_succ, ih, ascPochhammer_succ_eval, ascPochhammer_succ_eval]
      have hd : (ascPochhammer ℝ n).eval (lam + 1) ≠ 0 :=
        ne_of_gt (denominatorPochhammer_pos lam hlam n)
      have hn : (n : ℝ) + lam + 1 ≠ 0 := by positivity
      have hs : lam + 1 + (n : ℝ) ≠ 0 := by positivity
      field_simp
      ring

#print axioms GegenbauerFock.KummerCoefficients.denominatorPochhammer_pos
#print axioms GegenbauerFock.KummerCoefficients.numeratorPochhammer_pos
#print axioms GegenbauerFock.KummerCoefficients.ratio_eq_pochhammer

end GegenbauerFock.KummerCoefficients
