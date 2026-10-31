/-
# Definition 2.1 of the V001 manuscript: the sine integral and its series (real argument)

`Si x = ∫₀ˣ sinc` (module `FourierModes`).  Proved here, for real `x`:
* the Maclaurin series `Si x = ∑ (−1)^k x^{2k+1} / ((2k+1)·(2k+1)!)`;
* the middle form of Eq. (4): `(2k+1)·(2k+1)! = (2k+1)² (k!)² C(2k,k)`, i.e.
  `Si x = ∑ (−1)^k x^{2k+1} / ((2k+1)² (k!)² C(2k,k))`
  (a reciprocal central binomial sum);
* the hypergeometric form of Eq. (4): `Si x = x · ₁F₂(½; 3/2, 3/2; −x²/4)`, the argument being
  `z₀² x²/2` with `z₀² = (i/√2)² = −1/2`; the ₁F₂ coefficients are written with Pochhammer
  symbols `(a)_k = ascPochhammer`.
The extension to complex `z` (Si entire) is not formalised.
-/
import EulerianCert.FourierModes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.RingTheory.Polynomial.Pochhammer

open Real Nat intervalIntegral MeasureTheory
open EulerianCert.FourierModes

noncomputable section

namespace EulerianCert.SineIntegral

/-- Maclaurin series of `sinc`. -/
lemma hasSum_sinc (t : ℝ) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * t ^ (2 * n) / ((2 * n + 1)! : ℝ)) (sinc t) := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [sinc_zero]
    convert hasSum_single (f := fun n : ℕ => (-1 : ℝ) ^ n * (0 : ℝ) ^ (2 * n) / ((2 * n + 1)! : ℝ))
      0 (fun n hn => by simp [zero_pow (by omega : 2 * n ≠ 0)]) using 1
    simp
  · rw [sinc_of_ne_zero ht]
    have := (Real.hasSum_sin t).div_const t
    convert this using 1
    ext n
    rw [pow_succ]
    field_simp

/-- The Maclaurin series of `Si` (termwise integration of `hasSum_sinc`). -/
theorem hasSum_Si (x : ℝ) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * x ^ (2 * n + 1) / ((2 * n + 1 : ℝ) * ((2 * n + 1)! : ℝ)))
      (Si x) := by
  unfold Si
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0)
    (b := x) (F := fun n (t : ℝ) => (-1 : ℝ) ^ n * t ^ (2 * n) / ((2 * n + 1)! : ℝ)) (f := sinc)
    (fun n _ => |x| ^ (2 * n) / ((2 * n)! : ℝ))
    (fun n => (by fun_prop : Continuous fun t : ℝ => (-1 : ℝ) ^ n * t ^ (2 * n) /
      ((2 * n + 1)! : ℝ)).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (fun t ht => by
      have ht' : |t| ≤ |x| := by
        rcases le_total 0 x with h | h
        · rw [Set.uIoc_of_le h] at ht
          rw [abs_of_pos (by linarith [ht.1]), abs_of_nonneg h]; exact ht.2
        · rw [Set.uIoc_of_ge h] at ht
          rw [abs_of_nonpos ht.2, abs_of_nonpos h]; linarith [ht.1]
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_pow, Nat.abs_cast]
      apply div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg _) ht' _)
        (by positivity)
      exact_mod_cast Nat.factorial_le (by omega)))
    (Filter.Eventually.of_forall (fun _ _ => by
      have h := Real.summable_pow_div_factorial |x|
      exact h.comp_injective (fun a b hab => by simpa using hab)))
    (by
      apply Continuous.intervalIntegrable
      exact continuous_const)
    (Filter.Eventually.of_forall (fun t _ => hasSum_sinc t))
  convert key using 1
  ext n
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  field_simp
  ring

/-- `(2k+1)·(2k+1)! = (2k+1)² (k!)² C(2k,k)`. -/
lemma odd_factorial_identity (k : ℕ) :
    ((2 * k + 1 : ℝ) * ((2 * k + 1)! : ℝ)) =
      (2 * k + 1 : ℝ) ^ 2 * ((k ! : ℝ)) ^ 2 * ((2 * k).choose k : ℝ) := by
  have h1 : (2 * k + 1)! = (2 * k + 1) * (2 * k)! := Nat.factorial_succ _
  have h2 : (2 * k).choose k * k ! * k ! = (2 * k)! := by
    have := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    rwa [show 2 * k - k = k by omega] at this
  rw [h1, ← h2]
  push_cast
  ring

/-- **Definition 2.1, Eq. (4), middle form**: the reciprocal central binomial series. -/
theorem hasSum_Si_binomial (x : ℝ) :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k * x ^ (2 * k + 1) /
      ((2 * k + 1 : ℝ) ^ 2 * ((k ! : ℝ)) ^ 2 * ((2 * k).choose k : ℝ))) (Si x) := by
  convert hasSum_Si x using 2 with k
  rw [odd_factorial_identity]

/-! ### The hypergeometric form -/

lemma poch_ratio (k : ℕ) :
    (ascPochhammer ℝ k).eval (1 / 2 : ℝ) / (ascPochhammer ℝ k).eval (3 / 2 : ℝ) =
      1 / (2 * k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
    have hp : (ascPochhammer ℝ k).eval (3 / 2 : ℝ) ≠ 0 := by
      have := ascPochhammer_pos k (3 / 2 : ℝ) (by norm_num)
      exact this.ne'
    rw [mul_div_mul_comm, ih]
    push_cast
    field_simp
    ring

lemma poch_three_halves (k : ℕ) :
    (ascPochhammer ℝ k).eval (3 / 2 : ℝ) = ((2 * k + 1)! : ℝ) / (4 ^ k * (k ! : ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ih]
    have hf : ((2 * (k + 1) + 1)! : ℝ) = (2 * k + 3) * (2 * k + 2) * ((2 * k + 1)! : ℝ) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by ring, Nat.factorial_succ,
        Nat.factorial_succ]
      push_cast; ring
    have hk : (((k + 1)! : ℕ) : ℝ) = (k + 1) * (k ! : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hf, hk]
    have : ((2 * k + 1)! : ℝ) ≠ 0 := by positivity
    have : ((k ! : ℝ)) ≠ 0 := by positivity
    field_simp
    ring

/-- The ₁F₂(½; 3/2, 3/2; w) coefficient. -/
def coef (k : ℕ) : ℝ :=
  (ascPochhammer ℝ k).eval (1 / 2 : ℝ) /
    ((ascPochhammer ℝ k).eval (3 / 2 : ℝ) * (ascPochhammer ℝ k).eval (3 / 2 : ℝ) * (k ! : ℝ))

/-- **Definition 2.1, Eq. (4), hypergeometric form**: `Si x = x · ₁F₂(½; 3/2, 3/2; −x²/4)`. -/
theorem hasSum_Si_hypergeometric (x : ℝ) :
    HasSum (fun k : ℕ => x * (coef k * (-(x ^ 2) / 4) ^ k)) (Si x) := by
  convert hasSum_Si x using 1
  ext k
  have h1 : coef k = 1 / (2 * k + 1) * (4 ^ k * (k ! : ℝ) / ((2 * k + 1)! : ℝ)) / (k ! : ℝ) := by
    rw [coef, ← poch_ratio k, poch_three_halves k]
    have : ((2 * k + 1)! : ℝ) ≠ 0 := by positivity
    have : ((k ! : ℝ)) ≠ 0 := by positivity
    field_simp
  rw [h1, div_pow, neg_pow, ← pow_mul]
  have : ((2 * k + 1)! : ℝ) ≠ 0 := by positivity
  have : ((k ! : ℝ)) ≠ 0 := by positivity
  field_simp
  ring

end EulerianCert.SineIntegral
