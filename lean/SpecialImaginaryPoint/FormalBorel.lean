import Mathlib

/-!
# Formal coefficient version of the double Borel differential intertwiner

For a sequence a(n), operatorA and operatorF model, coefficientwise,
  L_A = theta + 1/2 - t(theta + 1)
  L_F = theta(theta + 1/2) - t
where theta=t d/dt. This module proves
  L_F (B^2 a) = theta (B^2 (L_A a)).
This is a formal-series identity, not an analytic convergence theorem.
-/
namespace EulerianSpecialPoint

/-- The coefficientwise double Borel transform divides by (n!)². -/
def doubleBorel (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  a n / ((n.factorial : ℚ) ^ 2)

/-- Coefficients of ((theta + 1/2) - t(theta+1)) A. -/
def operatorA (a : ℕ → ℚ) : ℕ → ℚ
  | 0 => (1/2 : ℚ) * a 0
  | n + 1 => (((n+1 : ℕ) : ℚ) + 1/2) * a (n+1) - ((n+1 : ℕ) : ℚ) * a n

/-- Coefficients of (theta(theta+1/2)-t) F. -/
def operatorF (a : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => ((n+1 : ℕ) : ℚ) * (((n+1 : ℕ) : ℚ) + 1/2) * a (n+1) - a n

/-- Coefficient action of theta=t d/dt. -/
def theta (a : ℕ → ℚ) (n : ℕ) : ℚ := (n : ℚ) * a n

/-- Formal differential intertwiner over Q, at every Taylor coefficient. -/
theorem doubleBorel_intertwines (a : ℕ → ℚ) :
    operatorF (doubleBorel a) = theta (doubleBorel (operatorA a)) := by
  funext n
  cases n with
  | zero => simp [operatorF, theta]
  | succ n =>
      simp only [operatorF, doubleBorel, operatorA, theta]
      have hn : (n.factorial : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.factorial_pos n))
      have hn1 : (((n + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
      rw [Nat.factorial_succ]
      push_cast
      field_simp


/-- The exact reciprocal-central-binomial input coefficients
of manuscript Proposition 3.1, after expansion of the binomial. -/
def binomialInputCoefficient (n : ℕ) : ℚ :=
  4 ^ n * (n.factorial : ℚ) ^ 2 / ((2 * n + 1).factorial : ℚ)

/-- The entire-function coefficients appearing in manuscript Theorem 3.3. -/
def eulerianBorelCoefficient (n : ℕ) : ℚ :=
  4 ^ n / ((2 * n + 1).factorial : ℚ)

/-- Exact coefficient equality under double Borel: no approximation and
no unproved analytic convergence assumption is involved. -/
theorem doubleBorel_binomialInput_coefficients (n : ℕ) :
    doubleBorel binomialInputCoefficient n = eulerianBorelCoefficient n := by
  simp only [doubleBorel, binomialInputCoefficient, eulerianBorelCoefficient]
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have hm : ((2 * n + 1).factorial : ℚ) ≠ 0 := by positivity
  field_simp

#print axioms EulerianSpecialPoint.doubleBorel_binomialInput_coefficients

#print axioms EulerianSpecialPoint.doubleBorel_intertwines
end EulerianSpecialPoint
