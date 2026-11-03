import Mathlib

/-!
# The double-Borel differential intertwiner over complex coefficients

This is the coefficientwise form of the manuscript's Theorem 3.5
over ℂ[[t]]. The type `ℕ → ℂ` is the complete coefficient
representation of a formal series. Analytic convergence is not
assumed or claimed by this theorem.

  L_A = θ + 1/2 - t(θ+1)
  L_F = θ(θ+1/2) - t
  L_F ∘ B² = θ ∘ B² ∘ L_A

The identical rational-coefficient statement is proved separately
in `FormalBorel.lean`.
-/

namespace EulerianSpecialPoint

def doubleBorelComplex (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n / ((n.factorial : ℂ) ^ 2)

def operatorAComplex (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => (1 / 2 : ℂ) * a 0
  | n + 1 => (((n + 1 : ℕ) : ℂ) + 1 / 2) * a (n + 1)
      - ((n + 1 : ℕ) : ℂ) * a n

def operatorFComplex (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => ((n + 1 : ℕ) : ℂ)
      * (((n + 1 : ℕ) : ℂ) + 1 / 2) * a (n + 1) - a n

def thetaComplex (a : ℕ → ℂ) (n : ℕ) : ℂ := (n : ℂ) * a n

/-- The exact complex-coefficient form of the manuscript's double-Borel
differential intertwining identity; valid for *every* formal input. -/
theorem doubleBorel_intertwines_complex (a : ℕ → ℂ) :
    operatorFComplex (doubleBorelComplex a) =
      thetaComplex (doubleBorelComplex (operatorAComplex a)) := by
  funext n
  cases n with
  | zero => simp [operatorFComplex, thetaComplex]
  | succ n =>
      simp only [operatorFComplex, doubleBorelComplex, operatorAComplex,
        thetaComplex]
      have hn : (n.factorial : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.factorial_pos n))
      have hn1 : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by positivity
      rw [Nat.factorial_succ]
      push_cast
      field_simp

#print axioms EulerianSpecialPoint.doubleBorel_intertwines_complex

end EulerianSpecialPoint
