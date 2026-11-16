import Mathlib

/-!
Manuscript 16 v16.5, Section 14, Theorem 14.3.
Authoritative ZIP SHA-256:
4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e.
Finite generating-function identity with exact tail; neither infinite trace
nor operator realization nor Wasserstein theorem is assumed or claimed.
-/
namespace Manuscript16.V165

open scoped BigOperators

def resonanceWeight (n : ℕ) : ℝ := 4 * ((n : ℝ) + 1) * ((n : ℝ) + 3)

def tailPoly (n : ℕ) (q : ℝ) : ℝ :=
  4 * (((n : ℝ) + 1) * ((n : ℝ) + 3)
    - (2 * (n : ℝ)^2 + 6 * (n : ℝ) + 1) * q
    + (n : ℝ) * ((n : ℝ) + 2) * q^2)

theorem resonance_weight_energy (n : ℕ) :
    resonanceWeight n = (2 * (n : ℝ) + 1)^2 + 6 * (2 * (n : ℝ) + 1) + 5 := by
  unfold resonanceWeight
  ring

theorem tailPoly_step (n : ℕ) (q : ℝ) :
    tailPoly n q - q * tailPoly (n + 1) q =
      (1 - q)^3 * resonanceWeight n := by
  unfold tailPoly resonanceWeight
  push_cast
  ring

/-- The exact finite version of the rational generating function,
with the full polynomial-geometric remainder retained. -/
theorem finite_resonance_generating (N : ℕ) (q : ℝ) :
    (1 - q)^3 * (∑ n ∈ Finset.range N, resonanceWeight n * q^n) =
      4 * (3 - q) - q^N * tailPoly N q := by
  induction N with
  | zero =>
    simp [tailPoly] <;> ring
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    unfold tailPoly resonanceWeight
    push_cast
    ring

#print axioms Manuscript16.V165.resonance_weight_energy
#print axioms Manuscript16.V165.tailPoly_step
#print axioms Manuscript16.V165.finite_resonance_generating

end Manuscript16.V165
