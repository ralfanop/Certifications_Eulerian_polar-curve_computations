import Mathlib

/-!
# Manuscript 14.1 §7 — finite Dirichlet spectral determinants

The n-th Dirichlet eigenvalue on (0,1) is π²(n+1)².
This module verifies finite-dimensional determinant identities and
monotonicity of the Euler-product truncations. It does NOT claim the
infinite Fredholm/zeta determinant identity or trace-class convergence.
The actual infinite-dimensional operator remains a separate obligation.
-/

namespace Manuscript14Dirichlet

/-- The n-th eigenvalue factor of I + t A⁻¹, indexed from zero. -/
noncomputable def factor (n : ℕ) (t : ℝ) : ℝ :=
  1 + t / (Real.pi ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 2))

/-- The determinant of the first N diagonal spectral factors. -/
noncomputable def finiteFredholm (N : ℕ) (t : ℝ) : ℝ :=
  ∏ n ∈ Finset.range N, factor n t

/-- The corresponding concrete N×N real diagonal matrix. -/
noncomputable def finiteDiagonal (N : ℕ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => factor i.val t)

/-- Matrix determinant equals the finite product of actual spectral factors. -/
theorem finiteDiagonal_det (N : ℕ) (t : ℝ) :
    Matrix.det (finiteDiagonal N t) =
      ∏ i : Fin N, factor i.val t := by
  simp only [finiteDiagonal, Matrix.det_diagonal]

theorem factor_ge_one (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    1 ≤ factor n t := by
  have h : 0 ≤ t / (Real.pi ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    positivity
  unfold factor
  linarith

theorem factor_pos (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 < factor n t :=
  lt_of_lt_of_le (by norm_num) (factor_ge_one n t ht)

/-- Each finite truncation is strictly positive for nonnegative shifts. -/
theorem finiteFredholm_pos (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 < finiteFredholm N t := by
  unfold finiteFredholm
  apply Finset.prod_pos
  intro n hn
  exact factor_pos n t ht

/-- Exact finite Euler-product recurrence. -/
theorem finiteFredholm_succ (N : ℕ) (t : ℝ) :
    finiteFredholm (N + 1) t = finiteFredholm N t * factor N t := by
  simp only [finiteFredholm, Finset.prod_range_succ]

/-- Positivity implies monotonicity of the finite Fredholm truncations. -/
theorem finiteFredholm_mono_step (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    finiteFredholm N t ≤ finiteFredholm (N + 1) t := by
  rw [finiteFredholm_succ]
  calc
    finiteFredholm N t = finiteFredholm N t * 1 := by ring
    _ ≤ finiteFredholm N t * factor N t :=
      mul_le_mul_of_nonneg_left (factor_ge_one N t ht)
        (le_of_lt (finiteFredholm_pos N t ht))

theorem finiteFredholm_ge_one (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    1 ≤ finiteFredholm N t := by
  induction N with
  | zero => simp [finiteFredholm]
  | succ N ih => exact le_trans ih (finiteFredholm_mono_step N t ht)

theorem finiteFredholm_zero (N : ℕ) :
    finiteFredholm N 0 = 1 := by
  simp [finiteFredholm, factor]

#print axioms Manuscript14Dirichlet.finiteDiagonal_det
#print axioms Manuscript14Dirichlet.factor_ge_one
#print axioms Manuscript14Dirichlet.finiteFredholm_pos
#print axioms Manuscript14Dirichlet.finiteFredholm_succ
#print axioms Manuscript14Dirichlet.finiteFredholm_mono_step
#print axioms Manuscript14Dirichlet.finiteFredholm_ge_one
#print axioms Manuscript14Dirichlet.finiteFredholm_zero

end Manuscript14Dirichlet
