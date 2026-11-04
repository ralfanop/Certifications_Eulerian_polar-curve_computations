import Mathlib

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
def affineOrbitPolynomial (d : ℕ → ℚ) : ℕ → Polynomial ℚ
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
            norm_num
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
      ring

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

end Manuscript14Section11
