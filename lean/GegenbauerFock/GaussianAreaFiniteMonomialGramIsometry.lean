import GegenbauerFock.GaussianAreaNormalizedBasis

/-!
# V007 — finite Gram isometry of normalized Gaussian holomorphic monomials

The exact normalized complex-plane Gaussian mixed-monomial integrals
from the pinned Mathlib-certified development form an identity Gram
matrix. Hence, for every FINITE family, the sesquilinear Gram
quadratic form is exactly the ordinary ℓ² coefficient pairing.

This is a finite-degree isometry at the level of genuinely computed
Gaussian-area Gram entries. It does NOT yet identify the completion
of holomorphic polynomials with the full Gaussian holomorphic L²
space or assert the surjectivity of the Bargmann–Fock extension.
-/

noncomputable section
open MeasureTheory
namespace GegenbauerFock.GaussianArea

/-- Finite normalized polynomial Gram pairing, using ACTUAL Gaussian
area integrals of normalized complex monomials on the plane. -/
noncomputable def finiteMonomialGramPair
    (alpha : ℝ) (s : Finset ℕ) (a b : ℕ → ℂ) : ℂ :=
  ∑ m ∈ s, ∑ n ∈ s,
    a m * star (b n) *
      (∫ z : ℂ,
        ((alpha / Real.pi : ℝ) : ℂ) *
          (normalizedMonomial alpha m z *
            star (normalizedMonomial alpha n z) *
            (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ)))

/-- Exact finite sesquilinear Gaussian Gram identity:
the normalized monomial system has the coefficient ℓ² Gram form. -/
theorem finiteMonomialGramPair_eq_coefficients
    (alpha : ℝ) (ha : 0 < alpha)
    (s : Finset ℕ) (a b : ℕ → ℂ) :
    finiteMonomialGramPair alpha s a b =
      ∑ n ∈ s, a n * star (b n) := by
  classical
  unfold finiteMonomialGramPair
  simp_rw [integral_normalized_monomial_pair_delta alpha ha]
  simp only [mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq']

/-- In particular, every finite Gaussian normalized-monomial Gram
quadratic form is the exact squared coefficient norm, in ℂ. -/
theorem finiteMonomialGramPair_diagonal
    (alpha : ℝ) (ha : 0 < alpha)
    (s : Finset ℕ) (a : ℕ → ℂ) :
    finiteMonomialGramPair alpha s a a =
      ∑ n ∈ s, ((‖a n‖ ^ 2 : ℝ) : ℂ) := by
  rw [finiteMonomialGramPair_eq_coefficients alpha ha]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

#print axioms GegenbauerFock.GaussianArea.finiteMonomialGramPair_eq_coefficients
#print axioms GegenbauerFock.GaussianArea.finiteMonomialGramPair_diagonal

end GegenbauerFock.GaussianArea
