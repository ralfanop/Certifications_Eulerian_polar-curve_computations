import GegenbauerFock.GaussianAreaWeightedMonomialL2
import GegenbauerFock.GaussianAreaNormalizedBasis

/-!
# V007 — actual L² vectors for Gaussian holomorphic monomials

For α>0 the Gaussian measure is explicitly realized as a density
against planar Lebesgue area and the complex monomials are provably
in L² of that measure. This module constructs actual elements of
the Hilbert L² space, including factorial-normalized monomials.

These are genuine completed-space Lp elements, not formal scalar
Gram entries. Density of polynomials in the holomorphic Fock
subspace, an isometry of completed Hilbert spaces, and onto
surjectivity remain separate obligations.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The unnormalized holomorphic monomial as an actual
vector in the Gaussian weighted complex L² space. -/
noncomputable def monomialL2Vector
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    Lp ℂ 2 (gaussianAreaMeasure alpha) :=
  MemLp.toLp (fun z : ℂ => z ^ n)
    (monomial_memLp_two_gaussianArea alpha ha n)

/-- The L²-vector represents the original holomorphic monomial
outside a Gaussian-null set. -/
theorem monomialL2Vector_ae
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    (monomialL2Vector alpha ha n : ℂ → ℂ)
      =ᵐ[gaussianAreaMeasure alpha] (fun z : ℂ => z ^ n) := by
  exact MemLp.coeFn_toLp (monomial_memLp_two_gaussianArea alpha ha n)

/-- Factorial-normalized monomials are still members of
Gaussian L², by multiplication with their exact scalar weights. -/
theorem normalizedMonomial_memLp_two
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    MemLp (normalizedMonomial alpha n) 2 (gaussianAreaMeasure alpha) := by
  change MemLp (fun z : ℂ => monomialWeight alpha n * z ^ n)
    2 (gaussianAreaMeasure alpha)
  exact (monomial_memLp_two_gaussianArea alpha ha n).const_mul
    (monomialWeight alpha n)

/-- The factorial-normalized monomial as an actual completed
weighted Gaussian L² vector. -/
noncomputable def normalizedMonomialL2Vector
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    Lp ℂ 2 (gaussianAreaMeasure alpha) :=
  MemLp.toLp (normalizedMonomial alpha n)
    (normalizedMonomial_memLp_two alpha ha n)

/-- The normalized L²-vector still agrees a.e. with its
entire complex monomial representative. -/
theorem normalizedMonomialL2Vector_ae
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    (normalizedMonomialL2Vector alpha ha n : ℂ → ℂ)
      =ᵐ[gaussianAreaMeasure alpha] (normalizedMonomial alpha n) := by
  exact MemLp.coeFn_toLp (normalizedMonomial_memLp_two alpha ha n)

#print axioms GegenbauerFock.GaussianArea.monomialL2Vector_ae
#print axioms GegenbauerFock.GaussianArea.normalizedMonomial_memLp_two
#print axioms GegenbauerFock.GaussianArea.normalizedMonomialL2Vector_ae

end GegenbauerFock.GaussianArea
