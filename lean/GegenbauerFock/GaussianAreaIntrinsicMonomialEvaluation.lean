import GegenbauerFock.GaussianAreaIntrinsicEntireEvaluation

/-!
# V007 — intrinsic Gaussian-Fock point evaluation on normalized monomials

The intrinsic entire-representative evaluation agrees at every point
with the explicitly normalized monomials in the genuine Gaussian L²
space. The family of point evaluations separates all intrinsic entire
classes. These are algebraic/analytic prerequisites, not continuity of
evaluation or density of polynomials.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The genuine normalized Gaussian L² monomial as an element of
the independently defined intrinsic entire submodule. -/
noncomputable def normalizedMonomialIntrinsicVector
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    entireGaussianL2Submodule alpha :=
  ⟨normalizedMonomialL2Vector alpha ha n,
    normalizedMonomialL2Vector_mem_entireGaussianL2Submodule alpha ha n⟩

/-- The canonical entire representative of the genuine L² monomial
is precisely its original normalized polynomial, everywhere. -/
theorem entireRepresentative_normalizedMonomialIntrinsicVector
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    entireRepresentative alpha (normalizedMonomialIntrinsicVector alpha ha n) =
      normalizedMonomial alpha n := by
  apply entireGaussianRepresentative_unique alpha ha
    (normalizedMonomialL2Vector alpha ha n)
  · exact entireRepresentative_differentiable alpha
      (normalizedMonomialIntrinsicVector alpha ha n)
  · exact normalizedMonomial_differentiable alpha n
  · exact entireRepresentative_ae alpha
      (normalizedMonomialIntrinsicVector alpha ha n)
  · exact (normalizedMonomialL2Vector_ae alpha ha n).symm

/-- The intrinsic point evaluation recovers the exact factorial
normalized holomorphic monomial at every complex point. -/
theorem intrinsicEntireEvaluation_normalizedMonomial
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) (z : ℂ) :
    intrinsicEntireEvaluation alpha ha z
      (normalizedMonomialIntrinsicVector alpha ha n) =
        normalizedMonomial alpha n z := by
  exact congrFun
    (entireRepresentative_normalizedMonomialIntrinsicVector alpha ha n) z

/-- If two intrinsic Gaussian entire classes agree under all
point evaluations, then they are equal in genuine Gaussian L². -/
theorem intrinsicEntireEvaluation_separates
    (alpha : ℝ) (ha : 0 < alpha)
    {x y : entireGaussianL2Submodule alpha}
    (h : ∀ z : ℂ, intrinsicEntireEvaluation alpha ha z x =
      intrinsicEntireEvaluation alpha ha z y) : x = y := by
  apply entireRepresentative_injective alpha
  funext z
  exact h z

#print axioms GegenbauerFock.GaussianArea.entireRepresentative_normalizedMonomialIntrinsicVector
#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluation_normalizedMonomial
#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluation_separates

end GegenbauerFock.GaussianArea
