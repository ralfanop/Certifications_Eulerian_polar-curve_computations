import GegenbauerFock.GaussianAreaActualL2Vectors
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# V007 — actual Gaussian weighted L² inner product of monomial vectors

This bridge replaces scalar Lebesgue Gaussian Gram integrals with
the actual inner product in the completed Hilbert L² space associated
to the normalized positive Gaussian measure. It proves that the
previously constructed normalized monomial vectors form a genuine
orthonormal family in L²(μ_α).

This does not assert that holomorphic polynomials span every
holomorphic weighted L² function or that the coefficient-to-function
Bargmann–Fock map is already surjective.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Exact change of Gaussian weighted integration into its planar
Lebesgue-density expression, for any complex-valued function. -/
theorem integral_gaussianArea_eq_integral_density
    (alpha : ℝ) (ha : 0 < alpha) (f : ℂ → ℂ) :
    (∫ z : ℂ, f z ∂gaussianAreaMeasure alpha) =
      (∫ z : ℂ,
        ((alpha / Real.pi : ℝ) : ℂ) *
          (f z * (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ))) := by
  have hmeas :
      Measurable (fun z : ℂ => ENNReal.ofReal
        ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2))) := by
    fun_prop
  have hfinite : ∀ᵐ z : ℂ ∂(volume : Measure ℂ),
      ENNReal.ofReal ((alpha / Real.pi) *
        Real.exp (-alpha * ‖z‖ ^ 2)) < ⊤ := by
    filter_upwards [] with z
    simp
  unfold gaussianAreaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hfinite]
  apply integral_congr_ae
  filter_upwards [] with z
  have hpositive : 0 ≤ (alpha / Real.pi) *
      Real.exp (-alpha * ‖z‖ ^ 2) := by
    positivity
  rw [ENNReal.toReal_ofReal hpositive, Complex.real_smul]
  push_cast
  ring

/-- Actual weighted Gaussian monomial integral on the complex plane.
These are genuine integrals with respect to μ_α, not formal Gram data. -/
theorem integral_gaussianArea_normalizedMonomial_pair_delta
    (alpha : ℝ) (ha : 0 < alpha) (m n : ℕ) :
    (∫ z : ℂ,
      normalizedMonomial alpha m z *
        star (normalizedMonomial alpha n z)
      ∂gaussianAreaMeasure alpha) =
      if m = n then (1 : ℂ) else 0 := by
  rw [integral_gaussianArea_eq_integral_density alpha ha]
  exact integral_normalized_monomial_pair_delta alpha ha m n

/-- The actual L² vectors of normalized holomorphic monomials
have the Kronecker-delta inner products in the completed Hilbert space. -/
theorem inner_normalizedMonomialL2Vector_delta
    (alpha : ℝ) (ha : 0 < alpha) (m n : ℕ) :
    inner ℂ
      (normalizedMonomialL2Vector alpha ha m)
      (normalizedMonomialL2Vector alpha ha n) =
      if m = n then (1 : ℂ) else 0 := by
  rw [L2.inner_def]
  calc
    (∫ z : ℂ,
      inner ℂ ((normalizedMonomialL2Vector alpha ha m) z)
        ((normalizedMonomialL2Vector alpha ha n) z)
      ∂gaussianAreaMeasure alpha) =
    (∫ z : ℂ,
      normalizedMonomial alpha n z *
        star (normalizedMonomial alpha m z)
      ∂gaussianAreaMeasure alpha) := by
        apply integral_congr_ae
        filter_upwards
          [normalizedMonomialL2Vector_ae alpha ha m,
           normalizedMonomialL2Vector_ae alpha ha n] with z hm hn
        rw [hm, hn]
        simp only [RCLike.inner_apply', Complex.star_def]
        ring
    _ = if n = m then (1 : ℂ) else 0 :=
      integral_gaussianArea_normalizedMonomial_pair_delta alpha ha n m
    _ = if m = n then (1 : ℂ) else 0 := by
      rw [eq_comm]

#print axioms GegenbauerFock.GaussianArea.integral_gaussianArea_eq_integral_density
#print axioms GegenbauerFock.GaussianArea.integral_gaussianArea_normalizedMonomial_pair_delta
#print axioms GegenbauerFock.GaussianArea.inner_normalizedMonomialL2Vector_delta

end GegenbauerFock.GaussianArea
