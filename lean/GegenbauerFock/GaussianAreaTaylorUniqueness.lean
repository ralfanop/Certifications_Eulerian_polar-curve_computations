import GegenbauerFock.GaussianAreaReproducingCriterion
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# V007 — Taylor uniqueness for intrinsic entire Gaussian vectors

A genuinely entire function is uniquely determined by its complete
sequence of complex derivatives at zero, by the global complex Taylor
series theorem. For the independently defined intrinsic Gaussian L²
submodule this is an unconditional analytic uniqueness statement.

We then identify the exact remaining moment-extraction obligation:
full intrinsic polynomial density is equivalent to the implication
that vanishing Gaussian monomial moments forces all derivatives of
the entire representative at zero to vanish. The latter implication
is NOT asserted without proof; in particular no onto Fock isometry
is claimed by this module.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Global Taylor uniqueness for an entire complex function. -/
theorem entireFunction_eq_zero_of_iteratedDeriv_zero
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h : ∀ n : ℕ, iteratedDeriv n f 0 = 0) :
    f = 0 := by
  funext z
  have hs := Complex.taylorSeries_eq_of_entire' hf 0 z
  simpa [h] using hs.symm

/-- The canonical entire representative of the zero Gaussian L²
class is the identically zero function, not merely zero a.e. -/
theorem entireRepresentative_zero
    (alpha : ℝ) (ha : 0 < alpha) :
    entireRepresentative alpha
      (0 : entireGaussianL2Submodule alpha) = 0 := by
  have h := entireRepresentative_smul alpha ha (0 : ℂ)
    (0 : entireGaussianL2Submodule alpha)
  simpa using h

/-- A Gaussian L² class with an entire representative is zero if and
only if all complex Taylor derivatives of that representative at
the origin vanish. This uses the global Taylor theorem and genuine
Gaussian a.e. identification, not polynomial density. -/
theorem intrinsicGaussian_zero_iff_taylor_derivs_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    x = 0 ↔
      ∀ n : ℕ, iteratedDeriv n (entireRepresentative alpha x) 0 = 0 := by
  constructor
  · intro hx
    subst x
    intro n
    simp [entireRepresentative_zero alpha ha, iteratedDeriv_const_zero]
  · intro hder
    have hfun : entireRepresentative alpha x = 0 :=
      entireFunction_eq_zero_of_iteratedDeriv_zero
        (entireRepresentative alpha x)
        (entireRepresentative_differentiable alpha x) hder
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [entireRepresentative_ae alpha x,
      Lp.coeFn_zero ℂ 2 (gaussianAreaMeasure alpha)] with z hz hzero
    calc
      ((x : Lp ℂ 2 (gaussianAreaMeasure alpha)) : ℂ → ℂ) z =
          entireRepresentative alpha x z := hz.symm
      _ = 0 := by rw [hfun]; rfl
      _ = ((0 : Lp ℂ 2 (gaussianAreaMeasure alpha)) : ℂ → ℂ) z :=
        hzero.symm

/-- The exact outstanding analytic obligation is to derive vanishing
Taylor derivatives from vanishing Gaussian monomial moments. The
equivalence is unconditional, but it does not prove that implication. -/
theorem intrinsicEntire_le_polynomialClosure_iff_moments_force_taylor_zero
    (alpha : ℝ) (ha : 0 < alpha) :
    entireGaussianL2Submodule alpha ≤ gaussianPolynomialClosure alpha ha ↔
      ∀ x : entireGaussianL2Submodule alpha,
        (∀ n : ℕ,
          inner ℂ (normalizedMonomialL2Vector alpha ha n)
            (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) = 0) →
        (∀ n : ℕ,
          iteratedDeriv n (entireRepresentative alpha x) 0 = 0) := by
  constructor
  · intro h x hm
    have hu := (intrinsicEntire_le_polynomialClosure_iff_moment_unique
      alpha ha).1 h
    have hxzero : (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) = 0 :=
      hu (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) x.property hm
    have hx : x = 0 := Subtype.ext hxzero
    exact (intrinsicGaussian_zero_iff_taylor_derivs_zero alpha ha x).1 hx
  · intro h
    apply (intrinsicEntire_le_polynomialClosure_iff_moment_unique alpha ha).2
    intro x hx hm
    let y : entireGaussianL2Submodule alpha := ⟨x, hx⟩
    have hder : ∀ n : ℕ,
        iteratedDeriv n (entireRepresentative alpha y) 0 = 0 :=
      h y hm
    have hy : y = 0 :=
      (intrinsicGaussian_zero_iff_taylor_derivs_zero alpha ha y).2 hder
    exact congrArg
      (fun v : entireGaussianL2Submodule alpha =>
        (v : Lp ℂ 2 (gaussianAreaMeasure alpha))) hy

#print axioms GegenbauerFock.GaussianArea.entireFunction_eq_zero_of_iteratedDeriv_zero
#print axioms GegenbauerFock.GaussianArea.entireRepresentative_zero
#print axioms GegenbauerFock.GaussianArea.intrinsicGaussian_zero_iff_taylor_derivs_zero
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_le_polynomialClosure_iff_moments_force_taylor_zero

end GegenbauerFock.GaussianArea
