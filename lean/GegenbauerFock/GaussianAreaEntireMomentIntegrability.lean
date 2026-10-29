import GegenbauerFock.GaussianAreaPolarFubini
import GegenbauerFock.GaussianAreaIntrinsicEntireEvaluation
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# V007 — Gaussian L² representatives have genuine integrable mixed moments

The first analytic bridge toward polynomial density is the weighted
Cauchy–Schwarz (Hölder) integrability of the product of an arbitrary
Gaussian L² vector with a conjugate monomial. In particular, this
applies to the canonical entire representative of any intrinsic Fock
vector. No polar Fubini interchange or density assertion is used here.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Complex-conjugate monomials belong to the genuine Gaussian L² space. -/
theorem conjugate_monomial_memLp_two_gaussianArea
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    MemLp (fun z : ℂ => star (z ^ n)) 2 (gaussianAreaMeasure alpha) := by
  apply (monomial_memLp_two_gaussianArea alpha ha n).congr_norm
  · fun_prop
  · filter_upwards [] with z
    simp only [norm_star]

/-- Hölder's inequality makes every conjugate-monomial moment of an
arbitrary Gaussian L² vector absolutely integrable with respect to
the actual normalized Gaussian area measure. -/
theorem gaussianL2_conjugate_monomial_integrable
    (alpha : ℝ) (ha : 0 < alpha)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) (n : ℕ) :
    Integrable (fun z : ℂ => (x : ℂ → ℂ) z * star (z ^ n))
      (gaussianAreaMeasure alpha) := by
  exact MemLp.integrable_mul (p := 2) (q := 2)
    (Lp.memLp x)
    (conjugate_monomial_memLp_two_gaussianArea alpha ha n)

/-- The canonical entire representative inherits the genuine L²
property from its Gaussian almost-everywhere equality with the class. -/
theorem entireRepresentative_memLp_two_gaussianArea
    (alpha : ℝ) (x : entireGaussianL2Submodule alpha) :
    MemLp (entireRepresentative alpha x) 2 (gaussianAreaMeasure alpha) := by
  exact (Lp.memLp (x : Lp ℂ 2 (gaussianAreaMeasure alpha))).ae_eq
    (entireRepresentative_ae alpha x).symm

/-- The actual entire representative times a conjugate monomial is
Gaussian L¹ for every order, without assuming polynomial density. -/
theorem entireRepresentative_conjugate_monomial_integrable
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    Integrable
      (fun z : ℂ => entireRepresentative alpha x z * star (z ^ n))
      (gaussianAreaMeasure alpha) := by
  exact MemLp.integrable_mul (p := 2) (q := 2)
    (entireRepresentative_memLp_two_gaussianArea alpha x)
    (conjugate_monomial_memLp_two_gaussianArea alpha ha n)

#print axioms GegenbauerFock.GaussianArea.conjugate_monomial_memLp_two_gaussianArea
#print axioms GegenbauerFock.GaussianArea.gaussianL2_conjugate_monomial_integrable
#print axioms GegenbauerFock.GaussianArea.entireRepresentative_memLp_two_gaussianArea
#print axioms GegenbauerFock.GaussianArea.entireRepresentative_conjugate_monomial_integrable

end GegenbauerFock.GaussianArea
