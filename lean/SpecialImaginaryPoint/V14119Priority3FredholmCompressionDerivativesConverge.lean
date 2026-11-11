import SpecialImaginaryPoint.V14119Priority3UniversalFredholmComplexScaleCovariance
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Priority 3 — derivatives and logarithmic derivatives of genuine Fredholm compressions

For every arbitrary complex CFC Schatten-S₁ Hilbert operator T, the
TRUE finite Hilbert-compression determinant polynomials
  D_N(T,z) = det(I_N + z P_N T P_N)
converge LOCALLY UNIFORMLY in z to the genuine universal Fredholm
determinant D(T,z). By the complex-analytic Weierstrass theorem
in Mathlib, their derivatives ALSO converge locally uniformly.

Moreover, at every z for which the actual universal determinant
does not vanish, the logarithmic derivatives of the genuine finite
compression determinants converge pointwise to the actual infinite
Fredholm logarithmic derivative.

This is NOT an assertion of a spectral product or an unverified
trace-resolvent identity. It certifies passage to the infinite limit
for complex derivatives and logarithmic derivatives without any
normality or positivity assumptions.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmCompressionDerivativesConverge

open Filter Topology Set Complex
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire

/-- Locally uniform convergence on ALL ℂ of derivatives of the
ACTUAL finite CFC-S₁ Hilbert compression determinant polynomials. -/
theorem finiteFredholm_derivatives_locally_uniform
    (T : ProbabilisticTheory.TraceClass H) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => deriv (finiteDeterminant N T))
      (deriv (fredholmDet T)) atTop (Set.univ : Set ℂ) := by
  have h := (finiteDeterminants_spectral_locally_uniform T).deriv
    (Filter.Eventually.of_forall
      (fun N => (finiteDeterminant_entire N T).differentiableOn))
    isOpen_univ
  simpa only [Function.comp_def] using h

/-- For every complex spectral parameter, the complex derivatives
of genuine Hilbert-compression Fredholm determinants converge
pointwise to the derivative of the true universal determinant. -/
theorem finiteFredholm_derivatives_pointwise_tendsto
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    Tendsto (fun N : ℕ => deriv (finiteDeterminant N T) z)
      atTop (𝓝 (deriv (fredholmDet T) z)) := by
  exact (finiteFredholm_derivatives_locally_uniform T).tendsto_at
    (Set.mem_univ z)

/-- At any nonzero spectral parameter of the TRUE universal Fredholm
determinant, the logarithmic derivatives of its ACTUAL finite Hilbert
compression determinant polynomials converge pointwise. -/
theorem finiteFredholm_logDerivatives_pointwise_tendsto
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : fredholmDet T z ≠ 0) :
    Tendsto (fun N : ℕ => logDeriv (finiteDeterminant N T) z)
      atTop (𝓝 (logDeriv (fredholmDet T) z)) := by
  exact Complex.logDeriv_tendsto isOpen_univ (Set.mem_univ z)
    (finiteDeterminants_spectral_locally_uniform T)
    (Filter.Eventually.of_forall
      (fun N => (finiteDeterminant_entire N T).differentiableOn))
    hz

#print axioms Manuscript14Priority3.FredholmCompressionDerivativesConverge.finiteFredholm_derivatives_locally_uniform
#print axioms Manuscript14Priority3.FredholmCompressionDerivativesConverge.finiteFredholm_derivatives_pointwise_tendsto
#print axioms Manuscript14Priority3.FredholmCompressionDerivativesConverge.finiteFredholm_logDerivatives_pointwise_tendsto

end Manuscript14Priority3.FredholmCompressionDerivativesConverge
