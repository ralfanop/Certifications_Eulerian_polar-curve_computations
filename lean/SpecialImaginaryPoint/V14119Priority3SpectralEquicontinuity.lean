import SpecialImaginaryPoint.V14119Priority3UniversalCompressionTraceNorm

/-!
# Priority 3 — spectral parameter perturbation of true finite Hilbert determinants

The unconditional true CFC-S₁ trace-norm estimate at every finite
Hilbert compression dimension yields a dimension-free bound in z.

  |D_N(T,z)-D_N(T,w)|
  <= |z-w| ||T||₁ exp((|w|+|z-w|)||T||₁).

The core exact identity is D_N(T,z)=D_N(z • T,1).
Together these provide N-equicontinuity in the complex spectral
parameter, a prerequisite for the locally uniform convergence
needed for entire holomorphy of the universal determinant.
-/

noncomputable section
namespace Manuscript14Priority3.SpectralEquicontinuity

open Filter Topology InnerProductSpace
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.FiniteRankFredholm
open Manuscript14Priority3.UniversalCompressionTraceNorm

/-- Genuine finite Hilbert-compression matrix is complex-linear
with respect to scalar multiplication of an arbitrary CFC trace-class
operator, without positivity or normality assumptions. -/
theorem compressedCFC_smul (N : ℕ)
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    compressedCFC N (z • T) = z • compressedCFC N T := by
  ext i j
  simp only [compressedCFC, Matrix.smul_apply,
    ProbabilisticTheory.TraceClass.smul_operator,
    ContinuousLinearMap.smul_apply, inner_smul_right]

/-- Exact commutation of spectral scalar z with CFC-S₁ operator
scaling inside an ACTUAL finite Hilbert compression determinant. -/
theorem finiteDeterminant_spectral_smul
    (N : ℕ) (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    finiteDeterminant N T z = finiteDeterminant N (z • T) 1 := by
  simp only [finiteDeterminant, compressedCFC_smul, one_smul]

/-- Dimension-independent complex spectral perturbation inequality
for every genuine CFC-S₁ operator and every finite compression N.
No unproved finite optimality assumption. -/
theorem finiteDeterminant_spectral_diff_norm_le
    (N : ℕ) (T : ProbabilisticTheory.TraceClass H) (z w : ℂ) :
    ‖finiteDeterminant N T z - finiteDeterminant N T w‖ ≤
      (‖z - w‖ * ‖T‖) *
        Real.exp ((‖w‖ + ‖z-w‖) * ‖T‖) := by
  have hsum : w • T + (z-w) • T = z • T := by
    rw [← add_smul]
    congr 1
    ring
  have h := finiteDeterminant_global_traceNorm_perturbation
    N (w • T) ((z-w) • T) 1
  rw [hsum] at h
  rw [← finiteDeterminant_spectral_smul N T z,
      ← finiteDeterminant_spectral_smul N T w] at h
  simpa only [norm_one, one_mul, norm_smul, mul_assoc, add_mul] using h

#print axioms Manuscript14Priority3.SpectralEquicontinuity.compressedCFC_smul
#print axioms Manuscript14Priority3.SpectralEquicontinuity.finiteDeterminant_spectral_smul
#print axioms Manuscript14Priority3.SpectralEquicontinuity.finiteDeterminant_spectral_diff_norm_le

end Manuscript14Priority3.SpectralEquicontinuity
