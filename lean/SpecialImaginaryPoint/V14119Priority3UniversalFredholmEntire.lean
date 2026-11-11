import SpecialImaginaryPoint.V14119Priority3UniversalFredholmExistence
import SpecialImaginaryPoint.V14119Priority3SpectralEquicontinuity
import SpecialImaginaryPoint.V14119Priority3SpectralExpEquicontinuity
import SpecialImaginaryPoint.V14119Priority3EquicontinuousWeierstrass
import SpecialImaginaryPoint.V14119Priority3FiniteShiftEntirePolynomial

/-!
# Priority 3 — ENTIRE holomorphy of the genuine universal CFC-S₁ Fredholm determinant

For every actual CFC trace-class Hilbert operator T, not necessarily
normal, selfadjoint, positive or invertible, the universal determinant
constructed as the true N-dimensional Hilbert compression limit
  z ↦ fredholmDet T z
is COMPLEX ENTIRE.

* Every actual finite Hilbert compression det(I_N+z P_N T P_N)
  is exactly a complex matrix polynomial (certified finite lemma).
* The sharp genuine trace-norm perturbation in operator variable,
  after replacing T by z•T, gives dimension-independent
  equicontinuity of the compression determinants in z.
* Since they converge pointwise for every T,z, compact Ascoli yields
  locally uniform convergence throughout ℂ.
* Mathlib's complex Weierstrass theorem proves the limit entire.

This module discharges the final analyticity obligation independently
of any spectral enumeration or positivity. Every theorem below is
unconditional once the previous kernel-checked module imports compile.
-/

noncomputable section
namespace Manuscript14Priority3.UniversalFredholmEntire

open Filter Topology
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.FiniteRankFredholm
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.SpectralEquicontinuity
open Manuscript14Priority3.SpectralExpEquicontinuity
open Manuscript14Priority3.EquicontinuousWeierstrass
open Manuscript14Priority3.FiniteShiftEntirePolynomial

/-- Every TRUE finite-dimensional Hilbert compression Fredholm
determinant is entire in the complex spectral parameter. -/
theorem finiteDeterminant_entire
    (N : ℕ) (T : ProbabilisticTheory.TraceClass H) :
    Differentiable ℂ (fun z : ℂ => finiteDeterminant N T z) := by
  change Differentiable ℂ
    (fun z : ℂ => (1 + z • compressedCFC N T).det)
  exact determinant_shift_entire N (compressedCFC N T)

/-- The ENTIRE family of genuine Hilbert compression determinant
functions is equicontinuous in z at every complex point,
with a neighborhood independent of the dimension N. -/
theorem finiteDeterminants_spectral_equicontinuous
    (T : ProbabilisticTheory.TraceClass H) :
    Equicontinuous
      (fun N : ℕ => fun z : ℂ => finiteDeterminant N T z) := by
  exact equicontinuity_of_asymmetric_exponential_norm_bound
    (fun N : ℕ => fun z : ℂ => finiteDeterminant N T z)
    ‖T‖ (norm_nonneg T)
    (fun N z w => finiteDeterminant_spectral_diff_norm_le N T z w)

/-- Genuine CFC Schatten-S₁ Fredholm finite compression polynomials
converge locally uniformly in z on all ℂ to the universal Fredholm
determinant, for any T even nonnormal and nonselfadjoint. -/
theorem finiteDeterminants_spectral_locally_uniform
    (T : ProbabilisticTheory.TraceClass H) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun z : ℂ => finiteDeterminant N T z)
      (fredholmDet T) atTop (Set.univ : Set ℂ) := by
  exact locally_uniform_of_equicontinuous
    (fun N : ℕ => fun z : ℂ => finiteDeterminant N T z)
    (fredholmDet T)
    (finiteDeterminants_spectral_equicontinuous T)
    (fun z => finiteDeterminant_tendsto_fredholmDet T z)

/-- COMPLETE: the true universal Fredholm determinant on the
infinite-dimensional genuine CFC-S₁ ideal is ENTIRE in z for
all operators, with NO positivity/normality/invertibility assumption. -/
theorem universal_fredholmDet_entire
    (T : ProbabilisticTheory.TraceClass H) :
    Differentiable ℂ (fredholmDet T) := by
  exact entire_of_equicontinuous_pointwise
    (fun N : ℕ => fun z : ℂ => finiteDeterminant N T z)
    (fredholmDet T)
    (finiteDeterminants_spectral_equicontinuous T)
    (fun z => finiteDeterminant_tendsto_fredholmDet T z)
    (fun N => finiteDeterminant_entire N T)

#print axioms Manuscript14Priority3.UniversalFredholmEntire.finiteDeterminant_entire
#print axioms Manuscript14Priority3.UniversalFredholmEntire.finiteDeterminants_spectral_equicontinuous
#print axioms Manuscript14Priority3.UniversalFredholmEntire.finiteDeterminants_spectral_locally_uniform
#print axioms Manuscript14Priority3.UniversalFredholmEntire.universal_fredholmDet_entire

end Manuscript14Priority3.UniversalFredholmEntire
