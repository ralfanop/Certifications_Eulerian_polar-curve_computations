import SpecialImaginaryPoint.V14119Priority3UniversalFredholmZeroMultiplicity
import Mathlib.Analysis.Analytic.Order

/-!
# Priority 3 — exact local analytic factorization of universal CFC-S₁ Fredholm zeros

For any complex CFC Schatten-S₁ Hilbert operator T (including arbitrary
nonnormal operators), its genuine universal Hilbert compression-limit
Fredholm determinant f_T(z) = det_F(I+zT) is entire, and f_T(0)=1.

Near ANY complex parameter z, the determinant admits a factorization
f_T(w) = (w-z)^n * g(w), with n a finite natural number and g analytic
near z with g(z) ≠ 0. If f_T(z)=0, then n is strictly positive.

The analytic factor is a genuine function on ℂ, locally equal to the
quotient by the exact zero multiplicity; no spectral eigenvalue
enumeration, selfadjointness, or diagonal positivity is presumed.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalFredholmLocalFactorization

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire
open Manuscript14Priority3.UniversalFredholmZeroMultiplicity

/-- At every complex shift, the TRUE universal Fredholm determinant
has a local analytic factorization with finite exponent and a
nonvanishing analytic residual factor. -/
theorem universalFredholm_local_factorization
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    ∃ (n : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
      (∀ᶠ w in 𝓝 z, fredholmDet T w = (w-z)^n * g w) := by
  obtain ⟨n, hn⟩ := universalFredholm_analyticOrderAt_eq_nat T z
  obtain ⟨g, hg, hg0, hfg⟩ :=
    (((universal_fredholmDet_entire T).analyticAt z).analyticOrderAt_eq_natCast).mp hn
  refine ⟨n, g, hg, hg0, ?_⟩
  filter_upwards [hfg] with w hw
  simpa only [smul_eq_mul] using hw

/-- At EVERY spectral zero of the genuine universal trace-class
Fredholm determinant, the local analytic factorization has
strictly positive exponent and nonvanishing analytic residual. -/
theorem universalFredholm_zero_local_factorization
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : fredholmDet T z = 0) :
    ∃ (n : ℕ) (g : ℂ → ℂ), 0 < n ∧ AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
      (∀ᶠ w in 𝓝 z, fredholmDet T w = (w-z)^n * g w) := by
  obtain ⟨n, hnpos, hn⟩ :=
    universalFredholm_zero_has_positive_finite_order T z hz
  obtain ⟨g, hg, hg0, hfg⟩ :=
    (((universal_fredholmDet_entire T).analyticAt z).analyticOrderAt_eq_natCast).mp hn
  refine ⟨n, g, hnpos, hg, hg0, ?_⟩
  filter_upwards [hfg] with w hw
  simpa only [smul_eq_mul] using hw

#print axioms Manuscript14Priority3.UniversalFredholmLocalFactorization.universalFredholm_local_factorization
#print axioms Manuscript14Priority3.UniversalFredholmLocalFactorization.universalFredholm_zero_local_factorization

end Manuscript14Priority3.UniversalFredholmLocalFactorization
