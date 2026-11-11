import SpecialImaginaryPoint.V14119Priority3UniversalFredholmLogDerivative
import Mathlib.Analysis.Analytic.Order

/-!
# Priority 3 — finite positive multiplicity at every genuine Fredholm spectral zero

For ANY CFC Schatten-S₁ complex trace-class Hilbert operator T, the
actual universal Hilbert-compression-limit Fredholm determinant
    f_T(z) = det_F(I+zT)
is entire and satisfies f_T(0)=1. Hence it is not identically zero.

Mathlib's analytic identity theorem then proves that the analytic
order of f_T at EVERY complex spectral parameter is finite. At any
spectral zero, the order is a positive natural number. Thus every
genuine Fredholm spectral zero has finite strictly positive analytic
multiplicity, even for nonnormal and nonselfadjoint T.

No eigenvalue enumeration or operator invertibility criterion is used.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalFredholmZeroMultiplicity

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire

/-- For an arbitrary trace-class operator, the actual universal
Fredholm determinant has finite analytic order at EVERY complex shift. -/
theorem universalFredholm_analyticOrderAt_ne_top
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    analyticOrderAt (fredholmDet T) z ≠ ⊤ := by
  intro htop
  have hfzero : fredholmDet T = 0 :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
      (fun w => (universal_fredholmDet_entire T).analyticAt w)).mp htop
  have hcontra : (1 : ℂ) = 0 := by
    simpa [fredholmDet_zero] using congrFun hfzero 0
  exact one_ne_zero hcontra

/-- At each genuine complex Fredholm spectral parameter there exists
a finite natural-number analytic order, without normality assumptions. -/
theorem universalFredholm_analyticOrderAt_eq_nat
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    ∃ n : ℕ, analyticOrderAt (fredholmDet T) z = n := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
    (universalFredholm_analyticOrderAt_ne_top T z)
  exact ⟨n, hn.symm⟩

/-- At an actual zero of the infinite-dimensional Fredholm determinant,
the analytic order is never zero. -/
theorem universalFredholm_analyticOrderAt_ne_zero
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : fredholmDet T z = 0) :
    analyticOrderAt (fredholmDet T) z ≠ 0 := by
  exact ((universal_fredholmDet_entire T).analyticAt z).analyticOrderAt_ne_zero.mpr hz

/-- Every genuine universal Fredholm determinant zero has finite,
strictly POSITIVE analytic multiplicity n ≥ 1. -/
theorem universalFredholm_zero_has_positive_finite_order
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : fredholmDet T z = 0) :
    ∃ n : ℕ, 0 < n ∧ analyticOrderAt (fredholmDet T) z = n := by
  obtain ⟨n, hn⟩ := universalFredholm_analyticOrderAt_eq_nat T z
  have hnpos : 0 < n := by
    by_contra hnot
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnot
    apply universalFredholm_analyticOrderAt_ne_zero T z hz
    simpa only [hnzero, Nat.cast_zero] using hn
  exact ⟨n, hnpos, hn⟩

#print axioms Manuscript14Priority3.UniversalFredholmZeroMultiplicity.universalFredholm_analyticOrderAt_ne_top
#print axioms Manuscript14Priority3.UniversalFredholmZeroMultiplicity.universalFredholm_analyticOrderAt_eq_nat
#print axioms Manuscript14Priority3.UniversalFredholmZeroMultiplicity.universalFredholm_analyticOrderAt_ne_zero
#print axioms Manuscript14Priority3.UniversalFredholmZeroMultiplicity.universalFredholm_zero_has_positive_finite_order

end Manuscript14Priority3.UniversalFredholmZeroMultiplicity
