import SpecialImaginaryPoint.V14119Priority3FiniteFredholmZeroDivisor
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Analytic.Order

/-!
# Priority 3 — exact identification of the true universal Fredholm zero divisor

For every complex CFC Schatten-S₁ trace-class Hilbert operator T, even
nonnormal and nonselfadjoint, the ACTUAL universal Hilbert-compression-limit
Fredholm determinant f_T(z)=det_F(I+zT) is entire and f_T(0)=1.

We have independently constructed (i) the exact finite set of genuine
Fredholm zeros in a closed disk, and (ii) their strictly positive finite
analytic multiplicities. Mathlib's classical meromorphic divisor theory
provides an apparently different locally finitely supported integer-valued
divisor on the same disk.

This module proves that the sum of Mathlib's *actual analytic divisor*
of the true infinite-dimensional operatorial Fredholm determinant equals
exactly the previously constructed finite positive-natural multiplicity
sum. This equality is the bridge needed to transfer Jensen's classical
inequality directly to the operatorial finite-zero divisor.

No artificial finite matrix spectral determinant or eigenvalue
enumeration is assumed.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmDivisorFinsum

open Filter Topology Set Metric
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire
open Manuscript14Priority3.UniversalFredholmZeroMultiplicity
open Manuscript14Priority3.FiniteFredholmZeroDivisor

/-- The genuine Mathlib meromorphic divisor sum on a finite disk is
EXACTLY the total analytic multiplicity of the independently
constructed true universal Fredholm finite spectral zero divisor. -/
theorem universalFredholm_divisor_finsum_eq_totalMultiplicity
    (T : ProbabilisticTheory.TraceClass H) (R : ℝ) :
    (∑ᶠ z : ℂ,
      MeromorphicOn.divisor (fredholmDet T)
        (Metric.closedBall (0 : ℂ) R) z) =
      (universalFredholm_closedDisk_totalMultiplicity T R : ℤ) := by
  classical
  let U : Set ℂ := Metric.closedBall (0 : ℂ) R
  let S : Finset ℂ := universalFredholm_closedDisk_zeroFinset T R
  have hAnalytic : AnalyticOnNhd ℂ (fredholmDet T) U := by
    intro z _
    exact (universal_fredholmDet_entire T).analyticAt z
  have hSupport :
      Function.support
        (fun z : ℂ => MeromorphicOn.divisor (fredholmDet T) U z) ⊆
          (S : Set ℂ) := by
    intro z hz
    have hzNe :
        MeromorphicOn.divisor (fredholmDet T) U z ≠ 0 := by
      simpa only [Function.mem_support] using hz
    by_cases hzU : z ∈ U
    · by_cases hz0 : fredholmDet T z = 0
      · have hbound : ‖z‖ ≤ R := by
          simpa [U, Metric.mem_closedBall, dist_zero_right] using hzU
        change z ∈ S
        exact (mem_universalFredholm_closedDisk_zeroFinset_iff T R z).mpr
          ⟨hbound, hz0⟩
      · have horder :
            analyticOrderAt (fredholmDet T) z = 0 :=
          ((hAnalytic z hzU).analyticOrderAt_eq_zero).mpr hz0
        have hdiv :
            MeromorphicOn.divisor (fredholmDet T) U z = 0 := by
          rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAnalytic hzU, horder]
          simp
        exact (hzNe hdiv).elim
    · have hdiv :
          MeromorphicOn.divisor (fredholmDet T) U z = 0 := by
        simp [MeromorphicOn.divisor_def, hzU]
      exact (hzNe hdiv).elim
  have hPoint (z : ℂ) (hz : z ∈ S) :
      MeromorphicOn.divisor (fredholmDet T) U z =
        (analyticOrderNatAt (fredholmDet T) z : ℤ) := by
    have hbound : ‖z‖ ≤ R :=
      ((mem_universalFredholm_closedDisk_zeroFinset_iff T R z).mp hz).1
    have hzU : z ∈ U := by
      simpa [U, Metric.mem_closedBall, dist_zero_right] using hbound
    obtain ⟨n, hn⟩ := universalFredholm_analyticOrderAt_eq_nat T z
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAnalytic hzU, hn]
    simp [analyticOrderNatAt, hn]
  calc
    (∑ᶠ z : ℂ, MeromorphicOn.divisor (fredholmDet T) U z) =
        ∑ z ∈ S, MeromorphicOn.divisor (fredholmDet T) U z := by
      exact finsum_eq_sum_of_support_subset _ hSupport
    _ = ∑ z ∈ S, (analyticOrderNatAt (fredholmDet T) z : ℤ) := by
      exact Finset.sum_congr rfl hPoint
    _ = (universalFredholm_closedDisk_totalMultiplicity T R : ℤ) := by
      simp [universalFredholm_closedDisk_totalMultiplicity, S]

#print axioms Manuscript14Priority3.FredholmDivisorFinsum.universalFredholm_divisor_finsum_eq_totalMultiplicity

end Manuscript14Priority3.FredholmDivisorFinsum
