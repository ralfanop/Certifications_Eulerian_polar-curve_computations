import GegenbauerFock.TwoSidedGramNonzeroFredholmIndexZero
import Mathlib.Algebra.Module.LinearMap.Index

/-!
# V007 — equality of nullity and defect for all nonzero Gram shifts

The Fredholm index vanishes at every nonzero spectral shift of each
of the genuine ultraspherical/Fock Grams. Unfolding the index gives
an equality between the finite dimension of the kernel and the
finite codimension of the range, even at nonzero eigenvalues.
This is not a finite-matrix or truncation statement.

The dependent zero-index module and this module must pass the pinned
Lean kernel and axiom audits before being called certified.
-/

noncomputable section

-- Elaborating the two concrete infinite-dimensional Gram shifts can require
-- more reduction steps than Lean's default heartbeat budget.
set_option maxHeartbeats 2000000

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- For any complex Hilbert operator of Fredholm index zero, its
kernel dimension equals the codimension of its range. -/
theorem fredholmIndexZero_finrank_kernel_eq_cokernel
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : H →L[ℂ] H)
    (hFred : S.IsFredholm) (hIndex : S.index = 0) :
    Module.finrank ℂ S.ker = Module.finrank ℂ (H ⧸ S.range) := by
  haveI : FiniteDimensional ℂ S.ker := hFred.finite_ker
  haveI : S.range.CoFG := hFred.finite_coker
  have h : (Module.finrank ℂ S.ker : ℤ) -
      (Module.finrank ℂ (H ⧸ S.range) : ℤ) = 0 := by
    change (S.toLinearMap).index = 0 at hIndex
    simpa only [LinearMap.index_eq_finrank_sub] using hIndex
  omega

/-- At every nonzero complex spectral shift of the actual source
Gram, the Fredholm kernel dimension equals the range codimension. -/
theorem sourceGram_nonzero_shift_nullity_eq_defect
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    let S := gram lam alpha hlam ha -
      mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam))
    Module.finrank ℂ S.ker =
      Module.finrank ℂ (Lp ℂ 2 (Ultraspherical.measure lam) ⧸ S.range) := by
  dsimp only
  exact fredholmIndexZero_finrank_kernel_eq_cokernel _
    (sourceGram_nonzero_shift_isFredholm lam alpha hlam ha mu hmu)
    (sourceGram_nonzero_shift_fredholm_index_zero lam alpha hlam ha mu hmu)

/-- At every nonzero shift of the full Gaussian-Fock output Gram,
the range defect equals its finite-dimensional kernel nullity. -/
theorem outputGram_nonzero_shift_nullity_eq_defect
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    let S := outputGram lam alpha hlam ha -
      mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
        InfiniteAnalysis.FockCoefficients)
    Module.finrank ℂ S.ker =
      Module.finrank ℂ (InfiniteAnalysis.FockCoefficients ⧸ S.range) := by
  dsimp only
  exact fredholmIndexZero_finrank_kernel_eq_cokernel _
    (outputGram_nonzero_shift_isFredholm lam alpha hlam ha mu hmu)
    (outputGram_nonzero_shift_fredholm_index_zero lam alpha hlam ha mu hmu)

/-- Bilateral zero-index Fredholm operators have equal kernel and
cokernel dimensions at all nonzero spectral parameters. -/
theorem two_sided_gram_nonzero_shift_nullity_defect_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    (let S := gram lam alpha hlam ha -
      mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam))
     Module.finrank ℂ S.ker =
       Module.finrank ℂ (Lp ℂ 2 (Ultraspherical.measure lam) ⧸ S.range)) ∧
    (let S := outputGram lam alpha hlam ha -
      mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
        InfiniteAnalysis.FockCoefficients)
     Module.finrank ℂ S.ker =
       Module.finrank ℂ (InfiniteAnalysis.FockCoefficients ⧸ S.range)) :=
  ⟨sourceGram_nonzero_shift_nullity_eq_defect lam alpha hlam ha mu hmu,
    outputGram_nonzero_shift_nullity_eq_defect lam alpha hlam ha mu hmu⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.fredholmIndexZero_finrank_kernel_eq_cokernel
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_nonzero_shift_nullity_eq_defect
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_nonzero_shift_nullity_eq_defect
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_nonzero_shift_nullity_defect_eq

end GegenbauerFock.GeneralUltrasphericalFock
