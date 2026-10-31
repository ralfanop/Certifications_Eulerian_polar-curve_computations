import GegenbauerFock.TwoSidedGramFredholmNullityDefect
import GegenbauerFock.SingularEigenspaceLinearEquiv

/-!
# V007 — bilateral equality of finite Fredholm range defects

For every nonzero complex spectral parameter, the actual source and
output Gram Fredholm shifts have equal finite-dimensional kernels, via
the original Gegenbauer–Fock map C and its inverse on each nonzero
eigenspace. Their Fredholm indices vanish, so the finite codimensions
of their respective ranges must coincide.

This is a comparison of finite nullity/defect data on two distinct
infinite-dimensional Hilbert spaces; no global identification or
surjectivity of C is asserted.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The kernel of a bounded complex Hilbert-space spectral shift is
the algebraic eigenspace of the underlying linear endomorphism. -/
theorem continuousGramShift_kernel_eq_eigenspace
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (mu : ℂ) :
    (T - mu • (1 : H →L[ℂ] H)).ker =
      eigenspace T.toLinearMap mu := by
  ext x
  rw [LinearMap.mem_ker, mem_eigenspace_iff]
  change T x - mu • x = 0 ↔ T x = mu • x
  exact sub_eq_zero

/-- The actual source/output Gram shifts have the same nullity at
every nonzero complex parameter, not just at a chosen eigenvalue. -/
theorem two_sided_nonzero_gram_shift_kernel_finrank_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    Module.finrank ℂ (gram lam alpha hlam ha -
      mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam))).ker =
    Module.finrank ℂ (outputGram lam alpha hlam ha -
      mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
        InfiniteAnalysis.FockCoefficients)).ker := by
  rw [continuousGramShift_kernel_eq_eigenspace,
    continuousGramShift_kernel_eq_eigenspace]
  exact C_nonzero_eigenspace_finrank_eq lam alpha hlam ha mu hmu

/-- The finite Fredholm cokernels (quotients by the operator ranges)
of the two distinct actual Gram shifts have equal complex dimension
for every nonzero complex parameter, including nonzero eigenvalues. -/
theorem two_sided_nonzero_gram_shift_range_defects_equal
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    let S := gram lam alpha hlam ha -
      mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam))
    let R := outputGram lam alpha hlam ha -
      mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
        InfiniteAnalysis.FockCoefficients)
    Module.finrank ℂ (Lp ℂ 2 (Ultraspherical.measure lam) ⧸ S.range) =
      Module.finrank ℂ (InfiniteAnalysis.FockCoefficients ⧸ R.range) := by
  dsimp
  have hs := sourceGram_nonzero_shift_nullity_eq_defect
    lam alpha hlam ha mu hmu
  have hr := outputGram_nonzero_shift_nullity_eq_defect
    lam alpha hlam ha mu hmu
  dsimp at hs hr
  calc
    Module.finrank ℂ (Lp ℂ 2 (Ultraspherical.measure lam) ⧸
      (gram lam alpha hlam ha -
        mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))).range) =
      Module.finrank ℂ (gram lam alpha hlam ha -
        mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))).ker := hs.symm
    _ = Module.finrank ℂ (outputGram lam alpha hlam ha -
        mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients)).ker :=
      two_sided_nonzero_gram_shift_kernel_finrank_eq lam alpha hlam ha mu hmu
    _ = Module.finrank ℂ (InfiniteAnalysis.FockCoefficients ⧸
        (outputGram lam alpha hlam ha -
          mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
            InfiniteAnalysis.FockCoefficients)).range) := hr

/-- For a nonzero complex parameter, the Fredholm range defect of the
ultraspherical source Gram shift equals the geometric multiplicity of
that parameter as an eigenvalue of the genuine source Gram. -/
theorem sourceGram_nonzero_shift_defect_eq_eigenspace_finrank
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    Module.finrank ℂ (Lp ℂ 2 (Ultraspherical.measure lam) ⧸
      (gram lam alpha hlam ha -
        mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))).range) =
    Module.finrank ℂ (eigenspace (gram lam alpha hlam ha).toLinearMap mu) := by
  have hs := sourceGram_nonzero_shift_nullity_eq_defect
    lam alpha hlam ha mu hmu
  dsimp only at hs
  rw [continuousGramShift_kernel_eq_eigenspace] at hs
  exact hs.symm

/-- The corresponding Fredholm range defect of the full Gaussian-Fock
output Gram shift equals its true nonzero eigenvalue multiplicity. -/
theorem outputGram_nonzero_shift_defect_eq_eigenspace_finrank
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    Module.finrank ℂ (InfiniteAnalysis.FockCoefficients ⧸
      (outputGram lam alpha hlam ha -
        mu • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients)).range) =
    Module.finrank ℂ (eigenspace (outputGram lam alpha hlam ha).toLinearMap mu) := by
  have hr := outputGram_nonzero_shift_nullity_eq_defect
    lam alpha hlam ha mu hmu
  dsimp only at hr
  rw [continuousGramShift_kernel_eq_eigenspace] at hr
  exact hr.symm

#print axioms GegenbauerFock.GeneralUltrasphericalFock.continuousGramShift_kernel_eq_eigenspace
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_nonzero_gram_shift_kernel_finrank_eq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_nonzero_gram_shift_range_defects_equal
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_nonzero_shift_defect_eq_eigenspace_finrank
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_nonzero_shift_defect_eq_eigenspace_finrank

end GegenbauerFock.GeneralUltrasphericalFock
