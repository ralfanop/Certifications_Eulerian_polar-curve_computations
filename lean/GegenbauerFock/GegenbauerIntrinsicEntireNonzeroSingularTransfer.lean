import GegenbauerFock.GegenbauerIntrinsicEntireOutputGram
import GegenbauerFock.GegenbauerIntrinsicEntireGramIdentity
import GegenbauerFock.GramSingularTransfer

/-!
# V007 — nonzero eigenvalue transfer to the actual holomorphic output Gram

The true intrinsic-entire Gaussian Fock Hilbert space and the infinite
coefficient Hilbert space are unitarily equivalent by the certified onto
Bargmann–Fock synthesis map. The actual output Gram C_hol C_hol† is
conjugate to C C† under this equivalence. Hence these two output Grams
have precisely the same nonzero point eigenvalues.

Combining this with the already certified source/output nonzero
singular-pair transfer proves that the actual ultraspherical-source
Gram C_hol† C_hol and the true holomorphic Gaussian Fock output Gram
C_hol C_hol† have precisely the same nonzero point eigenvalues.
No finite-section approximation or unproved surjectivity of C_hol is used.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Nonzero eigenvalues of the coefficient output Gram and the
intrinsic entire Gaussian Fock output Gram agree, with explicit
nonzero eigenvectors transported by the certified onto isometry. -/
theorem outputGram_eigenvalue_iff_intrinsicEntire_outputGram
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) :
    (∃ Fc : InfiniteAnalysis.FockCoefficients,
      Fc ≠ 0 ∧ outputGram lam alpha hlam ha Fc = mu • Fc) ↔
    (∃ F : GaussianArea.entireGaussianL2Submodule alpha,
      F ≠ 0 ∧ C_intrinsicEntire_outputGram lam alpha hlam ha F = mu • F) := by
  let U := GaussianArea.coefficientIntrinsicEntireEquiv alpha ha
  constructor
  · rintro ⟨Fc, hFc, hmu⟩
    refine ⟨U Fc, ?_, ?_⟩
    · intro hz
      have heq : Fc = 0 := U.injective (by simpa using hz)
      exact hFc heq
    · rw [C_intrinsicEntire_outputGram_apply]
      change U (outputGram lam alpha hlam ha (U.symm (U Fc))) = mu • U Fc
      rw [U.symm_apply_apply, hmu]
      exact map_smul U mu Fc
  · rintro ⟨F, hF, hmu⟩
    refine ⟨U.symm F, ?_, ?_⟩
    · intro hz
      apply hF
      have h : U (U.symm F) = 0 := by rw [hz, map_zero]
      simpa only [U.apply_symm_apply] using h
    · have hp := congrArg U.symm hmu
      rw [C_intrinsicEntire_outputGram_apply] at hp
      change U.symm (U (outputGram lam alpha hlam ha (U.symm F))) =
        U.symm (mu • F) at hp
      simpa only [U.symm_apply_apply, map_smul] using hp

/-- The two genuine Grams of the compact transform with holomorphic
Gaussian codomain have the same nonzero point spectrum. The source and
output Hilbert spaces are NOT identified with one another. -/
theorem intrinsicEntire_source_output_nonzero_eigenvalue_iff
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    (∃ f : Lp ℂ 2 (Ultraspherical.measure lam),
      f ≠ 0 ∧ C_intrinsicEntire_gram lam alpha hlam ha f = mu • f) ↔
    (∃ F : GaussianArea.entireGaussianL2Submodule alpha,
      F ≠ 0 ∧ C_intrinsicEntire_outputGram lam alpha hlam ha F = mu • F) := by
  simpa only [C_intrinsicEntire_gram_eq lam alpha hlam ha] using
    (gram_outputGram_nonzero_eigenvalue_iff lam alpha hlam ha mu hmu).trans
      (outputGram_eigenvalue_iff_intrinsicEntire_outputGram lam alpha hlam ha mu)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_eigenvalue_iff_intrinsicEntire_outputGram
#print axioms GegenbauerFock.GeneralUltrasphericalFock.intrinsicEntire_source_output_nonzero_eigenvalue_iff

end GegenbauerFock.GeneralUltrasphericalFock
