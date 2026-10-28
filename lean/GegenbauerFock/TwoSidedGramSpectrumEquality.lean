import GegenbauerFock.TwoSidedGramContinuousSpectrum
import GegenbauerFock.SingularEigenspaceLinearEquiv
import GegenbauerFock.OutputGramSpectrum
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# V007 — full spectrum equality of both actual compact Gram operators

Let G = C†C act on ultraspherical L² and H = CC† act on the full
Fock coefficient Hilbert space. Fredholm's alternative says that
every nonzero spectral value of a compact endomorphism is an eigenvalue.
The previously proved eigenvector transfers imply that their nonzero
spectra agree; the already certified bilateral zero spectral theorem
then upgrades this to equality of their entire complex spectra.

The Hilbert spaces are not identified, the operator C is not claimed
surjective, and zero is a continuous spectral value rather than an
eigenvalue for either Gram.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Every nonzero eigenvalue occurs for both true Gram operators. -/
theorem two_sided_gram_hasEigenvalue_iff
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    HasEigenvalue (gram lam alpha hlam ha).toLinearMap mu ↔
      HasEigenvalue (outputGram lam alpha hlam ha).toLinearMap mu := by
  constructor
  · intro hsource
    obtain ⟨f, hf⟩ := hsource.exists_hasEigenvector
    have hfne : f ≠ 0 := (hasEigenvector_iff.mp hf).2
    have hfeq : gram lam alpha hlam ha f = mu • f :=
      mem_eigenspace_iff.mp (hasEigenvector_iff.mp hf).1
    obtain ⟨F, hFne, hFeq⟩ :=
      (gram_outputGram_nonzero_eigenvalue_iff lam alpha hlam ha mu hmu).mp
        ⟨f, hfne, hfeq⟩
    apply hasEigenvalue_of_hasEigenvector
    exact hasEigenvector_iff.mpr
      ⟨mem_eigenspace_iff.mpr hFeq, hFne⟩
  · intro htarget
    obtain ⟨F, hF⟩ := htarget.exists_hasEigenvector
    have hFne : F ≠ 0 := (hasEigenvector_iff.mp hF).2
    have hFeq : outputGram lam alpha hlam ha F = mu • F :=
      mem_eigenspace_iff.mp (hasEigenvector_iff.mp hF).1
    obtain ⟨f, hfne, hfeq⟩ :=
      (gram_outputGram_nonzero_eigenvalue_iff lam alpha hlam ha mu hmu).mpr
        ⟨F, hFne, hFeq⟩
    apply hasEigenvalue_of_hasEigenvector
    exact hasEigenvector_iff.mpr
      ⟨mem_eigenspace_iff.mpr hfeq, hfne⟩

/-- Compactness and the Fredholm alternative upgrade equality of
nonzero *point spectra* to equality of nonzero operator spectra. -/
theorem two_sided_gram_nonzero_spectrum_iff
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    mu ∈ spectrum ℂ (gram lam alpha hlam ha) ↔
      mu ∈ spectrum ℂ (outputGram lam alpha hlam ha) := by
  have hsource :=
    (gram_compact_concrete lam alpha hlam ha).hasEigenvalue_iff_mem_spectrum hmu
  have htarget :=
    (outputGram_compact lam alpha hlam ha).hasEigenvalue_iff_mem_spectrum hmu
  exact hsource.symm.trans
    ((two_sided_gram_hasEigenvalue_iff lam alpha hlam ha mu hmu).trans htarget)

/-- The true L²-source Gram and full Fock-output Gram have exactly
the same complex operator spectrum, *including zero*. This is a
set equality of spectra, not an isomorphism of their Hilbert spaces. -/
theorem two_sided_gram_spectrum_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    spectrum ℂ (gram lam alpha hlam ha) =
      spectrum ℂ (outputGram lam alpha hlam ha) := by
  ext mu
  by_cases hmu : mu = 0
  · subst mu
    exact ⟨fun _ => outputGram_zero_mem_spectrum lam alpha hlam ha,
      fun _ => gram_zero_mem_spectrum lam alpha hlam ha⟩
  · exact two_sided_gram_nonzero_spectrum_iff lam alpha hlam ha mu hmu

#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_hasEigenvalue_iff
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_nonzero_spectrum_iff
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_spectrum_eq

end GegenbauerFock.GeneralUltrasphericalFock
