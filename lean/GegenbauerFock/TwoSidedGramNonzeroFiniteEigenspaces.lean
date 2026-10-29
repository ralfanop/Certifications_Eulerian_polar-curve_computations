import GegenbauerFock.TwoSidedGramSpectrumEquality
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# V007 — finite geometric multiplicity of all nonzero bilateral Gram eigenvalues

The two true Gram endomorphisms C†C and CC† are compact.
Mathlib's compact-operator spectral theorem proves that their
eigenspaces are finite-dimensional at every nonzero scalar.

This is a genuine new ingredient in the program to identify the
full Fredholm essential spectrum as {0}: nonzero eigenvalues have
finite *geometric multiplicity*. It is not by itself sufficient to
conclude the shifted operators are Fredholm; the range-closedness
and finite-cokernel obligations for every nonzero shift remain.

The result does not use finite matrix truncations or identify the
distinct ultraspherical and Fock-coefficient Hilbert spaces.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Every nonzero eigenspace of the true source Gram is
finite-dimensional in the full ultraspherical L² Hilbert space. -/
theorem sourceGram_nonzero_eigenspace_finiteDimensional
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    FiniteDimensional ℂ (eigenspace (gram lam alpha hlam ha).toLinearMap mu) :=
  ContinuousLinearMap.finite_dimensional_eigenspace
    (gram_compact_concrete lam alpha hlam ha) mu hmu

/-- Every nonzero eigenspace of the true Fock-output Gram is
finite-dimensional in the full coefficient Hilbert space. -/
theorem outputGram_nonzero_eigenspace_finiteDimensional
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    FiniteDimensional ℂ (eigenspace (outputGram lam alpha hlam ha).toLinearMap mu) :=
  ContinuousLinearMap.finite_dimensional_eigenspace
    (outputGram_compact lam alpha hlam ha) mu hmu

/-- Finite geometric multiplicity simultaneously for both true
Gram endomorphisms, including at all common positive eigenvalues. -/
theorem two_sided_gram_nonzero_eigenspaces_finiteDimensional
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    FiniteDimensional ℂ (eigenspace (gram lam alpha hlam ha).toLinearMap mu) ∧
    FiniteDimensional ℂ (eigenspace (outputGram lam alpha hlam ha).toLinearMap mu) :=
  ⟨sourceGram_nonzero_eigenspace_finiteDimensional lam alpha hlam ha mu hmu,
   outputGram_nonzero_eigenspace_finiteDimensional lam alpha hlam ha mu hmu⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_nonzero_eigenspace_finiteDimensional
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_nonzero_eigenspace_finiteDimensional
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_nonzero_eigenspaces_finiteDimensional

end GegenbauerFock.GeneralUltrasphericalFock
