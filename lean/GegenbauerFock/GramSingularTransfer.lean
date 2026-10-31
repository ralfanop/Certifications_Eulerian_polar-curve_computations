import GegenbauerFock.GramSpectralKernel
import GegenbauerFock.GramSpectralTheorem

/-!
# V007: exact nonzero singular-pair transfer for the concrete Fock transform

This separates the two positive Gram operators C†C on the source and
CC† on the Fock coefficient target. Nonzero eigenvectors are carried
in both directions by the genuine bounded operator C and its Hilbert
adjoint. In particular the two Grams have exactly the same nonzero
point-spectrum, as a concrete first step toward the full singular
system.

No injectivity or dense-range hypothesis is introduced, and no
enumeration of singular values is claimed.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- Actual output-space Gram CC† on the infinite Fock coefficient space. -/
noncomputable def outputGram
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    InfiniteAnalysis.FockCoefficients →L[ℂ]
      InfiniteAnalysis.FockCoefficients :=
  (C lam alpha hlam ha).comp (C_adjoint lam alpha hlam ha)

/-- An eigenvector of C†C maps under C to an eigenvector of CC†
with the same complex eigenvalue. -/
theorem C_maps_gram_eigenvector
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (f : Lp ℂ 2 (Ultraspherical.measure lam))
    (h : gram lam alpha hlam ha f = mu • f) :
    outputGram lam alpha hlam ha (C lam alpha hlam ha f) =
      mu • C lam alpha hlam ha f := by
  change C lam alpha hlam ha (gram lam alpha hlam ha f) = _
  rw [h]
  simp

/-- Nonzero eigenvalues preserve nonzero vectors when transferred
from source to target. This follows from ker(C†C)=ker(C). -/
theorem C_maps_nonzero_gram_eigenvector
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) (hf : f ≠ 0)
    (h : gram lam alpha hlam ha f = mu • f) :
    C lam alpha hlam ha f ≠ 0 := by
  intro hz
  have hzG : gram lam alpha hlam ha f = 0 :=
    (gram_apply_eq_zero_iff_C_eq_zero lam alpha hlam ha f).2 hz
  have hzS : mu • f = 0 := h.symm.trans hzG
  exact (smul_ne_zero hmu hf) hzS

/-- Conversely C† transports each output Gram eigenvector to a
source Gram eigenvector with the same eigenvalue. -/
theorem C_adjoint_maps_output_eigenvector
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (F : InfiniteAnalysis.FockCoefficients)
    (h : outputGram lam alpha hlam ha F = mu • F) :
    gram lam alpha hlam ha (C_adjoint lam alpha hlam ha F) =
      mu • C_adjoint lam alpha hlam ha F := by
  change C_adjoint lam alpha hlam ha
      (outputGram lam alpha hlam ha F) = _
  rw [h]
  simp

/-- The dual transfer C† does not annihilate a nonzero eigenvector
at a nonzero eigenvalue. -/
theorem C_adjoint_maps_nonzero_output_eigenvector
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0)
    (F : InfiniteAnalysis.FockCoefficients) (hF : F ≠ 0)
    (h : outputGram lam alpha hlam ha F = mu • F) :
    C_adjoint lam alpha hlam ha F ≠ 0 := by
  intro hz
  have hzOut : outputGram lam alpha hlam ha F = 0 := by
    change C lam alpha hlam ha (C_adjoint lam alpha hlam ha F) = 0
    rw [hz]
    simp
  have hzS : mu • F = 0 := h.symm.trans hzOut
  exact (smul_ne_zero hmu hF) hzS

/-- Exact nonzero point-spectrum equivalence between the two actual
infinite-dimensional Grams, with no finite-rank approximation. -/
theorem gram_outputGram_nonzero_eigenvalue_iff
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    (∃ f : Lp ℂ 2 (Ultraspherical.measure lam),
      f ≠ 0 ∧ gram lam alpha hlam ha f = mu • f) ↔
    (∃ F : InfiniteAnalysis.FockCoefficients,
      F ≠ 0 ∧ outputGram lam alpha hlam ha F = mu • F) := by
  constructor
  · rintro ⟨f, hf, h⟩
    exact ⟨C lam alpha hlam ha f,
      C_maps_nonzero_gram_eigenvector lam alpha hlam ha mu hmu f hf h,
      C_maps_gram_eigenvector lam alpha hlam ha mu f h⟩
  · rintro ⟨F, hF, h⟩
    exact ⟨C_adjoint lam alpha hlam ha F,
      C_adjoint_maps_nonzero_output_eigenvector lam alpha hlam ha mu hmu F hF h,
      C_adjoint_maps_output_eigenvector lam alpha hlam ha mu F h⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_maps_gram_eigenvector
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_maps_nonzero_gram_eigenvector
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_maps_output_eigenvector
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_maps_nonzero_output_eigenvector
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_outputGram_nonzero_eigenvalue_iff

end GegenbauerFock.GeneralUltrasphericalFock
