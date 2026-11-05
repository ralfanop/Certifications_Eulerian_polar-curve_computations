import GegenbauerFock.SingularEigenspaceIsometry

/-!
# V007 — exact nonzero singular eigenspace correspondence

For each nonzero complex eigenvalue mu, the genuine source Gram C†C
and output Gram CC† have mutually inverse eigenspace transfers:
C maps source eigenvectors to output eigenvectors and mu⁻¹ C†
recovers the unique source eigenvector. These identities apply
in the actual infinite Hilbert spaces, without assuming global
injectivity or dense range. The positive-real normalization and
norm-preserving restriction are certified separately.

This module does not assert equal spectral multiplicities via a
bundled linear equivalence, or global completeness of singular values.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- The adjoint reverses the forward singular transfer on every
nonzero source-Gram eigenspace, after division by the eigenvalue. -/
theorem nonzero_source_eigenvector_recovered
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0)
    (f : Lp ℂ 2 (Ultraspherical.measure lam))
    (hf : gram lam alpha hlam ha f = mu • f) :
    mu⁻¹ • C_adjoint lam alpha hlam ha (C lam alpha hlam ha f) = f := by
  change mu⁻¹ • gram lam alpha hlam ha f = f
  rw [hf, smul_smul, inv_mul_cancel₀ hmu, one_smul]

/-- Conversely the forward operator reverses the adjoint transfer
on every nonzero output-Gram eigenspace. -/
theorem nonzero_output_eigenvector_recovered
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0)
    (F : InfiniteAnalysis.FockCoefficients)
    (hF : outputGram lam alpha hlam ha F = mu • F) :
    mu⁻¹ • C lam alpha hlam ha (C_adjoint lam alpha hlam ha F) = F := by
  change mu⁻¹ • outputGram lam alpha hlam ha F = F
  rw [hF, smul_smul, inv_mul_cancel₀ hmu, one_smul]

/-- The inverse image mu⁻¹ C†F of an output eigenvector is a genuine
source-Gram eigenvector, with the same nonzero eigenvalue. -/
theorem nonzero_output_eigenvector_source_preimage
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0)
    (F : InfiniteAnalysis.FockCoefficients)
    (hF : outputGram lam alpha hlam ha F = mu • F) :
    gram lam alpha hlam ha (mu⁻¹ • C_adjoint lam alpha hlam ha F) =
      mu • (mu⁻¹ • C_adjoint lam alpha hlam ha F) := by
  rw [map_smul,
    C_adjoint_maps_output_eigenvector lam alpha hlam ha mu F hF]
  simp only [smul_smul, mul_comm]

/-- Every output-Gram eigenvector at a nonzero eigenvalue lies
in the ACTUAL range of C, and its source preimage is again
a source-Gram eigenvector. -/
theorem nonzero_output_eigenvector_has_source
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0)
    (F : InfiniteAnalysis.FockCoefficients)
    (hF : outputGram lam alpha hlam ha F = mu • F) :
    ∃ f : Lp ℂ 2 (Ultraspherical.measure lam),
      gram lam alpha hlam ha f = mu • f ∧
        C lam alpha hlam ha f = F := by
  refine ⟨mu⁻¹ • C_adjoint lam alpha hlam ha F, ?_, ?_⟩
  · exact nonzero_output_eigenvector_source_preimage
      lam alpha hlam ha mu hmu F hF
  · rw [map_smul]
    exact nonzero_output_eigenvector_recovered
      lam alpha hlam ha mu hmu F hF

/-- C is injective when restricted to ANY fixed nonzero eigenspace
of the actual source Gram, regardless of its global kernel. -/
theorem C_injective_on_nonzero_gram_eigenvectors
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam))
    (hf : gram lam alpha hlam ha f = mu • f)
    (hg : gram lam alpha hlam ha g = mu • g)
    (hfg : C lam alpha hlam ha f = C lam alpha hlam ha g) :
    f = g := by
  calc
    f = mu⁻¹ • C_adjoint lam alpha hlam ha
        (C lam alpha hlam ha f) :=
      (nonzero_source_eigenvector_recovered
        lam alpha hlam ha mu hmu f hf).symm
    _ = mu⁻¹ • C_adjoint lam alpha hlam ha
        (C lam alpha hlam ha g) := by rw [hfg]
    _ = g := nonzero_source_eigenvector_recovered
      lam alpha hlam ha mu hmu g hg

/-- Pointwise bijection: an output eigenvector for mu ≠ 0 has
exactly one source eigenvector mapping to it under C. -/
theorem nonzero_output_eigenvector_unique_source
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0)
    (F : InfiniteAnalysis.FockCoefficients)
    (hF : outputGram lam alpha hlam ha F = mu • F) :
    ∃! f : Lp ℂ 2 (Ultraspherical.measure lam),
      gram lam alpha hlam ha f = mu • f ∧
        C lam alpha hlam ha f = F := by
  obtain ⟨f, hf, hCf⟩ :=
    nonzero_output_eigenvector_has_source
      lam alpha hlam ha mu hmu F hF
  refine ⟨f, ⟨hf, hCf⟩, ?_⟩
  intro g hg
  exact C_injective_on_nonzero_gram_eigenvectors
    lam alpha hlam ha mu hmu g f hg.1 hf (hg.2.trans hCf.symm)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.nonzero_source_eigenvector_recovered
#print axioms GegenbauerFock.GeneralUltrasphericalFock.nonzero_output_eigenvector_recovered
#print axioms GegenbauerFock.GeneralUltrasphericalFock.nonzero_output_eigenvector_source_preimage
#print axioms GegenbauerFock.GeneralUltrasphericalFock.nonzero_output_eigenvector_has_source
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_injective_on_nonzero_gram_eigenvectors
#print axioms GegenbauerFock.GeneralUltrasphericalFock.nonzero_output_eigenvector_unique_source

end GegenbauerFock.GeneralUltrasphericalFock
