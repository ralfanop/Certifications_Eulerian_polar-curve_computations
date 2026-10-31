import GegenbauerFock.SingularNonzeroEigenspaceCorrespondence

/-!
# V007 — linear equivalence of the nonzero singular eigenspaces

The actual Gegenbauer--Fock operator C restricts to a complex-linear
bijection between the mu-eigenspaces of C†C and CC† when mu ≠ 0.
Its inverse is mu⁻¹ C†. Consequently, the two nonzero eigenspaces
have equal algebraic dimensions (including eigenvalue multiplicity).

No hypothesis of global injectivity or dense range is introduced.
The zero eigenspaces and global spectral enumeration remain separate.
-/

noncomputable section

open Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- The genuine Gegenbauer--Fock map restricts to a linear map
between the source and coefficient-side Gram mu-eigenspaces. -/
noncomputable def C_nonzero_eigenspace_linearMap
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) :
    eigenspace (gram lam alpha hlam ha).toLinearMap mu →ₗ[ℂ]
      eigenspace (outputGram lam alpha hlam ha).toLinearMap mu where
  toFun f :=
    ⟨C lam alpha hlam ha f.1,
      mem_eigenspace_iff.mpr
        (C_maps_gram_eigenvector lam alpha hlam ha mu f.1
          (mem_eigenspace_iff.mp f.2))⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add (C lam alpha hlam ha) f.1 g.1
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (C lam alpha hlam ha) c f.1

/-- The restriction is a genuine linear equivalence between the two
nonzero eigenspaces, not merely an equivalence of their spectra. -/
noncomputable def C_nonzero_eigenspace_linearEquiv
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    eigenspace (gram lam alpha hlam ha).toLinearMap mu ≃ₗ[ℂ]
      eigenspace (outputGram lam alpha hlam ha).toLinearMap mu := by
  apply LinearEquiv.ofBijective
    (C_nonzero_eigenspace_linearMap lam alpha hlam ha mu)
  constructor
  · intro f g hfg
    apply Subtype.ext
    exact C_injective_on_nonzero_gram_eigenvectors
      lam alpha hlam ha mu hmu f.1 g.1
      (mem_eigenspace_iff.mp f.2)
      (mem_eigenspace_iff.mp g.2)
      (congrArg Subtype.val hfg)
  · intro F
    obtain ⟨f, hf, hCf⟩ :=
      nonzero_output_eigenvector_has_source
        lam alpha hlam ha mu hmu F.1
        (mem_eigenspace_iff.mp F.2)
    refine ⟨⟨f, mem_eigenspace_iff.mpr hf⟩, ?_⟩
    apply Subtype.ext
    exact hCf

/-- The forward linear equivalence is the ORIGINAL operator C,
without any spectral truncation or replacement by a model. -/
theorem C_nonzero_eigenspace_linearEquiv_apply
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0)
    (f : eigenspace (gram lam alpha hlam ha).toLinearMap mu) :
    (C_nonzero_eigenspace_linearEquiv lam alpha hlam ha mu hmu f).1 =
      C lam alpha hlam ha f.1 := rfl

/-- Each nonzero Gram eigenvalue has the SAME algebraic multiplicity
on the ultraspherical L² and Fock-coefficient Hilbert spaces. -/
theorem C_nonzero_eigenspace_finrank_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    Module.finrank ℂ (eigenspace (gram lam alpha hlam ha).toLinearMap mu) =
      Module.finrank ℂ (eigenspace (outputGram lam alpha hlam ha).toLinearMap mu) :=
  LinearEquiv.finrank_eq
    (C_nonzero_eigenspace_linearEquiv lam alpha hlam ha mu hmu)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_nonzero_eigenspace_linearMap
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_nonzero_eigenspace_linearEquiv
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_nonzero_eigenspace_linearEquiv_apply
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_nonzero_eigenspace_finrank_eq

end GegenbauerFock.GeneralUltrasphericalFock
