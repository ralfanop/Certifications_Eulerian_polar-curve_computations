import GegenbauerFock.GegenbauerIntrinsicEntireNonzeroSingularTransfer
import GegenbauerFock.SingularEigenspaceLinearEquiv

/-!
# V007 — genuine intrinsic Fock output eigenspace multiplicities

The certified onto Bargmann–Fock unitary U carries the coefficient
output Gram H = C C† to the genuine output Gram H_hol = C_hol C_hol†
on the closed intrinsic Gaussian L² space of entire representatives.
It thus induces a linear equivalence between eigenspaces at EVERY
complex scalar, not just an equivalence of spectral membership.

For a nonzero parameter, composition with the certified
ultraspherical-source Gram eigenspace equivalence gives an explicit
linear equivalence between the distinct actual source and
holomorphic output Hilbert-space eigenspaces. Consequently their
nonzero eigenvalue multiplicities agree exactly.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Unitary-coefficient transport on all eigenspaces, including zero:
the target is the real intrinsic entire Gaussian L² holomorphic space. -/
noncomputable def outputGram_intrinsicEntire_eigenspace_linearEquiv
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) :
    eigenspace (outputGram lam alpha hlam ha).toLinearMap mu ≃ₗ[ℂ]
      eigenspace (C_intrinsicEntire_outputGram lam alpha hlam ha).toLinearMap mu := by
  let U := GaussianArea.coefficientIntrinsicEntireEquiv alpha ha
  let Φ :
      eigenspace (outputGram lam alpha hlam ha).toLinearMap mu →ₗ[ℂ]
        eigenspace (C_intrinsicEntire_outputGram lam alpha hlam ha).toLinearMap mu :=
    { toFun := fun Fc => ⟨U Fc.1, by
        apply mem_eigenspace_iff.mpr
        change C_intrinsicEntire_outputGram lam alpha hlam ha (U Fc.1) =
          mu • U Fc.1
        rw [C_intrinsicEntire_outputGram_apply]
        change U (outputGram lam alpha hlam ha (U.symm (U Fc.1))) =
          mu • U Fc.1
        rw [U.symm_apply_apply, (mem_eigenspace_iff.mp Fc.2)]
        exact map_smul U mu Fc.1⟩
      map_add' := by
        intro Fc Gc
        apply Subtype.ext
        exact map_add U Fc.1 Gc.1
      map_smul' := by
        intro c Fc
        apply Subtype.ext
        exact map_smul U c Fc.1 }
  apply LinearEquiv.ofBijective Φ
  constructor
  · intro Fc Gc h
    apply Subtype.ext
    apply U.injective
    exact congrArg Subtype.val h
  · intro F
    have hF := mem_eigenspace_iff.mp F.2
    have h := congrArg U.symm hF
    rw [C_intrinsicEntire_outputGram_apply] at h
    change U.symm (U (outputGram lam alpha hlam ha (U.symm F.1))) =
      U.symm (mu • F.1) at h
    have hcoeff :
        outputGram lam alpha hlam ha (U.symm F.1) = mu • U.symm F.1 := by
      simpa only [U.symm_apply_apply, map_smul] using h
    refine ⟨⟨U.symm F.1, mem_eigenspace_iff.mpr hcoeff⟩, ?_⟩
    apply Subtype.ext
    exact U.apply_symm_apply F.1

/-- For every nonzero eigenvalue, the actual ultraspherical source
Gram and the genuine Bargmann–Fock output Gram eigenspaces are
linearly equivalent. The two Hilbert spaces remain distinct. -/
noncomputable def C_intrinsicEntire_nonzero_eigenspace_linearEquiv
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    eigenspace (C_intrinsicEntire_gram lam alpha hlam ha).toLinearMap mu ≃ₗ[ℂ]
      eigenspace (C_intrinsicEntire_outputGram lam alpha hlam ha).toLinearMap mu := by
  rw [C_intrinsicEntire_gram_eq lam alpha hlam ha]
  exact (C_nonzero_eigenspace_linearEquiv lam alpha hlam ha mu hmu).trans
    (outputGram_intrinsicEntire_eigenspace_linearEquiv lam alpha hlam ha mu)

/-- Exact equality of every nonzero eigenvalue's geometric
multiplicity for both genuine source/output Grams. -/
theorem C_intrinsicEntire_nonzero_eigenspace_finrank_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    Module.finrank ℂ
      (eigenspace (C_intrinsicEntire_gram lam alpha hlam ha).toLinearMap mu) =
    Module.finrank ℂ
      (eigenspace (C_intrinsicEntire_outputGram lam alpha hlam ha).toLinearMap mu) :=
  LinearEquiv.finrank_eq
    (C_intrinsicEntire_nonzero_eigenspace_linearEquiv lam alpha hlam ha mu hmu)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_intrinsicEntire_eigenspace_linearEquiv
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_nonzero_eigenspace_linearEquiv
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_nonzero_eigenspace_finrank_eq

end GegenbauerFock.GeneralUltrasphericalFock
