import GegenbauerFock.CanonicalCFCSpectralCutoffStrongRecovery
import GegenbauerFock.CanonicalCFCRootPolarCutoffStrongRecovery
import GegenbauerFock.CanonicalCFCSourceGramCutoffStrongRecovery
import GegenbauerFock.CanonicalCFCRootOperatorNormReconstructionObstruction

/-!
# V007 — constructive strong recovery with the sharp uniform obstruction

Finite singular spectral cutoffs recover every fixed source vector
from the actual CFC polar root, Gegenbauer–Fock map and Gram.
Nevertheless every bounded cutoff reconstructing any of the three
maps has operator-norm error at least one, and therefore there is
no uniform unit-ball recovery.

This states both mathematically distinct facts in the same genuine
infinite-dimensional operator context, without a positive spectral gap.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

private abbrev StrongRecoveryH (lam : ℝ) :=
  Lp ℂ 2 (Ultraspherical.measure lam)

/-- The actual Fock map has a bounded spectral-cutoff family
converging pointwise on every source vector, while the reconstruction
error is >=1 in operator norm for every individual cutoff. -/
theorem exists_Fock_strongCutoff_and_sharp_uniform_obstruction
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (R : Finset ι →
        InfiniteAnalysis.FockCoefficients →L[ℂ] StrongRecoveryH lam),
      (∀ f : StrongRecoveryH lam,
        Tendsto (fun s : Finset ι => R s (C lam alpha hlam ha f))
          atTop (nhds f)) ∧
      (∀ s : Finset ι, (1 : ℝ) ≤
        ‖(ContinuousLinearMap.id ℂ (StrongRecoveryH lam)) -
          (R s).comp (C lam alpha hlam ha)‖) := by
  obtain ⟨ι, R, hstrong⟩ :=
    exists_C_singularCutoff_strong_recovery lam alpha hlam ha
  obtain ⟨_hP, hC, _hG⟩ :=
    cfc_fock_gram_uniform_reconstruction_error_ge_one lam alpha hlam ha
  exact ⟨ι, R, hstrong, fun s => hC (R s)⟩

/-- The canonical CFC root P of the genuine source Gram also admits
strong recovery by bounded polar spectral cutoffs, without uniform
operator-norm recovery on the whole source unit sphere. -/
theorem exists_CFCroot_strongCutoff_and_sharp_uniform_obstruction
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (R : Finset ι → StrongRecoveryH lam →L[ℂ] StrongRecoveryH lam),
      (∀ f : StrongRecoveryH lam,
        Tendsto
          (fun s : Finset ι => R s (localCFCGramSqrt lam alpha hlam ha f))
          atTop (nhds f)) ∧
      (∀ s : Finset ι, (1 : ℝ) ≤
        ‖(ContinuousLinearMap.id ℂ (StrongRecoveryH lam)) -
          (R s).comp (localCFCGramSqrt lam alpha hlam ha)‖) := by
  obtain ⟨ι, R, hstrong⟩ :=
    exists_localCFC_polarCutoff_strong_recovery lam alpha hlam ha
  obtain ⟨hP, _hC, _hG⟩ :=
    cfc_fock_gram_uniform_reconstruction_error_ge_one lam alpha hlam ha
  exact ⟨ι, R, hstrong, fun s => hP (R s)⟩

/-- The genuine source Gram has a positive-eigenvalue inverse cutoff
family converging strongly, but every bounded cutoff still has a
uniform reconstruction error of at least one. -/
theorem exists_sourceGram_strongCutoff_and_sharp_uniform_obstruction
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (R : Finset ι → StrongRecoveryH lam →L[ℂ] StrongRecoveryH lam),
      (∀ f : StrongRecoveryH lam,
        Tendsto
          (fun s : Finset ι => R s (gram lam alpha hlam ha f))
          atTop (nhds f)) ∧
      (∀ s : Finset ι, (1 : ℝ) ≤
        ‖(ContinuousLinearMap.id ℂ (StrongRecoveryH lam)) -
          (R s).comp (gram lam alpha hlam ha)‖) := by
  obtain ⟨ι, R, hstrong⟩ :=
    exists_sourceGram_cutoff_strong_recovery lam alpha hlam ha
  obtain ⟨_hP, _hC, hG⟩ :=
    cfc_fock_gram_uniform_reconstruction_error_ge_one lam alpha hlam ha
  exact ⟨ι, R, hstrong, fun s => hG (R s)⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_Fock_strongCutoff_and_sharp_uniform_obstruction
#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_CFCroot_strongCutoff_and_sharp_uniform_obstruction
#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_sourceGram_strongCutoff_and_sharp_uniform_obstruction

end GegenbauerFock.GeneralUltrasphericalFock
