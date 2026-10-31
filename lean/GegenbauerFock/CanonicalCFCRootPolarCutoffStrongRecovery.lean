import GegenbauerFock.CanonicalCFCSpectralCutoffStrongRecovery
import GegenbauerFock.LocalCFCGramSquareRoot

/-!
# V007 — strongly convergent regularization of the canonical CFC root

The actual compact canonical CFC Gram square root P has the full
unitary polar factorization C = W P. Any bounded finite-cutoff
reconstruction of the actual Fock transform C therefore induces a
bounded finite-cutoff reconstruction for P by composing with W.

The result holds on the entire infinite ultraspherical L² source.
It is pointwise strong convergence, not norm convergence of
bounded-operator inverses.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- A family of bounded linear maps applied to the genuine
canonical positive CFC Gram square root recovers every source
in strong L² as finite cutoff sets increase. -/
theorem exists_localCFC_polarCutoff_strong_recovery
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (R : Finset ι →
        Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam)),
      ∀ (f : Lp ℂ 2 (Ultraspherical.measure lam)),
        Tendsto
          (fun s : Finset ι =>
            R s (localCFCGramSqrt lam alpha hlam ha f))
          atTop (nhds f) := by
  obtain ⟨W, _hcompact, _hinj, _hdense, _hnotclosed, hpolar⟩ :=
    exists_local_cfc_sqrt_compact_dense_nonclosed
      lam alpha hlam ha
  obtain ⟨ι, R, hR⟩ :=
    exists_C_singularCutoff_strong_recovery lam alpha hlam ha
  refine ⟨ι, (fun s => (R s).comp W.toContinuousLinearMap), ?_⟩
  intro f
  have heq :
      (fun s : Finset ι =>
        ((R s).comp W.toContinuousLinearMap)
          (localCFCGramSqrt lam alpha hlam ha f)) =
      (fun s : Finset ι => R s (C lam alpha hlam ha f)) := by
    funext s
    change R s (W (localCFCGramSqrt lam alpha hlam ha f)) =
      R s (C lam alpha hlam ha f)
    rw [hpolar f]
  change Tendsto
    (fun s : Finset ι =>
      ((R s).comp W.toContinuousLinearMap)
        (localCFCGramSqrt lam alpha hlam ha f))
    atTop (nhds f)
  rw [heq]
  exact hR f

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_localCFC_polarCutoff_strong_recovery

end GegenbauerFock.GeneralUltrasphericalFock
