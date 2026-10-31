import GegenbauerFock.CanonicalCFCRootOperatorNormReconstructionObstruction
import Mathlib.Topology.Order.OrderClosed

/-!
# V007 — no operator-norm consistent family of bounded reconstructions

The proved sharp lower bound ‖id - R ∘ T‖ ≥ 1 holds separately for every
bounded reconstruction R. Consequently it cannot tend to zero in
operator norm along any sequence of regularization parameters.

This DOES NOT exclude strong operator convergence of appropriately
regularized reconstructions. It only rules out uniform reconstruction
over the full unit ball of the source Hilbert space.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Abstract corollary: a uniform error-one lower bound prevents any
sequence of bounded linear reconstructions from converging to the
identity in operator norm. -/
theorem no_opNorm_consistent_reconstruction_sequence_of_lower_bound
    {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (T : H →L[ℂ] K)
    (hbound : ∀ (R : K →L[ℂ] H),
      (1 : ℝ) ≤ ‖(ContinuousLinearMap.id ℂ H) - R.comp T‖)
    (R : ℕ → (K →L[ℂ] H)) :
    ¬ Filter.Tendsto
      (fun n : ℕ => (ContinuousLinearMap.id ℂ H) - (R n).comp T)
      Filter.atTop (nhds (0 : H →L[ℂ] H)) := by
  intro h
  have hnorm : Filter.Tendsto
      (fun n : ℕ => ‖(ContinuousLinearMap.id ℂ H) - (R n).comp T‖)
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa using h.norm
  have hbad : (1 : ℝ) ≤ 0 :=
    ge_of_tendsto' hnorm (fun n => hbound (R n))
  norm_num at hbad

private abbrev RecoveryH (lam : ℝ) :=
  Lp ℂ 2 (Ultraspherical.measure lam)

/-- Neither the canonical CFC root, the true Fock analysis map nor
the source Gram admits a sequence of bounded linear left
regularizers converging to the source identity in operator norm. -/
theorem cfc_fock_gram_no_opNorm_consistent_reconstruction_sequence
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∀ (R : ℕ → (RecoveryH lam →L[ℂ] RecoveryH lam)),
      ¬ Filter.Tendsto
        (fun n : ℕ =>
          (ContinuousLinearMap.id ℂ (RecoveryH lam)) -
            (R n).comp (localCFCGramSqrt lam alpha hlam ha))
        Filter.atTop (nhds (0 : RecoveryH lam →L[ℂ] RecoveryH lam))) ∧
    (∀ (R : ℕ → (InfiniteAnalysis.FockCoefficients →L[ℂ] RecoveryH lam)),
      ¬ Filter.Tendsto
        (fun n : ℕ =>
          (ContinuousLinearMap.id ℂ (RecoveryH lam)) -
            (R n).comp (C lam alpha hlam ha))
        Filter.atTop (nhds (0 : RecoveryH lam →L[ℂ] RecoveryH lam))) ∧
    (∀ (R : ℕ → (RecoveryH lam →L[ℂ] RecoveryH lam)),
      ¬ Filter.Tendsto
        (fun n : ℕ =>
          (ContinuousLinearMap.id ℂ (RecoveryH lam)) -
            (R n).comp (gram lam alpha hlam ha))
        Filter.atTop (nhds (0 : RecoveryH lam →L[ℂ] RecoveryH lam))) := by
  obtain ⟨hP, hC, hG⟩ :=
    cfc_fock_gram_uniform_reconstruction_error_ge_one
      lam alpha hlam ha
  refine ⟨?_, ?_, ?_⟩
  · intro R
    exact no_opNorm_consistent_reconstruction_sequence_of_lower_bound
      (localCFCGramSqrt lam alpha hlam ha) hP R
  · intro R
    exact no_opNorm_consistent_reconstruction_sequence_of_lower_bound
      (C lam alpha hlam ha) hC R
  · intro R
    exact no_opNorm_consistent_reconstruction_sequence_of_lower_bound
      (gram lam alpha hlam ha) hG R

#print axioms GegenbauerFock.GeneralUltrasphericalFock.no_opNorm_consistent_reconstruction_sequence_of_lower_bound
#print axioms GegenbauerFock.GeneralUltrasphericalFock.cfc_fock_gram_no_opNorm_consistent_reconstruction_sequence

end GegenbauerFock.GeneralUltrasphericalFock
