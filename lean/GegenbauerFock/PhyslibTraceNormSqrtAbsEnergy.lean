import GegenbauerFock.PhyslibTraceClassHSFactorization
import GegenbauerFock.PhyslibTraceBasisIndependence

/-!
# V007 — exact square-root Hilbert–Schmidt energy of arbitrary CFC trace norm

On any complete complex Hilbert space, the actual source-compatible Physlib
trace norm of an arbitrary (possibly non-selfadjoint) trace-class endomorphism
T equals the squared Hilbert–Schmidt basis energy of sqrt(|T|).
This is valid on EVERY complete Hilbert basis.  It requires no finite-rank
hypothesis, positivity of T, or particular ultraspherical kernel.

This module is a prerequisite for the full trace-norm triangle inequality.
No normed/Banach structure is claimed here.
-/

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every complete Hilbert basis computes the genuine CFC trace norm
as the squared source-basis energy of the positive square root of |T|. -/
theorem traceNorm_eq_sqrt_abs_basisEnergy
    (T : H →L[ℂ] H) (hT : IsTraceClass T)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    traceNorm T hT =
      ∑' i : w, ‖(CFC.sqrt (CFC.abs T)) (b i)‖ ^ 2 := by
  let A : H →L[ℂ] H := CFC.abs T
  let S : H →L[ℂ] H := CFC.sqrt A
  have hA : 0 ≤ A := CFC.abs_nonneg T
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA
  have hSstar : ContinuousLinearMap.adjoint S = S :=
    (ContinuousLinearMap.star_eq_adjoint S).symm.trans
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A))
  calc
    traceNorm T hT =
        ∑' i : w, (inner ℂ (b i) (A (b i))).re :=
      traceNorm_eq_of_hilbertBasis hT b
    _ = ∑' i : w, ‖S (b i)‖ ^ 2 := by
      apply tsum_congr
      intro i
      have hi : inner ℂ (b i) (A (b i)) =
          inner ℂ (S (b i)) (S (b i)) := by
        rw [← hSS]
        show inner ℂ (b i) ((S * S) (b i)) =
          inner ℂ (S (b i)) (S (b i))
        rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
        rw [← ContinuousLinearMap.adjoint_inner_left S (S (b i)) (b i),
          hSstar]
      rw [hi, inner_self_eq_norm_sq_to_K]
      norm_cast
    _ = ∑' i : w, ‖(CFC.sqrt (CFC.abs T)) (b i)‖ ^ 2 := rfl

/-- The square-root energy series is summable on EVERY complete basis,
not just the existential one in the trace-class witness. -/
theorem summable_sqrt_abs_basisEnergy
    (T : H →L[ℂ] H) (hT : IsTraceClass T)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    Summable (fun i : w => ‖(CFC.sqrt (CFC.abs T)) (b i)‖ ^ 2) := by
  obtain ⟨w₀, b₀, hs⟩ := traceClass_sqrt_abs_isHS T hT
  exact (hasSum_norm_sq_apply_of_selfAdjoint
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (CFC.abs T)))
    b₀ b hs).summable

#print axioms ProbabilisticTheory.traceNorm_eq_sqrt_abs_basisEnergy
#print axioms ProbabilisticTheory.summable_sqrt_abs_basisEnergy

end ProbabilisticTheory
