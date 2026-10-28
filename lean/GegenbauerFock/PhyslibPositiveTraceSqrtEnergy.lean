import GegenbauerFock.PhyslibTraceClassHSFactorization
import GegenbauerFock.PhyslibTraceBasisIndependence

/-!
# V007 — exact positive trace norm as Hilbert–Schmidt square-root energy

For an arbitrary positive source-compatible trace-class endomorphism T
of an arbitrary complete complex Hilbert space, the true CFC trace norm
is the squared Hilbert–Schmidt energy of sqrt(T) on EVERY complete basis.

This is a necessary intermediate lemma for a general positive-conjugation
S₁ trace-norm bound. It asserts neither the unrestricted triangle
inequality nor completeness of the S₁ Banach type.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every basis gives exactly the same CFC trace norm of a positive
trace-class operator, computed as the squared norm of its true
functional-calculus square root on that basis. -/
theorem positive_traceNorm_eq_sqrt_basis_energy
    (T : H →L[ℂ] H) (hT : 0 ≤ T) (htr : IsTraceClass T)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    traceNorm T htr =
      ∑' i : w, ‖(CFC.sqrt T) (b i)‖ ^ 2 := by
  let S : H →L[ℂ] H := CFC.sqrt T
  have hsquare : S * S = T := CFC.sqrt_mul_sqrt_self T hT
  have hSstar : ContinuousLinearMap.adjoint S = S :=
    (ContinuousLinearMap.star_eq_adjoint S).symm.trans
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T))
  calc
    traceNorm T htr =
        ∑' i : w, (inner ℂ (b i) (CFC.abs T (b i))).re :=
      traceNorm_eq_of_hilbertBasis htr b
    _ = ∑' i : w, ‖S (b i)‖ ^ 2 := by
      apply tsum_congr
      intro i
      rw [CFC.abs_of_nonneg T hT, ← hsquare]
      change (inner ℂ (b i) (S (S (b i)))).re = ‖S (b i)‖ ^ 2
      rw [← ContinuousLinearMap.adjoint_inner_left S (S (b i)) (b i),
        hSstar, inner_self_eq_norm_sq_to_K]
      norm_cast
    _ = ∑' i : w, ‖(CFC.sqrt T) (b i)‖ ^ 2 := rfl

#print axioms ProbabilisticTheory.positive_traceNorm_eq_sqrt_basis_energy

end ProbabilisticTheory
