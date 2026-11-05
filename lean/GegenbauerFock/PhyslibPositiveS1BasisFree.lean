import GegenbauerFock.PhyslibTraceBasisIndependence

/-!
# V007 — arbitrary positive S₁ additive closure, no common-basis hypothesis

For *any* complete complex Hilbert space, two positive trace-class
endomorphisms sum to a positive trace-class endomorphism, and the
genuine CFC trace norm is exactly additive. Unlike the earlier
fixed-basis positive-cone theorem, the operator hypotheses here
are intrinsically basis independent. The new proof uses the
certified basis-change/trace-norm equality.

This is not unrestricted nonpositive S₁ addition; the latter
requires the polar-factor/HS-product bridge.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Any two positive S₁ operators have a trace-class sum,
without providing or selecting a common witness basis in the assumptions. -/
theorem isTraceClass_add_of_nonneg
    (A B : H →L[ℂ] H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hTA : IsTraceClass A) (hTB : IsTraceClass B) :
    IsTraceClass (A + B) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hsA : Summable (fun i : w => (inner ℂ (b i) (A (b i))).re) := by
    simpa only [CFC.abs_of_nonneg A hA] using
      (summable_inner_abs_of_hilbertBasis hTA b)
  have hsB : Summable (fun i : w => (inner ℂ (b i) (B (b i))).re) := by
    simpa only [CFC.abs_of_nonneg B hB] using
      (summable_inner_abs_of_hilbertBasis hTB b)
  apply isTraceClass_of_nonneg_of_summable
    (A + B) (add_nonneg hA hB) b
  simpa only [ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re] using
    hsA.add hsB

/-- Exact CFC trace-norm additivity on the entire positive S₁ cone,
with no shared witness-basis assumption on the two input operators. -/
theorem traceNorm_add_of_nonneg
    (A B : H →L[ℂ] H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hTA : IsTraceClass A) (hTB : IsTraceClass B) :
    traceNorm (A + B) (isTraceClass_add_of_nonneg A B hA hB hTA hTB) =
      traceNorm A hTA + traceNorm B hTB := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hsA : Summable (fun i : w => (inner ℂ (b i) (A (b i))).re) := by
    simpa only [CFC.abs_of_nonneg A hA] using
      (summable_inner_abs_of_hilbertBasis hTA b)
  have hsB : Summable (fun i : w => (inner ℂ (b i) (B (b i))).re) := by
    simpa only [CFC.abs_of_nonneg B hB] using
      (summable_inner_abs_of_hilbertBasis hTB b)
  calc
    traceNorm (A + B) (isTraceClass_add_of_nonneg A B hA hB hTA hTB) =
      ∑' i : w, (inner ℂ (b i) ((A + B) (b i))).re := by
        rw [traceNorm_eq_of_hilbertBasis
          (isTraceClass_add_of_nonneg A B hA hB hTA hTB) b,
          CFC.abs_of_nonneg (A + B) (add_nonneg hA hB)]
    _ = (∑' i : w, (inner ℂ (b i) (A (b i))).re) +
        (∑' i : w, (inner ℂ (b i) (B (b i))).re) := by
          simpa only [ContinuousLinearMap.add_apply, inner_add_right,
            Complex.add_re] using hsA.tsum_add hsB
    _ = traceNorm A hTA + traceNorm B hTB := by
          rw [traceNorm_eq_of_hilbertBasis hTA b,
            traceNorm_eq_of_hilbertBasis hTB b,
            CFC.abs_of_nonneg A hA, CFC.abs_of_nonneg B hB]

#print axioms ProbabilisticTheory.isTraceClass_add_of_nonneg
#print axioms ProbabilisticTheory.traceNorm_add_of_nonneg

end ProbabilisticTheory
