import GegenbauerFock.PhyslibTraceBasisIndependence

/-!
# V007 — monotonicity of the genuine positive CFC trace norm

On any complete complex Hilbert space, the trace norm of positive
source-compatible trace-class operators respects the Loewner order.
This uses the true functional-calculus absolute value, basis-independent
summable diagonals and positivity of the operator difference.

The result is not the general triangle inequality, and does not assume
Banach completeness, finite rank, commuting operators, or a common
preselected trace-class witness basis.
-/

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual CFC trace norm is monotone under Loewner order on
positive trace-class endomorphisms, in arbitrary Hilbert dimension. -/
theorem positive_traceNorm_mono_v007
    (T V : H →L[ℂ] H)
    (hT : 0 ≤ T) (hV : 0 ≤ V) (hTV : T ≤ V)
    (ht : IsTraceClass T) (hv : IsTraceClass V) :
    traceNorm T ht ≤ traceNorm V hv := by
  let w : Set H := ht.choose
  let b : HilbertBasis w ℂ H := ht.choose_spec.choose
  have hsT : Summable (fun i : w => (inner ℂ (b i) (T (b i))).re) := by
    simpa only [CFC.abs_of_nonneg T hT] using
      (summable_inner_abs_of_hilbertBasis ht b)
  have hsV : Summable (fun i : w => (inner ℂ (b i) (V (b i))).re) := by
    simpa only [CFC.abs_of_nonneg V hV] using
      (summable_inner_abs_of_hilbertBasis hv b)
  have hpoint (i : w) :
      (inner ℂ (b i) (T (b i))).re ≤
        (inner ℂ (b i) (V (b i))).re := by
    have hdiff : 0 ≤ V - T := sub_nonneg.mpr hTV
    have hp :=
      ((ContinuousLinearMap.nonneg_iff_isPositive).mp hdiff).re_inner_nonneg_right (b i)
    change 0 ≤ (inner ℂ (b i) ((V - T) (b i))).re at hp
    simp only [ContinuousLinearMap.sub_apply, inner_sub_right,
      Complex.sub_re] at hp
    exact sub_nonneg.mp hp
  calc
    traceNorm T ht =
        ∑' i : w, (inner ℂ (b i) (CFC.abs T (b i))).re :=
      traceNorm_eq_of_hilbertBasis ht b
    _ = ∑' i : w, (inner ℂ (b i) (T (b i))).re := by
      simp only [CFC.abs_of_nonneg T hT]
    _ ≤ ∑' i : w, (inner ℂ (b i) (V (b i))).re :=
      hsT.tsum_le_tsum hpoint hsV
    _ = traceNorm V hv := by
      rw [traceNorm_eq_of_hilbertBasis hv b, CFC.abs_of_nonneg V hV]

#print axioms ProbabilisticTheory.positive_traceNorm_mono_v007

end ProbabilisticTheory
