import GegenbauerFock.PhyslibTraceClassNormedSpace

/-!
# V007 — quantitative embedding of Schatten S₁ into bounded operators

This is the first metric bridge required for Banach completeness.
The map forgetting the trace-class witness is contractive: the
ambient operator norm is bounded by the CFC-absolute trace norm.
More strongly, distances between arbitrary trace-class elements
dominate the distances of their underlying bounded operators.

The result is **not** a proof of completeness of S₁. It only
provides the fundamental metric domination used to construct
operator-norm limits from S₁-Cauchy sequences. The required
trace-norm lower semicontinuity remains a separate obligation.

No change to existing certified modules, toolchains or V097.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass
open scoped Topology
open Filter

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The natural inclusion S₁(H) -> B(H) is contractive in norm. -/
theorem operator_norm_le_trace_norm (T : TraceClass H) :
    ‖T.1‖ ≤ ‖T‖ := by
  calc
    ‖T.1‖ ≤ ProbabilisticTheory.traceNorm T.1 T.2 :=
      ProbabilisticTheory.operatorNorm_le_traceNorm_via_sqrt_abs T.1 T.2
    _ = ‖T‖ := (norm_eq_genuineTraceNorm T).symm

/-- The operator-norm distance between arbitrary S₁ elements is
bounded by their genuine trace-norm distance. -/
theorem operator_sub_norm_le_trace_sub_norm (T V : TraceClass H) :
    ‖T.1 - V.1‖ ≤ ‖T - V‖ := by
  simpa only [sub_operator] using operator_norm_le_trace_norm (T - V)

/-- In particular the operator inclusion is nonexpansive for the
metrics induced by the respective norms. -/
theorem operator_dist_le_trace_dist (T V : TraceClass H) :
    dist T.1 V.1 ≤ dist T V := by
  simpa only [dist_eq_norm] using operator_sub_norm_le_trace_sub_norm T V

/-- The forgetful map from the genuine trace-normed Schatten S₁
space to the Banach space of bounded Hilbert operators is uniformly
continuous; it has nonexpansive modulus δ = ε. -/
theorem operator_uniformContinuous :
    UniformContinuous (operator H) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro T V hTV
  exact lt_of_le_of_lt (operator_dist_le_trace_dist T V) hTV

/-- Any trace-norm Cauchy sequence of CFC-trace-class operators has a
Cauchy sequence of underlying bounded operators. The existence of
the operator-norm limit uses completeness of B(H); trace-class
membership of that limit is a separate obligation. -/
theorem operator_cauchySeq_of_traceClass_cauchySeq
    {u : ℕ → TraceClass H} (hu : CauchySeq u) :
    CauchySeq (fun n => (u n).1) := by
  simpa only [Function.comp_def, operator] using
    (operator_uniformContinuous (H := H)).comp_cauchySeq hu

/-- Every trace-norm Cauchy sequence possesses an *operator-norm*
limit in the complete Banach space B(H). This does NOT yet establish
trace-class membership of that limit, which is the remaining
lower-semicontinuity/closedness part of S₁ completeness. -/
theorem exists_operator_limit_of_traceClass_cauchySeq
    {u : ℕ → TraceClass H} (hu : CauchySeq u) :
    ∃ T : H →L[ℂ] H,
      Tendsto (fun n => (u n).1) Filter.atTop (nhds T) :=
  cauchySeq_tendsto_of_complete
    (operator_cauchySeq_of_traceClass_cauchySeq hu)

/-- The operator-norm limit of an arbitrary S₁-Cauchy sequence
acts as its pointwise limit on *every* Hilbert vector. In
particular, the limit is a genuine bounded operator and not
merely a pointwise or weakly defined linear map. -/
theorem exists_pointwise_operator_limit_of_traceClass_cauchySeq
    {u : ℕ → TraceClass H} (hu : CauchySeq u) :
    ∃ T : H →L[ℂ] H,
      ∀ x : H, Tendsto (fun n => (u n).1 x) Filter.atTop (nhds (T x)) := by
  obtain ⟨T, hT⟩ := exists_operator_limit_of_traceClass_cauchySeq hu
  refine ⟨T, ?_⟩
  intro x
  have hev : Continuous (fun A : H →L[ℂ] H => A x) :=
    (ContinuousLinearMap.apply ℂ H x).continuous
  exact hev.continuousAt.tendsto.comp hT

/-- Operator-norm limits of the same S₁-Cauchy sequence are unique. -/
theorem traceClass_operator_limit_unique
    {u : ℕ → TraceClass H} {T V : H →L[ℂ] H}
    (hT : Tendsto (fun n => (u n).1) Filter.atTop (nhds T))
    (hV : Tendsto (fun n => (u n).1) Filter.atTop (nhds V)) :
    T = V :=
  tendsto_nhds_unique hT hV

#print axioms ProbabilisticTheory.TraceClass.operator_norm_le_trace_norm
#print axioms ProbabilisticTheory.TraceClass.operator_sub_norm_le_trace_sub_norm
#print axioms ProbabilisticTheory.TraceClass.operator_dist_le_trace_dist

#print axioms ProbabilisticTheory.TraceClass.operator_uniformContinuous
#print axioms ProbabilisticTheory.TraceClass.operator_cauchySeq_of_traceClass_cauchySeq
#print axioms ProbabilisticTheory.TraceClass.exists_operator_limit_of_traceClass_cauchySeq
#print axioms ProbabilisticTheory.TraceClass.exists_pointwise_operator_limit_of_traceClass_cauchySeq
#print axioms ProbabilisticTheory.TraceClass.traceClass_operator_limit_unique

end ProbabilisticTheory.TraceClass
