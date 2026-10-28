/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache-2.0.
Adapted to V007 pinned Lean and Mathlib from PhyslibAlpha
ProbabilisticTheory/HilbertSpace/TraceClass/Banach.lean.
-/
import GegenbauerFock.PhyslibTraceNormLowerSemicontinuity
import GegenbauerFock.PhyslibTraceClassNormedSpace

/-!
# V007 — candidate Banach completion of actual CFC Schatten S₁

The genuine trace-normed complex vector space from previous
modules is complete: absolutely summable series converge in trace
norm. The argument uses operator-norm completeness and a uniform
trace-norm limit bound from lower semicontinuity. No finite-rank
or ultraspherical-specific assumptions are needed.

This is an independent candidate pending pinned Lean compilation,
complete workflow SUCCESS and #print axioms audit. It does NOT
alter any previously certified checkpoints.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem v007_traceNorm_transport {X Y : H →L[ℂ] H}
    (hEq : X = Y) (hX : IsTraceClass X) :
    traceNorm X hX = traceNorm Y (hEq ▸ hX) := by
  subst hEq
  rfl

namespace TraceClass

/-- Local aliases matching the source-compatible subtype semantics. -/
private theorem isTraceClass_coe (T : TraceClass H) : IsTraceClass T.1 := T.2

private theorem norm_eq_traceNorm (T : TraceClass H) :
    ‖T‖ = ProbabilisticTheory.traceNorm T.1 T.2 := rfl

noncomputable instance instGenuineCompleteSpace : CompleteSpace (TraceClass H) := by
  apply NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
  intro u hu
  set psum : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, ‖u i‖ with hpartialdef
  set M : ℝ := ∑' n, ‖u n‖ with hMdef
  set Sn : ℕ → TraceClass H := fun n => ∑ i ∈ Finset.range n, u i with hSndef
  set Tn : ℕ → H →L[ℂ] H := fun n => (Sn n).1 with hTndef
  have hpartial_le_M : ∀ n, psum n ≤ M := fun n => hu.sum_le_tsum _ (fun i _ => norm_nonneg _)
  have hpartial_tendsto : Tendsto psum atTop (𝓝 M) := hu.hasSum.tendsto_sum_nat
  set tail : ℕ → ℝ := fun n => M - psum n with htaildef
  have htail_tendsto : Tendsto tail atTop (𝓝 0) := by
    have := hpartial_tendsto.const_sub M
    simpa [htaildef] using this
  have hSn_diff : ∀ n m : ℕ, n ≤ m → Sn m - Sn n = ∑ i ∈ Finset.Ico n m, u i := by
    intro n m hnm
    simp only [hSndef]
    rw [Finset.sum_Ico_eq_sub _ hnm]
  have hpsum_split : ∀ n m : ℕ, n ≤ m →
      (∑ i ∈ Finset.Ico n m, ‖u i‖) = psum m - psum n := by
    intro n m hnm
    simp only [hpartialdef]
    rw [Finset.sum_Ico_eq_sub _ hnm]
  have htrace_tail_bound : ∀ n m : ℕ, n ≤ m → ‖Sn m - Sn n‖ ≤ tail n := by
    intro n m hnm
    rw [hSn_diff n m hnm]
    calc ‖∑ i ∈ Finset.Ico n m, u i‖ ≤ ∑ i ∈ Finset.Ico n m, ‖u i‖ := norm_sum_le _ _
      _ = psum m - psum n := hpsum_split n m hnm
      _ ≤ tail n := by simp only [htaildef]; linarith [hpartial_le_M m]
  have hSn_diff_coe : ∀ n m : ℕ, ((Sn m - Sn n : TraceClass H)).1 = Tn m - Tn n :=
    fun n m => sub_operator (Sn m) (Sn n)
  have htn_cauchy : CauchySeq Tn := by
    apply cauchySeq_of_le_tendsto_0' tail _ htail_tendsto
    intro n m hnm
    rw [dist_eq_norm]
    have heqop : Tn n - Tn m = -(Tn m - Tn n) := by abel
    rw [heqop, norm_neg, ← hSn_diff_coe n m]
    calc ‖((Sn m - Sn n : TraceClass H)).1‖ ≤ ‖(Sn m - Sn n : TraceClass H)‖ :=
          operatorNorm_le_traceNorm_via_sqrt_abs (isTraceClass_coe (Sn m - Sn n))
      _ ≤ tail n := htrace_tail_bound n m hnm
  obtain ⟨S, hStendsto⟩ := cauchySeq_tendsto_of_complete htn_cauchy
  have hSn_bound : ∀ n, traceNorm (Sn n).1 (isTraceClass_coe (Sn n)) ≤ M := by
    intro n
    show ‖Sn n‖ ≤ M
    calc ‖Sn n‖ ≤ ∑ i ∈ Finset.range n, ‖u i‖ := by
          simp only [hSndef]; exact norm_sum_le _ _
      _ = psum n := rfl
      _ ≤ M := hpartial_le_M n
  obtain ⟨hS, -⟩ := isTraceClass_of_tendsto_of_traceNorm_bounded_v007
    (fun n => isTraceClass_coe (Sn n)) hSn_bound hStendsto
  refine ⟨ofOperator H S hS, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound_S : ∀ n, dist (Sn n) (ofOperator H S hS : TraceClass H) ≤ tail n := by
    intro n
    rw [dist_eq_norm]
    have hVtrace : ∀ m, IsTraceClass (Tn (n + m) - Tn n) := by
      intro m
      rw [← hSn_diff_coe n (n + m)]
      exact isTraceClass_coe (Sn (n + m) - Sn n)
    have hVbound : ∀ m, traceNorm (Tn (n + m) - Tn n) (hVtrace m) ≤ tail n := by
      intro m
      have h1 : traceNorm (Tn (n + m) - Tn n) (hVtrace m) =
          traceNorm ((Sn (n + m) - Sn n : TraceClass H)).1
            (isTraceClass_coe (Sn (n + m) - Sn n)) := by
        have hEq : Tn (n + m) - Tn n = ((Sn (n + m) - Sn n : TraceClass H)).1 :=
          (hSn_diff_coe n (n + m)).symm
        exact v007_traceNorm_transport hEq (hVtrace m)
      rw [h1]
      show ‖Sn (n + m) - Sn n‖ ≤ tail n
      exact htrace_tail_bound n (n + m) (Nat.le_add_right n m)
    have hVtendsto : Tendsto (fun m => Tn (n + m) - Tn n) atTop (𝓝 (S - Tn n)) := by
      have h1 : Tendsto (fun m => Tn (n + m)) atTop (𝓝 S) := by
        have h2 : Tendsto (fun m => Tn (m + n)) atTop (𝓝 S) :=
          hStendsto.comp (tendsto_add_atTop_nat n)
        simpa only [add_comm] using h2
      exact h1.sub tendsto_const_nhds
    obtain ⟨hSTn, hSTnbound⟩ := isTraceClass_of_tendsto_of_traceNorm_bounded_v007 hVtrace hVbound
      hVtendsto
    have heqfinal : ((ofOperator H S hS : TraceClass H) - Sn n).1 = S - Tn n := rfl
    have hnorm_eq : ‖(ofOperator H S hS : TraceClass H) - Sn n‖ = traceNorm (S - Tn n) hSTn := by
      have h3 : ‖(ofOperator H S hS : TraceClass H) - Sn n‖ =
          traceNorm ((ofOperator H S hS : TraceClass H) - Sn n).1
            (isTraceClass_coe ((ofOperator H S hS : TraceClass H) - Sn n)) := rfl
      rw [h3]
      exact v007_traceNorm_transport heqfinal (isTraceClass_coe ((ofOperator H S hS : TraceClass H) - Sn
          n))
    rw [norm_sub_rev]
    rw [hnorm_eq]
    exact hSTnbound
  exact squeeze_zero (fun n => dist_nonneg) hbound_S htail_tendsto


end TraceClass
end ProbabilisticTheory
