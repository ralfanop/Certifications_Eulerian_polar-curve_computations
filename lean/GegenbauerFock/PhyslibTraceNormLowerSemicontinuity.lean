/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache-2.0.
Source-compatible adaptation from PhyslibAlpha's
ProbabilisticTheory/HilbertSpace/TraceClass/Banach.lean.
-/
import GegenbauerFock.PhyslibTraceNormTriangleYoung

/-!
# V007 — lower semicontinuity of the CFC trace norm

Operator-norm limits of uniformly trace-norm bounded trace-class
operators are trace class and inherit the bound. The proof uses
the polar factor of the limit, finite-set diagonal estimates,
and positivity/summability of the CFC diagonal.

Separate candidate; no CompleteSpace instance and no extra axioms.
-/

noncomputable section
namespace ProbabilisticTheory
open scoped ComplexOrder InnerProductSpace Topology Filter
open Filter

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isTraceClass_of_tendsto_of_traceNorm_bounded_v007 {Tn : ℕ → H →L[ℂ] H} {T : H →L[ℂ] H} {C : ℝ}
    (hTn : ∀ n, IsTraceClass (Tn n)) (hbound : ∀ n, traceNorm (Tn n) (hTn n) ≤ C)
    (htendsto : Tendsto Tn atTop (𝓝 T)) :
    ∃ hT : IsTraceClass T, traceNorm T hT ≤ C := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  set W : H →L[ℂ] H := Polar.polarFactor T with hWdef
  have hWnorm : ‖W‖ ≤ 1 := Polar.polarFactor_opNorm_le T
  have hcont : ∀ i : w, Tendsto (fun n => ‖⟪W (b i), Tn n (b i)⟫_ℂ‖) atTop
      (𝓝 ‖⟪W (b i), T (b i)⟫_ℂ‖) := by
    intro i
    have h1 : Tendsto (fun n => Tn n (b i)) atTop (𝓝 (T (b i))) := by
      have hev : Continuous (fun X : H →L[ℂ] H => X (b i)) :=
        (ContinuousLinearMap.apply ℂ H (b i : H)).continuous
      exact hev.continuousAt.tendsto.comp htendsto
    have h2 : Tendsto (fun n => ⟪W (b i), Tn n (b i)⟫_ℂ) atTop
        (𝓝 ⟪W (b i), T (b i)⟫_ℂ) :=
      ((continuous_const.inner continuous_id).continuousAt.tendsto.comp h1
        |>.congr (fun _ => rfl)).mono_left le_rfl
    exact continuous_norm.continuousAt.tendsto.comp h2
  have hFinset : ∀ u : Finset w, (∑ i ∈ u, ‖⟪W (b i), T (b i)⟫_ℂ‖) ≤ C := by
    intro u
    have hpt : ∀ n, (∑ i ∈ u, ‖⟪W (b i), Tn n (b i)⟫_ℂ‖) ≤ C := by
      intro n
      have hsum : Summable (fun i : w => ‖⟪W (b i), Tn n (b i)⟫_ℂ‖) :=
        (norm_inner_contraction_tsum_le_traceNorm_young (Tn n) W (hTn n) hWnorm b).1
      have hall : (∑' i : w, ‖⟪W (b i), Tn n (b i)⟫_ℂ‖) ≤ C :=
        ((norm_inner_contraction_tsum_le_traceNorm_young (Tn n) W (hTn n) hWnorm b).2).trans (hbound n)
      exact (hsum.sum_le_tsum u (fun i _ => norm_nonneg _)).trans hall
    have hlim : Tendsto (fun n => ∑ i ∈ u, ‖⟪W (b i), Tn n (b i)⟫_ℂ‖) atTop
        (𝓝 (∑ i ∈ u, ‖⟪W (b i), T (b i)⟫_ℂ‖)) :=
      tendsto_finsetSum u (fun i _ => hcont i)
    exact le_of_tendsto hlim (Eventually.of_forall hpt)
  have hsummable : Summable (fun i : w => ‖⟪W (b i), T (b i)⟫_ℂ‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) hFinset
  have htsum_le : (∑' i : w, ‖⟪W (b i), T (b i)⟫_ℂ‖) ≤ C :=
    Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) hFinset
  have hpoint : ∀ i : w, (⟪b i, CFC.abs T (b i)⟫_ℂ).re = ‖⟪W (b i), T (b i)⟫_ℂ‖ := by
    intro i
    have hval : ⟪b i, CFC.abs T (b i)⟫_ℂ = ⟪W (b i), T (b i)⟫_ℂ := by
      have habs : CFC.abs T = star W * T := (Polar.star_polarFactor_mul_self T).symm
      rw [habs, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_right W (b i) (T (b i))]
    have hpos : (CFC.abs T).IsPositive := (CFC.abs T).nonneg_iff_isPositive.mp (CFC.abs_nonneg T)
    have hx := (ContinuousLinearMap.isPositive_iff_complex (CFC.abs T)).mp hpos (b i)
    have h1 : ⟪CFC.abs T (b i), b i⟫_ℂ = ((⟪CFC.abs T (b i), b i⟫_ℂ).re : ℂ) := hx.1.symm
    have hre : (⟪CFC.abs T (b i), b i⟫_ℂ).re = (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by
      rw [← inner_conj_symm (CFC.abs T (b i)) (b i)]; exact Complex.conj_re _
    have heq : ⟪b i, CFC.abs T (b i)⟫_ℂ = ((⟪b i, CFC.abs T (b i)⟫_ℂ).re : ℂ) := by
      calc
        ⟪b i, CFC.abs T (b i)⟫_ℂ = (starRingEnd ℂ) ⟪CFC.abs T (b i), b i⟫_ℂ :=
          (inner_conj_symm (b i) (CFC.abs T (b i))).symm
        _ = (starRingEnd ℂ) ((⟪CFC.abs T (b i), b i⟫_ℂ).re : ℂ) := congrArg (starRingEnd ℂ) h1
        _ = ((⟪CFC.abs T (b i), b i⟫_ℂ).re : ℂ) := by simp
        _ = ((⟪b i, CFC.abs T (b i)⟫_ℂ).re : ℂ) := by rw [hre]
    have hnonneg : 0 ≤ (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by rw [← hre]; exact hx.2
    rw [show ‖⟪W (b i), T (b i)⟫_ℂ‖ = ‖⟪b i, CFC.abs T (b i)⟫_ℂ‖ from by rw [hval],
      heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg, Complex.ofReal_re]
  have hT : IsTraceClass T := ⟨w, b, by
    apply hsummable.congr
    exact fun i => (hpoint i).symm⟩
  refine ⟨hT, ?_⟩
  rw [traceNorm_eq_of_hilbertBasis hT b]
  calc
    (∑' i : w, (⟪b i, CFC.abs T (b i)⟫_ℂ).re) = ∑' i : w, ‖⟪W (b i), T (b i)⟫_ℂ‖ :=
      tsum_congr hpoint
    _ ≤ C := htsum_le

#print axioms ProbabilisticTheory.isTraceClass_of_tendsto_of_traceNorm_bounded_v007

end ProbabilisticTheory
