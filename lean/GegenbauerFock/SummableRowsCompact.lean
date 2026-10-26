import GegenbauerFock.InfiniteFockTruncations
import Mathlib

/-!
# V007: Hilbert–Schmidt row summability implies compactness into Fock ℓ²

Let T:E→ℓ²(ℕ;ℂ) be bounded. If the squared operator norms
of all canonical coordinate rows (eval_n ∘ T) form a summable
nonnegative real series, T is compact.

Proof scheme, fully formal:
finite-rank coordinate truncations; exact ℓ² remainder identity;
uniform squared norm tail estimate; convergence of scalar series
tails; norm-convergence of finite-rank truncations; closure of the
compact operators in the operator norm.

The theorem is abstract in E but will apply without additional
assumptions to the concrete λ,α Gegenbauer–Fock operator, since
its coefficient row-energy was already proved summable.

No sorry, admit, or new axioms.
-/

open scoped ENNReal
open Filter

namespace GegenbauerFock.SummableRowsCompact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable abbrev Target := lp (fun _ : ℕ => ℂ) 2

noncomputable def row (T : E →L[ℂ] Target) (n : ℕ) : E →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).comp T

theorem row_apply (T : E →L[ℂ] Target) (n : ℕ) (x : E) :
    row T n x = (T x) n := rfl

noncomputable def truncation (T : E →L[ℂ] Target) (N : ℕ) :
    E →L[ℂ] Target :=
  FockFiniteRank.truncation (row T) N

theorem truncation_compact (T : E →L[ℂ] Target) (N : ℕ) :
    IsCompactOperator (truncation T N) :=
  FockFiniteRank.truncation_compact (row T) N

theorem truncation_apply (T : E →L[ℂ] Target) (N : ℕ) (x : E) :
    truncation T N x =
      ∑ n ∈ Finset.range N, lp.single 2 n ((T x) n) := by
  unfold truncation FockFiniteRank.truncation
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro n hn
  change (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 n)
    (row T n x) = lp.single 2 n ((T x) n)
  rw [lp.singleContinuousLinearMap_apply, row_apply]

theorem row_sq_bound (T : E →L[ℂ] Target) (x : E) (n : ℕ) :
    ‖(T x) n‖ ^ 2 ≤ ‖row T n‖ ^ 2 * ‖x‖ ^ 2 := by
  rw [← row_apply]
  calc
    ‖row T n x‖ ^ 2 ≤ (‖row T n‖ * ‖x‖) ^ 2 := by
      gcongr
      exact (row T n).le_opNorm x
    _ = ‖row T n‖ ^ 2 * ‖x‖ ^ 2 := mul_pow _ _ _

theorem output_rows_summable (T : E →L[ℂ] Target)
    (hk : Summable (fun n : ℕ => ‖row T n‖ ^ 2))
    (x : E) :
    Summable (fun n : ℕ => ‖(T x) n‖ ^ 2) := by
  exact Summable.of_nonneg_of_le (fun n => sq_nonneg _)
    (row_sq_bound T x) (hk.mul_right (‖x‖ ^ 2))

theorem error_norm_sq_tail (T : E →L[ℂ] Target)
    (hk : Summable (fun n : ℕ => ‖row T n‖ ^ 2))
    (x : E) (N : ℕ) :
    ‖T x - truncation T N x‖ ^ 2 =
      ∑' m : ℕ, ‖(T x) (m + N)‖ ^ 2 := by
  have hf := output_rows_summable T hk x
  have hnorm : ‖T x‖ ^ 2 =
      (∑' n : ℕ, ‖(T x) n‖ ^ 2) := by
    simpa using (lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (T x))
  have htrunc : ‖T x - truncation T N x‖ ^ 2 =
      ‖T x‖ ^ 2 - ∑ n ∈ Finset.range N, ‖(T x) n‖ ^ 2 := by
    rw [truncation_apply]
    simpa using (lp.norm_compl_sum_single
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (T x) (Finset.range N))
  rw [htrunc, hnorm]
  have hs := hf.sum_add_tsum_nat_add N
  linarith

noncomputable def tail (T : E →L[ℂ] Target) (N : ℕ) : ℝ :=
  ∑' m : ℕ, ‖row T (m + N)‖ ^ 2

theorem tail_nonneg (T : E →L[ℂ] Target) (N : ℕ) :
    0 ≤ tail T N :=
  tsum_nonneg (fun m => sq_nonneg _)

theorem error_norm_sq_le (T : E →L[ℂ] Target)
    (hk : Summable (fun n : ℕ => ‖row T n‖ ^ 2))
    (x : E) (N : ℕ) :
    ‖T x - truncation T N x‖ ^ 2 ≤ tail T N * ‖x‖ ^ 2 := by
  rw [error_norm_sq_tail T hk x N]
  have hx := output_rows_summable T hk x
  have hshift : Summable (fun m : ℕ => ‖(T x) (m + N)‖ ^ 2) :=
    (summable_nat_add_iff N).mpr hx
  have hbound : Summable (fun m : ℕ =>
      ‖row T (m + N)‖ ^ 2 * ‖x‖ ^ 2) :=
    ((summable_nat_add_iff N).mpr hk).mul_right (‖x‖ ^ 2)
  have h := hshift.tsum_le_tsum
    (fun m => row_sq_bound T x (m + N)) hbound
  simpa only [tail, tsum_mul_right] using h

theorem tail_tendsto_zero (T : E →L[ℂ] Target)
    (hk : Summable (fun n : ℕ => ‖row T n‖ ^ 2)) :
    Tendsto (tail T) atTop (nhds 0) := by
  have hsum := hk.tendsto_sum_tsum_nat
  have htail (N : ℕ) :
      tail T N =
        (∑' n : ℕ, ‖row T n‖ ^ 2) -
        ∑ n ∈ Finset.range N, ‖row T n‖ ^ 2 := by
    have h := hk.sum_add_tsum_nat_add N
    unfold tail
    linarith
  simp_rw [htail]
  simpa using (tendsto_const_nhds.sub hsum)

theorem operator_error_norm_bound (T : E →L[ℂ] Target)
    (hk : Summable (fun n : ℕ => ‖row T n‖ ^ 2)) (N : ℕ) :
    ‖T - truncation T N‖ ≤ Real.sqrt (tail T N) := by
  apply ContinuousLinearMap.opNorm_le_bound
    _ (Real.sqrt_nonneg _)
  intro x
  have hsq := error_norm_sq_le T hk x N
  have ht := Real.sq_sqrt (tail_nonneg T N)
  have hp : 0 ≤ Real.sqrt (tail T N) * ‖x‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hn : 0 ≤ ‖T x - truncation T N x‖ := norm_nonneg _
  change ‖T x - truncation T N x‖ ≤
    Real.sqrt (tail T N) * ‖x‖
  nlinarith [sq_nonneg ‖x‖]

theorem operator_truncations_tendsto (T : E →L[ℂ] Target)
    (hk : Summable (fun n : ℕ => ‖row T n‖ ^ 2)) :
    Tendsto (truncation T) atTop (nhds T) := by
  have htail := tail_tendsto_zero T hk
  have hsqrt : Tendsto (fun N => Real.sqrt (tail T N)) atTop (nhds 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0).comp htail
  have hnorm : Tendsto (fun N => ‖T - truncation T N‖) atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _)
      (Filter.Eventually.of_forall fun N => operator_error_norm_bound T hk N)
      hsqrt
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  simpa only [norm_sub_rev] using hnorm

/-- The actual infinite-dimensional Hilbert–Schmidt compactness bridge:
square-summable canonical output-row norms imply operator compactness. -/
theorem compact_of_summable_rows (T : E →L[ℂ] Target)
    (hk : Summable (fun n : ℕ => ‖row T n‖ ^ 2)) :
    IsCompactOperator T := by
  apply isCompactOperator_of_tendsto (operator_truncations_tendsto T hk)
  exact Filter.Eventually.of_forall (truncation_compact T)

#print axioms GegenbauerFock.SummableRowsCompact.error_norm_sq_tail
#print axioms GegenbauerFock.SummableRowsCompact.operator_error_norm_bound
#print axioms GegenbauerFock.SummableRowsCompact.operator_truncations_tendsto
#print axioms GegenbauerFock.SummableRowsCompact.compact_of_summable_rows

end GegenbauerFock.SummableRowsCompact
