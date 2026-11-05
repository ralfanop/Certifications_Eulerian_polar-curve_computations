import GegenbauerFock.UltrasphericalSturmLiouvilleResolventFiniteTruncationCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventMultiplierMonotone
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertResolventCoordinates
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# V007 — sharp uniform upper bound on the ACTUAL closed Sturm resolvent tail

The explicitly normalized all-degree Gegenbauer Hilbert basis provides
an isometry onto real ℓ². The canonical closed resolvent and each finite
truncation have exact multipliers in those SAME concrete coordinates.
Use pointwise monotonicity of the omitted multipliers together with the
ℓ² norm comparison lemma to prove an OPERATOR-NORM inequality, not just
strong convergence on each input.

This theorem is the outstanding quantitative step needed by the compact
resolvent bridge.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Uniform sharp operator-norm bound for genuine real weighted-L²
Gegenbauer resolvent finite-rank truncations. -/
theorem sturmRealClosedResolvent_finite_tail_norm_le
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (N : ℕ) :
    ‖sturmRealPositiveResolventFullCLM lam t hlam ht -
        sturmRealResolventFiniteRankTruncation lam t hlam N‖ ≤
      (t + (N : ℝ) * ((N : ℝ) + 2 * lam))⁻¹ := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  let T := sturmRealResolventFiniteRankTruncation lam t hlam N
  let B := R - T
  let β : ℕ → ℝ := fun n =>
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹
  have hβpos (n : ℕ) : 0 < β n :=
    sturmResolventMultiplier_pos lam t hlam ht n
  have hβtail (k : ℕ) (hk : N ≤ k) : β k ≤ β N :=
    sturmResolventMultiplier_tail_le lam t hlam ht N k hk
  have hbound : ∀ f : SturmH lam, ‖B f‖ ≤ β N * ‖f‖ := by
    intro f
    have hcoeff (k : ℕ) :
        ‖b.repr (B f) k‖ ≤
          ‖((β N) • (b.repr f)) k‖ := by
      have hR : b.repr (R f) k = β k * b.repr f k :=
        sturmMonicRealHilbertBasis_full_resolvent_repr_diagonal
          lam t hlam ht f k
      have hT : b.repr (T f) k =
          if k < N then β k * b.repr f k else 0 :=
        sturmRealResolventFiniteRankTruncation_repr_diagonal lam t hlam N f k
      have hB : b.repr (B f) k =
          β k * b.repr f k -
            (if k < N then β k * b.repr f k else 0) := by
        calc
          b.repr (B f) k =
              b.repr (R f) k - b.repr (T f) k := by
                simp only [B, ContinuousLinearMap.sub_apply, map_sub,
                  lp.coeFn_sub, Pi.sub_apply]
          _ = _ := by rw [hR, hT]
      have hrhs :
          ((β N) • (b.repr f)) k = β N * b.repr f k := by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      by_cases hk : k < N
      · rw [hB, if_pos hk, sub_self, norm_zero]
        exact norm_nonneg _
      · have hle : N ≤ k := Nat.le_of_not_gt hk
        rw [hB, if_neg hk, sub_zero, hrhs, norm_mul, norm_mul]
        have hnonneg : 0 ≤ ‖b.repr f k‖ := norm_nonneg _
        have hmul := mul_le_mul_of_nonneg_right (hβtail k hle) hnonneg
        simpa only [Real.norm_eq_abs, abs_of_pos (hβpos k),
          abs_of_pos (hβpos N)] using hmul
    have hmono :
        ‖b.repr (B f)‖ ≤ ‖(β N) • (b.repr f)‖ :=
      lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) hcoeff
    calc
      ‖B f‖ = ‖b.repr (B f)‖ := (b.repr.norm_map _).symm
      _ ≤ ‖(β N) • (b.repr f)‖ := hmono
      _ = β N * ‖f‖ := by
        rw [norm_smul, b.repr.norm_map, Real.norm_eq_abs,
          abs_of_pos (hβpos N)]
  change ‖B‖ ≤ β N
  exact B.opNorm_le_bound (le_of_lt (hβpos N)) hbound

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_finite_tail_norm_le

end GegenbauerFock.Ultraspherical
