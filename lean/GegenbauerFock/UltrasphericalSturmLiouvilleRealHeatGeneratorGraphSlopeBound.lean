import GegenbauerFock.UltrasphericalSturmLiouvilleExactGegenbauerSpectralClosure
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitHilbertCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatScalarDomination
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicInfiniteSpectralPoincare
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# V007 — uniform heat difference-quotient estimate on canonical graph domain

For every f in the domain of the ORIGINAL polynomial Sturm closure and
every positive time s, the actual full weighted-L² heat semigroup obeys

   ‖(H_s f - f) / s‖₂ ≤ ‖closure(L₀) f‖₂.

This time-independent bound is a graph-norm continuity estimate.
Its proof uses the already established full-L² diagonal heat action,
the exact closed Sturm diagonal action, the scalar inequality
-w ≤ (exp(-s w)-1)/s ≤ 0, and Hilbert-basis Parseval.

It supports the forward generator-domain inclusion, but is not by
itself the required full graph-domain strong derivative convergence.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The exact uniform graph-domain difference-quotient bound for the
genuine weighted-L² heat limit, for every lambda > 0 and s > 0. -/
theorem sturmRealHeat_closed_domain_slope_norm_le
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 < s)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    ‖s⁻¹ •
      (sturmRealHeatLimitCLM lam hlam s hs.le (x : SturmH lam) -
        (x : SturmH lam))‖ ≤
      ‖(sturmRealPartialOperator lam hlam).closure x‖ := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let f : SturmH lam := x
  let A := (sturmRealPartialOperator lam hlam).closure
  let T := sturmRealHeatLimitCLM lam hlam s hs.le
  let z : SturmH lam := s⁻¹ • (T f - f)
  have hz (n : ℕ) :
      (b.repr z) n =
        ((Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) - 1) / s) *
          (b.repr f) n := by
    have hdiag :=
      sturmRealHeatLimitCLM_hilbert_repr_diagonal
        lam hlam s hs.le f n
    change (b.repr (s⁻¹ • (T f - f))) n = _
    rw [map_smul, map_sub]
    change s⁻¹ * ((b.repr (T f)) n - (b.repr f) n) = _
    rw [hdiag, div_eq_mul_inv]
    ring
  have hA (n : ℕ) :
      (b.repr (A x)) n =
        (-(n : ℝ) * ((n : ℝ) + 2 * lam)) * (b.repr f) n :=
    sturmRealClosed_monicHilbert_diagonal_action
      lam 1 hlam (by norm_num) x n
  have hpoint (n : ℕ) :
      ((b.repr z) n) ^ 2 ≤ ((b.repr (A x)) n) ^ 2 := by
    let w : ℝ := (n : ℝ) * ((n : ℝ) + 2 * lam)
    let q : ℝ := (Real.exp (-s * w) - 1) / s
    have hw : 0 ≤ w := by
      dsimp [w]
      positivity
    obtain ⟨hlo, hhi⟩ :=
      sturmRealHeat_scalar_slope_error_bounded w s hw hs
    have hqlo : -w ≤ q := by dsimp [q]; linarith
    have hqhi : q ≤ 0 := by dsimp [q]; linarith
    have hsq : q ^ 2 ≤ (-w) ^ 2 := by nlinarith
    rw [hz n, hA n]
    change (q * (b.repr f) n) ^ 2 ≤
      ((-w) * (b.repr f) n) ^ 2
    calc
      (q * (b.repr f) n) ^ 2 =
          q ^ 2 * ((b.repr f) n) ^ 2 := by ring
      _ ≤ (-w) ^ 2 * ((b.repr f) n) ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = ((-w) * (b.repr f) n) ^ 2 := by ring
  have hsquared (y : SturmH lam) :
      Summable (fun n : ℕ => ((b.repr y) n) ^ 2) := by
    have hsum := b.summable_inner_mul_inner y y
    have hterm (n : ℕ) :
        inner ℝ y (b n) * inner ℝ (b n) y =
          ((b.repr y) n) ^ 2 := by
      rw [HilbertBasis.repr_apply_apply, real_inner_comm y (b n)]
      ring
    exact hsum.congr hterm
  have hbound :=
    (hsquared z).tsum_le_tsum hpoint (hsquared (A x))
  rw [sturmMonic_realL2_parseval_tsum_sq lam hlam z,
    sturmMonic_realL2_parseval_tsum_sq lam hlam (A x)] at hbound
  have hnonnegz : 0 ≤ ‖z‖ := norm_nonneg _
  have hnonnega : 0 ≤ ‖A x‖ := norm_nonneg _
  change ‖z‖ ≤ ‖A x‖
  nlinarith

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_closed_domain_slope_norm_le

end GegenbauerFock.Ultraspherical
