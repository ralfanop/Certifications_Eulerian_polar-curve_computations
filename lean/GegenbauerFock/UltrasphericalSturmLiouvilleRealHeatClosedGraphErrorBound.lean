import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitHilbertCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatScalarDomination
import GegenbauerFock.UltrasphericalSturmLiouvilleExactGegenbauerSpectralClosure
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicInfiniteSpectralPoincare

/-!
# V007 — graph-uniform bound for full-L2 heat generator difference quotients

Let A be the exact canonical closure of the polynomial Gegenbauer Sturm
operator, and H_s the genuine strongly constructed contraction semigroup.
For every f in the full closed graph domain and every s>0,

  ||s^{-1}(H_s f - f) - A f|| <= ||A f||.

This is NOT a scalar eigenmode statement: it is an actual weighted-real-L2
norm bound on every closed-domain vector. It follows by the already-certified
full-L2 heat multiplier identity, exact canonical closed Sturm diagonalization,
pointwise scalar domination, and Parseval. It is a quantitative ingredient
for graph-core/dominated-convergence proofs of the forward generator inclusion.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Exact Gegenbauer representation of the discrepancy between the
actual full-space heat difference quotient and closed Sturm action. -/
theorem sturmRealHeat_closed_graph_slope_error_repr
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 < s)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) (n : ℕ) :
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (s⁻¹ • (sturmRealHeatLimitCLM lam hlam s hs.le (x : SturmH lam) -
        (x : SturmH lam)) -
        (sturmRealPartialOperator lam hlam).closure x) n =
    ((Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) - 1) / s +
      ((n : ℝ) * ((n : ℝ) + 2 * lam))) *
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (x : SturmH lam) n := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let w : ℝ := (n : ℝ) * ((n : ℝ) + 2 * lam)
  let c : ℝ := (b.repr (x : SturmH lam)) n
  have hheat := sturmRealHeatLimitCLM_hilbert_repr_diagonal
    lam hlam s hs.le (x : SturmH lam) n
  have hclosed :=
    (sturmRealClosed_eq_exact_monicGegenbauer_spectral_realization
      lam hlam).2 x n
  change (b.repr
    (s⁻¹ • (sturmRealHeatLimitCLM lam hlam s hs.le (x : SturmH lam) -
      (x : SturmH lam)) -
      (sturmRealPartialOperator lam hlam).closure x)) n =
    ((Real.exp (-s * w) - 1) / s + w) * c
  rw [map_sub, map_smul, map_sub, hheat, hclosed]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

/-- Every true closed-domain input obeys the time-uniform sharp
graph norm error bound for right heat difference quotients in full L2. -/
theorem sturmRealHeat_closed_graph_slope_error_norm_le
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 < s)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    ‖s⁻¹ • (sturmRealHeatLimitCLM lam hlam s hs.le (x : SturmH lam) -
        (x : SturmH lam)) -
        (sturmRealPartialOperator lam hlam).closure x‖ ≤
      ‖(sturmRealPartialOperator lam hlam).closure x‖ := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let A := (sturmRealPartialOperator lam hlam).closure
  let y : SturmH lam :=
    s⁻¹ • (sturmRealHeatLimitCLM lam hlam s hs.le (x : SturmH lam) -
      (x : SturmH lam)) - A x
  have hsquared (z : SturmH lam) :
      Summable (fun n : ℕ => ((b.repr z) n) ^ 2) := by
    have hsum := b.summable_inner_mul_inner z z
    have hterm (n : ℕ) :
        inner ℝ z (b n) * inner ℝ (b n) z =
          ((b.repr z) n) ^ 2 := by
      rw [HilbertBasis.repr_apply_apply, real_inner_comm z (b n)]
      ring
    exact hsum.congr hterm
  have hpoint (n : ℕ) :
      ((b.repr y) n) ^ 2 ≤ ((b.repr (A x)) n) ^ 2 := by
    let w : ℝ := (n : ℝ) * ((n : ℝ) + 2 * lam)
    let c : ℝ := (b.repr (x : SturmH lam)) n
    have hw : 0 ≤ w := by dsimp [w]; positivity
    obtain ⟨hq0, hqw⟩ :=
      sturmRealHeat_scalar_slope_error_bounded w s hw hs
    have hsq :
        (((Real.exp (-s * w) - 1) / s + w)) ^ 2 ≤ w ^ 2 := by
      nlinarith
    have hcoef :=
      sturmRealHeat_closed_graph_slope_error_repr lam hlam s hs x n
    have hA :=
      (sturmRealClosed_eq_exact_monicGegenbauer_spectral_realization
        lam hlam).2 x n
    change (b.repr y) n =
      ((Real.exp (-s * w) - 1) / s + w) * c at hcoef
    change (b.repr (A x)) n = (-w) * c at hA
    rw [hcoef, hA]
    calc
      (((Real.exp (-s * w) - 1) / s + w) * c) ^ 2 =
        (((Real.exp (-s * w) - 1) / s + w)) ^ 2 * c ^ 2 := by ring
      _ ≤ w ^ 2 * c ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg c)
      _ = ((-w) * c) ^ 2 := by ring
  have hbound := (hsquared y).tsum_le_tsum hpoint (hsquared (A x))
  change ‖y‖ ≤ ‖A x‖
  rw [← sturmMonic_realL2_parseval_tsum_sq lam hlam y,
    ← sturmMonic_realL2_parseval_tsum_sq lam hlam (A x)] at *
  nlinarith [norm_nonneg y, norm_nonneg (A x)]

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_closed_graph_slope_error_repr
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_closed_graph_slope_error_norm_le

end GegenbauerFock.Ultraspherical
