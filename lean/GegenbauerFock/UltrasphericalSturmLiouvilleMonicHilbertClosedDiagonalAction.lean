import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertResolventCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventSpectralGraph

/-!
# V007 — exact diagonal ACTION of the canonical closed Sturm operator

For every u in the genuine domain of the closure of the polynomial
ultraspherical Sturm operator, its Fourier coordinates in the
EXPLICIT, kernel-verified normalized Gegenbauer Hilbert basis obey

  b.repr (Abar u) n = -n(n+2λ) * b.repr u n.

This proves the closed operator itself acts as the expected
unbounded diagonal differential spectrum on EVERY domain vector,
not just on polynomial eigenfunctions or a hypothetical extension.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

theorem sturmRealClosed_monicHilbert_diagonal_action
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (x : (sturmRealPartialOperator lam hlam).closure.domain)
    (n : ℕ) :
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      ((sturmRealPartialOperator lam hlam).closure x) n =
    (-(n : ℝ) * ((n : ℝ) + 2 * lam)) *
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (x : SturmH lam) n := by
  let A := (sturmRealPartialOperator lam hlam).closure
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let w : ℝ := t + (n : ℝ) * ((n : ℝ) + 2 * lam)
  let f : SturmH lam := t • (x : SturmH lam) - A x
  have hw : w ≠ 0 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have ht2 : 0 ≤ (n : ℝ) + 2 * lam := by positivity
    have hh : 0 ≤ (n : ℝ) * ((n : ℝ) + 2 * lam) :=
      mul_nonneg hn ht2
    apply ne_of_gt
    dsimp [w]
    linarith
  have hinv := sturmRealPositiveResolventFullCLM_left_inverse_closed_shift
    lam t hlam ht x
  have hcoord := sturmMonicRealHilbertBasis_full_resolvent_repr_diagonal
    lam t hlam ht f n
  change
    (b.repr (sturmRealPositiveResolventFullCLM lam t hlam ht f)) n =
      w⁻¹ * (b.repr f) n at hcoord
  rw [hinv] at hcoord
  have hweighted : w * (b.repr (x : SturmH lam)) n =
      (b.repr f) n := by
    calc
      w * (b.repr (x : SturmH lam)) n =
          w * (w⁻¹ * (b.repr f) n) := by rw [hcoord]
      _ = (b.repr f) n := by
        rw [← mul_assoc, mul_inv_cancel₀ hw, one_mul]
  have hlinear : (b.repr f) n =
      t * (b.repr (x : SturmH lam)) n -
        (b.repr (A x)) n := by
    dsimp [f]
    rw [map_sub, map_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change (b.repr (A x)) n =
    (-(n : ℝ) * ((n : ℝ) + 2 * lam)) *
      (b.repr (x : SturmH lam)) n
  calc
    (b.repr (A x)) n =
        t * (b.repr (x : SturmH lam)) n -
          w * (b.repr (x : SturmH lam)) n := by
            rw [hweighted] at hlinear
            linarith
    _ = (-(n : ℝ) * ((n : ℝ) + 2 * lam)) *
          (b.repr (x : SturmH lam)) n := by
            dsimp [w]
            ring

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_monicHilbert_diagonal_action

end GegenbauerFock.Ultraspherical
