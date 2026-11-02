import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitHilbertCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleRealSpectralGapScalar
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicInfiniteSpectralPoincare
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# V007 — exact sharp mean-zero heat decay on all genuine weighted real L²

From the kernel-verified normalized Gegenbauer Hilbert basis and the
all-L² diagonal action of the strong Yosida heat limit, Parseval and
the first spectral gap imply the SHARP operator norm estimate

  ||H_s f||₂ ≤ exp(-s(1+2λ)) ||f||₂

for every f in the zero-constant-coordinate closed subspace, s≥0.
The degree-one normalized mode attains equality (separate certified
first-mode theorem). Unlike single-mode inequalities, this is on the
entire infinite-dimensional mean-zero weighted L².
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Sharp full weighted-L² heat decay on the entire mean-zero
subspace (not merely the span of finitely many eigenfunctions). -/
theorem sturmRealHeatLimitCLM_mean_zero_exponential_decay
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s) (f : SturmH lam)
    (hzero :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 = 0) :
    ‖sturmRealHeatLimitCLM lam hlam s hs f‖ ≤
      Real.exp (-s * (1 + 2 * lam)) * ‖f‖ := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let T := sturmRealHeatLimitCLM lam hlam s hs
  let gamma : ℝ := Real.exp (-s * (1 + 2 * lam))
  have hgamma : 0 ≤ gamma := (Real.exp_pos _).le
  have hsquared (x : SturmH lam) :
      Summable (fun n : ℕ => ((b.repr x) n) ^ 2) := by
    have hsum := b.summable_inner_mul_inner x x
    have hterm (n : ℕ) :
        inner ℝ x (b n) * inner ℝ (b n) x =
          ((b.repr x) n) ^ 2 := by
      rw [HilbertBasis.repr_apply_apply, real_inner_comm x (b n)]
      ring
    exact hsum.congr hterm
  have hsumf := hsquared f
  have hsumT := hsquared (T f)
  have hsumScaled :
      Summable (fun n : ℕ => gamma ^ 2 * ((b.repr f) n) ^ 2) :=
    hsumf.mul_left _
  have hdiag (n : ℕ) :
      (b.repr (T f)) n =
        Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) *
          (b.repr f) n :=
    sturmRealHeatLimitCLM_hilbert_repr_diagonal lam hlam s hs f n
  have hpoint (n : ℕ) :
      ((b.repr (T f)) n) ^ 2 ≤
        gamma ^ 2 * ((b.repr f) n) ^ 2 := by
    rw [hdiag n]
    by_cases hn : n = 0
    · subst n
      change (b.repr f) 0 = 0 at hzero
      simp [hzero]
    · have hw :=
        sturmPositiveDegree_spectralRate_ge_first lam hlam n
          (Nat.pos_of_ne_zero hn)
      have hmul := mul_le_mul_of_nonneg_left hw hs
      have hExp :
          Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) ≤ gamma := by
        apply Real.exp_le_exp.mpr
        linarith
      have hePos :
          0 ≤ Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) :=
        (Real.exp_pos _).le
      have hsq :
          (Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))) ^ 2 ≤
            gamma ^ 2 := by
        nlinarith
      calc
        (Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) *
          (b.repr f) n) ^ 2 =
            (Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))) ^ 2 *
              ((b.repr f) n) ^ 2 := by ring
        _ ≤ gamma ^ 2 * ((b.repr f) n) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hbound := hsumT.tsum_le_tsum hpoint hsumScaled
  rw [tsum_mul_left] at hbound
  change (∑' n : ℕ, ((b.repr (T f)) n) ^ 2) ≤
    gamma ^ 2 * (∑' n : ℕ, ((b.repr f) n) ^ 2) at hbound
  rw [sturmMonic_realL2_parseval_tsum_sq lam hlam (T f),
    sturmMonic_realL2_parseval_tsum_sq lam hlam f] at hbound
  have hnonneg : 0 ≤ gamma * ‖f‖ :=
    mul_nonneg hgamma (norm_nonneg _)
  have hnorm : 0 ≤ ‖T f‖ := norm_nonneg _
  nlinarith

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_mean_zero_exponential_decay

end GegenbauerFock.Ultraspherical
