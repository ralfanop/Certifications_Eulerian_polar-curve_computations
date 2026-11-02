import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitEigenmodes
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2HilbertBasis
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# V007 — exact heat Fourier coordinates for every genuine weighted L² vector

Unlike the individual eigenmode formula, this theorem identifies the
Fourier-Gegenbauer coefficients of H_s f for ARBITRARY f in the actual
weighted real L². The proof uses the complete orthonormal Hilbert basis,
the norm-convergent basis expansion, the continuous heat-limit operator,
and the exact eigenvalue of each normalized basis vector.

No unbounded-generator identification is assumed.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The genuine full-L² contractive heat-limit continuous linear operator
has the exact Gegenbauer Fourier multiplier exp(-s*n(n+2lambda))
on EVERY weighted L² vector, not just finite eigenmode sums. -/
theorem sturmRealHeatLimitCLM_hilbert_repr_diagonal
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s)
    (f : SturmH lam) (n : ℕ) :
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (sturmRealHeatLimitCLM lam hlam s hs f) n =
    Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) *
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f n := by
  let b : HilbertBasis ℕ ℝ (SturmH lam) :=
    sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let T : SturmH lam →L[ℝ] SturmH lam :=
    sturmRealHeatLimitCLM lam hlam s hs
  let beta : ℕ → ℝ :=
    fun i => Real.exp (-s * ((i : ℝ) * ((i : ℝ) + 2 * lam)))
  have hb (i : ℕ) :
      b i = sturmMonicEigenCandidate_realL2_normalized lam hlam i := by
    simp only [b, sturmMonicEigenCandidate_realL2_hilbertBasis,
      HilbertBasis.coe_mkOfOrthogonalEqBot]
  have heigen (i : ℕ) : T (b i) = beta i • b i := by
    rw [hb i]
    exact sturmRealHeatLimitCLM_normalized_Gegenbauer_eigen
      lam hlam s hs i
  have hterm (i : ℕ) :
      inner ℝ (b n) (T ((b.repr f i) • b i)) =
      beta n • inner ℝ (b n) ((b.repr f i) • b i) := by
    rw [map_smul, heigen i]
    simp only [inner_smul_right, smul_eq_mul]
    by_cases hi : i = n
    · subst i
      simp only [smul_eq_mul]
      ring
    · have horth : inner ℝ (b n) (b i) = 0 :=
        b.orthonormal.inner_eq_zero (Ne.symm hi)
      simp [horth]
  have hleft :=
    ((b.hasSum_repr f).mapL T).mapL (innerSL ℝ (b n))
  have hright :=
    ((b.hasSum_repr f).mapL (innerSL ℝ (b n))).const_smul (beta n)
  change HasSum
    (fun i : ℕ => inner ℝ (b n) (T ((b.repr f i) • b i)))
    (inner ℝ (b n) (T f)) at hleft
  change HasSum
    (fun i : ℕ => beta n • inner ℝ (b n) ((b.repr f i) • b i))
    (beta n • inner ℝ (b n) f) at hright
  have heq :
      (fun i : ℕ => inner ℝ (b n) (T ((b.repr f i) • b i))) =
      (fun i : ℕ => beta n • inner ℝ (b n) ((b.repr f i) • b i)) := by
    funext i
    exact hterm i
  rw [heq] at hleft
  have hfinal := hleft.unique hright
  change (b.repr (T f)) n = beta n * (b.repr f) n
  simpa only [HilbertBasis.repr_apply_apply, smul_eq_mul] using hfinal

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_hilbert_repr_diagonal

end GegenbauerFock.Ultraspherical
