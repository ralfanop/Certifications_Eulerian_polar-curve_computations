import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2BasisResolvent
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventMultiplierDecay

/-!
# V007 — exact infinite Gegenbauer expansion of the genuine closed resolvent

The complete normalized Gegenbauer Hilbert basis expands every actual
weighted-real-L² vector. Applying the bounded closed Sturm resolvent
termwise gives its true L²-convergent spectral synthesis formula, with
multipliers (t+n(n+2λ))⁻¹. This is convergence in the Hilbert norm for
each fixed input; proving convergence uniformly on the unit ball (in
operator norm) is a separate and stronger obligation for compactness.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Filter

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The actual closed Sturm resolvent equals the Hilbert-summable
spectral expansion on every real weighted-L² input. -/
theorem sturmRealClosedResolvent_hilbert_spectral_hasSum
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) :
    HasSum
      (fun n : ℕ =>
        (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
          ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f n •
            sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam n))
      (sturmRealPositiveResolventFullCLM lam t hlam ht f) := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  have hs : HasSum (fun n : ℕ => (b.repr f n) • b n) f :=
    b.hasSum_repr f
  have hmap : HasSum (fun n : ℕ => R ((b.repr f n) • b n)) (R f) :=
    hs.mapL R
  convert hmap using 1
  funext n
  have heigen : R (b n) =
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ • b n :=
    sturmMonicEigenCandidate_realL2_hilbertBasis_resolvent_diagonal
      lam t hlam ht n
  calc
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
        ((b.repr f n) • b n) =
      (b.repr f n) •
        ((t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ • b n) := by
          simp only [smul_smul, mul_comm]
    _ = (b.repr f n) • R (b n) := by rw [heigen]
    _ = R ((b.repr f n) • b n) := by rw [map_smul]

/-- Exact strong convergence of finite modal sums to the ACTUAL
closed resolvent, for every fixed weighted-real-L² input. -/
theorem sturmRealClosedResolvent_hilbert_spectral_tendsto
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) :
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N,
          (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
            ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f n •
              sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam n))
      atTop (nhds (sturmRealPositiveResolventFullCLM lam t hlam ht f)) :=
  (sturmRealClosedResolvent_hilbert_spectral_hasSum lam t hlam ht f).tendsto_sum_nat

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_hilbert_spectral_hasSum
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_hilbert_spectral_tendsto

end GegenbauerFock.Ultraspherical
