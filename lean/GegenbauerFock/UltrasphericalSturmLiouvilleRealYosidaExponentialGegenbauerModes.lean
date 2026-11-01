import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaExponentialEigenvector
import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaNormalizedEigen
import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaHilbertEigenmodes

/-!
# V007 — exact bounded Yosida semigroup action on genuine Gegenbauer modes

Every normalized Gegenbauer vector is an eigenvector of the true bounded
Yosida generator. Combining this with the kernel-checked operator exponential
eigenvector theorem produces exact semigroup eigenmultipliers on the full
weighted real Hilbert L². In particular the normalized constant mode is
preserved for every nonnegative or negative time. No unbounded semigroup
or strong t → ∞ limit is assumed.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Exact degree-wise semigroup multipliers of the bounded Yosida
approximation on the actual normalized Gegenbauer L² eigenvectors. -/
theorem sturmRealYosidaExponential_normalized_Gegenbauer_eigen
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (s : ℝ) (n : ℕ) :
    sturmRealYosidaExponential lam t hlam ht s
      (sturmMonicEigenCandidate_realL2_normalized lam hlam n) =
      (Real.exp (s * (-t * ((n : ℝ) * ((n : ℝ) + 2 * lam)) /
        (t + (n : ℝ) * ((n : ℝ) + 2 * lam))))) •
      sturmMonicEigenCandidate_realL2_normalized lam hlam n := by
  let u : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam n
  let A := sturmRealYosidaGenerator lam t hlam ht
  let mu : ℝ := -t * ((n : ℝ) * ((n : ℝ) + 2 * lam)) /
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam))
  have hu : A u = mu • u :=
    sturmRealYosidaGenerator_normalized_eigen lam t hlam ht n
  have hs : (s • A) u = (s * mu) • u := by
    rw [ContinuousLinearMap.smul_apply, hu, smul_smul]
  change (NormedSpace.exp (s • A)) u = (Real.exp (s * mu)) • u
  exact sturmRealOperatorExponential_eigenvector lam (s • A) u (s * mu) hs

/-- Every bounded Yosida exponential fixes the normalized degree-zero
Gegenbauer mode, uniformly in the time and shift parameters. -/
theorem sturmRealYosidaExponential_fixed_zero_mode
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (s : ℝ) :
    sturmRealYosidaExponential lam t hlam ht s
      (sturmMonicEigenCandidate_realL2_normalized lam hlam 0) =
      sturmMonicEigenCandidate_realL2_normalized lam hlam 0 := by
  let u : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam 0
  let A := sturmRealYosidaGenerator lam t hlam ht
  have hu : A u = 0 :=
    sturmRealYosidaGenerator_zero_mode lam t hlam ht
  have hs : (s • A) u = (0 : ℝ) • u := by
    rw [ContinuousLinearMap.smul_apply, hu]
    simp
  have h := sturmRealOperatorExponential_eigenvector
    lam (s • A) u 0 hs
  change (NormedSpace.exp (s • A)) u = u
  simpa only [Real.exp_zero, one_smul] using h

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaExponential_normalized_Gegenbauer_eigen
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaExponential_fixed_zero_mode

end GegenbauerFock.Ultraspherical
