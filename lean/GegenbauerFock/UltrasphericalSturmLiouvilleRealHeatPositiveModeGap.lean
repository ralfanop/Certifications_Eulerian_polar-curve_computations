import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitEigenmodes
import GegenbauerFock.UltrasphericalSturmLiouvilleRealSpectralGapScalar
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2HilbertBasis

/-!
# V007 — sharp first-gap decay on every normalized positive Gegenbauer mode

On the actual weighted real L² space, the limiting heat operator H_s
has eigenvalues exp(-s * n(n+2lambda)). The normalized Gegenbauer
eigenfunctions have norm one. This module proves their *exact* heat
norms and the universal spectral-gap bound for every positive degree.

A full mean-zero L² norm estimate requires the separate Parseval/diagonal
extension to arbitrary L² vectors; these single-mode statements do not
pretend to establish that stronger estimate.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Exact norm of the heat evolution of every normalized eigenmode
in the genuine weighted real L². -/
theorem sturmRealHeatLimitCLM_normalized_mode_norm
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    ‖sturmRealHeatLimitCLM lam hlam s hs
      (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖ =
      Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) := by
  rw [sturmRealHeatLimitCLM_normalized_Gegenbauer_eigen,
    norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),
    sturmMonicEigenCandidate_realL2_normalized_norm, mul_one]

/-- Every nonconstant normalized Gegenbauer mode decays at least as
fast as the *sharp* first spectral gap 1+2lambda. -/
theorem sturmRealHeatLimitCLM_positive_mode_gap_bound
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s)
    (n : ℕ) (hn : 0 < n) :
    ‖sturmRealHeatLimitCLM lam hlam s hs
      (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖ ≤
      Real.exp (-s * (1 + 2 * lam)) := by
  rw [sturmRealHeatLimitCLM_normalized_mode_norm lam hlam s hs n]
  have hgap := sturmPositiveDegree_spectralRate_ge_first lam hlam n hn
  have hmul := mul_le_mul_of_nonneg_left hgap hs
  apply Real.exp_le_exp.mpr
  linarith

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_normalized_mode_norm
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_positive_mode_gap_bound

end GegenbauerFock.Ultraspherical
