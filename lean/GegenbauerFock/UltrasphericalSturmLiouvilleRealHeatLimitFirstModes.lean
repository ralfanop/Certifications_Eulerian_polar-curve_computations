import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitEigenmodes
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2HilbertBasis

/-!
# V007 — exact constant and first nonconstant heat modes in genuine weighted L²

The strong Yosida heat limit has already been constructed as a contractive
continuous linear operator on all weighted real L². This module extracts
two exact consequences of its Gegenbauer diagonal action: conservation
of the constant mode and exponential decay at the first spectral gap.

The norm formula is an equality on the *actual normalized L² eigenvector*,
not a bound on an auxiliary coefficient sequence. It supplies a sharpness
witness for future global mean-zero heat-decay estimates.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The heat-limit semigroup fixes the normalized constant Gegenbauer mode. -/
theorem sturmRealHeatLimitCLM_fixed_constant_mode
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s) :
    sturmRealHeatLimitCLM lam hlam s hs
      (sturmMonicEigenCandidate_realL2_normalized lam hlam 0) =
      sturmMonicEigenCandidate_realL2_normalized lam hlam 0 := by
  simpa using
    (sturmRealHeatLimitCLM_normalized_Gegenbauer_eigen lam hlam s hs 0)

/-- The first nonconstant normalized mode decays with the exact
spectral-gap exponent -(1+2λ)s. -/
theorem sturmRealHeatLimitCLM_first_mode
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s) :
    sturmRealHeatLimitCLM lam hlam s hs
      (sturmMonicEigenCandidate_realL2_normalized lam hlam 1) =
      Real.exp (-s * (1 + 2 * lam)) •
        sturmMonicEigenCandidate_realL2_normalized lam hlam 1 := by
  simpa only [Nat.cast_one, one_mul] using
    (sturmRealHeatLimitCLM_normalized_Gegenbauer_eigen lam hlam s hs 1)

/-- Equality of the genuine weighted L² norm with the first-gap
decay factor, providing a nonzero sharpness witness. -/
theorem sturmRealHeatLimitCLM_first_mode_norm
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s) :
    ‖sturmRealHeatLimitCLM lam hlam s hs
      (sturmMonicEigenCandidate_realL2_normalized lam hlam 1)‖ =
      Real.exp (-s * (1 + 2 * lam)) := by
  rw [sturmRealHeatLimitCLM_first_mode lam hlam s hs,
    norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),
    sturmMonicEigenCandidate_realL2_normalized_norm, mul_one]

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_fixed_constant_mode
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_first_mode
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_first_mode_norm

end GegenbauerFock.Ultraspherical
