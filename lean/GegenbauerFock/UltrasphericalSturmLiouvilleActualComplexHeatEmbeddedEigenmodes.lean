import GegenbauerFock.UltrasphericalSturmLiouvilleActualComplexHeatCLM
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatComplexCFCS1Bridge
import GegenbauerFock.UltrasphericalSturmLiouvilleActualComplexLpIsometry

/-!
# V007 — actual complex Sturm heat on the embedded normalized Gegenbauer modes

The already kernel-certified complete REAL normalized Gegenbauer basis
is mapped into the GENUINE COMPLEX weighted L² by the actual isometric
real-to-complex inclusion, and the genuine COMPLEX-linear heat action
on each embedded mode is determined exactly.

The eigenvalue is the usual nonnegative-time Sturm heat multiplier,
regarded as a complex scalar:
    H^C_s (J e_n) = (exp(-s*n*(n+2*lambda)) : C) • J e_n.
Moreover each embedded mode is nonzero and has norm exactly one.

This certificate does NOT claim the embedded family has already been
formalized as a complete COMPLEX Hilbert basis. That additional
orthonormal-completeness claim must be proved independently.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory InnerProductSpace

private abbrev HR (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev HC (lam : ℝ) := Lp ℂ 2 (measure lam)

/-- Explicit genuine complex-valued Gegenbauer eigenvector. -/
noncomputable def sturmActualComplexNormalizedGegenbauer
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) : HC lam :=
  realToComplexLp lam
    ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n)

/-- The actual complex heat operator has the exact Sturm multiplier
on every embedded normalized Gegenbauer eigenvector. -/
theorem sturmActualComplexHeatCLM_normalized_Gegenbauer_eigen
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    sturmActualComplexHeatCLM lam hlam s hs
        (sturmActualComplexNormalizedGegenbauer lam hlam n) =
      ((Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) : ℝ) : ℂ) •
        sturmActualComplexNormalizedGegenbauer lam hlam n := by
  let r : ℝ := Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))
  let e : HR lam := (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n
  have heig :
      sturmRealHeatLimitCLM lam hlam s hs e = r • e :=
    sturmRealHeat_actual_complete_eigenbasis lam s hlam hs n
  have hcast :
      (r : ℂ) • realToComplexLp lam e =
        r • realToComplexLp lam e := by
    change (algebraMap ℝ ℂ r) • (realToComplexLp lam e) =
      r • (realToComplexLp lam e)
    exact IsScalarTower.algebraMap_smul ℂ r (realToComplexLp lam e)
  change sturmActualComplexHeatCLM lam hlam s hs
      (realToComplexLp lam e) = (r : ℂ) • realToComplexLp lam e
  rw [sturmActualComplexHeatCLM_embedded_real, heig, map_smul]
  exact hcast.symm

/-- Each actual embedded normalized Gegenbauer vector has norm one. -/
theorem sturmActualComplexNormalizedGegenbauer_norm_eq_one
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    ‖sturmActualComplexNormalizedGegenbauer lam hlam n‖ = 1 := by
  change ‖realToComplexLp lam
    ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n)‖ = 1
  rw [realToComplexLp_norm_eq]
  exact (sturmMonicEigenCandidate_realL2_hilbertBasis
    lam hlam).orthonormal.norm_eq_one n

/-- The embedded complex Gegenbauer eigenmode is nonzero. -/
theorem sturmActualComplexNormalizedGegenbauer_ne_zero
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    sturmActualComplexNormalizedGegenbauer lam hlam n ≠ 0 := by
  intro hz
  have hnorm := sturmActualComplexNormalizedGegenbauer_norm_eq_one
    lam hlam n
  rw [hz, norm_zero] at hnorm
  norm_num at hnorm

#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeatCLM_normalized_Gegenbauer_eigen
#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexNormalizedGegenbauer_norm_eq_one
#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexNormalizedGegenbauer_ne_zero

end GegenbauerFock.Ultraspherical
