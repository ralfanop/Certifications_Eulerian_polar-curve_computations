import GegenbauerFock.UltrasphericalSturmLiouvilleRealSameMeanSharpConsequences
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertSharpResolventNorm

/-!
# V007 — sharp convergence to constant equilibrium and resolvent splitting

On the full genuine weighted real L² space, the degree-zero normalized
Gegenbauer mode defines the canonical constant-equilibrium component.
For each datum f the heat flow fixes its equilibrium and the remainder
decays at the optimal spectral-gap rate exp(-s(1+2λ)).
The full resolvent acts by 1/t on the equilibrium and obeys the sharp
improved bound on the remainder with coefficient 1/(t+1+2λ).

All statements concern the genuine complete weighted L² Hilbert space,
not truncated coordinates or a formal polynomial approximation.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The rank-one constant equilibrium component extracted by the
normalized zero-th Gegenbauer Fourier coefficient. -/
noncomputable def sturmRealConstantEquilibrium
    (lam : ℝ) (hlam : 0 < lam) (f : SturmH lam) : SturmH lam :=
  ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0) •
    sturmMonicEigenCandidate_realL2_normalized lam hlam 0

/-- Taking the equilibrium component preserves exactly the
degree-zero coefficient of every actual weighted L² datum. -/
theorem sturmRealConstantEquilibrium_zero_coordinate
    (lam : ℝ) (hlam : 0 < lam) (f : SturmH lam) :
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (sturmRealConstantEquilibrium lam hlam f) 0 =
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  have hb0 : b 0 =
      sturmMonicEigenCandidate_realL2_normalized lam hlam 0 := by
    simp only [b, sturmMonicEigenCandidate_realL2_hilbertBasis,
      HilbertBasis.coe_mkOfOrthogonalEqBot]
  have hnorm : ‖b 0‖ = 1 := by
    rw [hb0]
    exact sturmMonicEigenCandidate_realL2_normalized_norm lam hlam 0
  change (b.repr (((b.repr f) 0) •
    sturmMonicEigenCandidate_realL2_normalized lam hlam 0)) 0 =
      (b.repr f) 0
  rw [← hb0, map_smul]
  change (b.repr f) 0 * (b.repr (b 0)) 0 = (b.repr f) 0
  rw [HilbertBasis.repr_apply_apply, real_inner_self_eq_norm_sq, hnorm]
  norm_num

/-- The genuine full-L² heat flow leaves each constant-equilibrium
component unchanged at every nonnegative time. -/
theorem sturmRealHeatLimitCLM_fixes_equilibrium
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s) (f : SturmH lam) :
    sturmRealHeatLimitCLM lam hlam s hs
      (sturmRealConstantEquilibrium lam hlam f) =
    sturmRealConstantEquilibrium lam hlam f := by
  unfold sturmRealConstantEquilibrium
  rw [map_smul, sturmRealHeatLimitCLM_fixed_constant_mode]

/-- Quantitative sharp spectral-gap convergence of the complete
heat semigroup towards the rank-one constant-equilibrium component. -/
theorem sturmRealHeatLimitCLM_equilibrium_convergence
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s) (f : SturmH lam) :
    ‖sturmRealHeatLimitCLM lam hlam s hs f -
      sturmRealConstantEquilibrium lam hlam f‖ ≤
    Real.exp (-s * (1 + 2 * lam)) *
      ‖f - sturmRealConstantEquilibrium lam hlam f‖ := by
  have hsame :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 =
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (sturmRealConstantEquilibrium lam hlam f) 0 :=
    (sturmRealConstantEquilibrium_zero_coordinate lam hlam f).symm
  have h := sturmRealHeatLimitCLM_same_mean_exponential_stability
    lam hlam s hs f (sturmRealConstantEquilibrium lam hlam f) hsame
  rw [sturmRealHeatLimitCLM_fixes_equilibrium lam hlam s hs f] at h
  exact h

/-- The equilibrium is an exact 1/t-eigencomponent for the genuine
canonical positive resolvent on all weighted real L². -/
theorem sturmRealPositiveResolventFullCLM_equilibrium_eigen
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) :
    sturmRealPositiveResolventFullCLM lam t hlam ht
      (sturmRealConstantEquilibrium lam hlam f) =
    t⁻¹ • sturmRealConstantEquilibrium lam hlam f := by
  unfold sturmRealConstantEquilibrium
  rw [map_smul, sturmRealPositiveResolventFullCLM_zero_mode]
  rw [smul_comm]

/-- Exact full-L² resolvent decomposition estimate: after removing
the zero mode, the spectral-gap denominator is t+1+2λ. -/
theorem sturmRealPositiveResolventFullCLM_equilibrium_remainder_bound
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) :
    (t + (1 + 2 * lam)) *
      ‖sturmRealPositiveResolventFullCLM lam t hlam ht f -
        t⁻¹ • sturmRealConstantEquilibrium lam hlam f‖ ≤
      ‖f - sturmRealConstantEquilibrium lam hlam f‖ := by
  have hsame :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 =
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (sturmRealConstantEquilibrium lam hlam f) 0 :=
    (sturmRealConstantEquilibrium_zero_coordinate lam hlam f).symm
  have h := sturmRealPositiveResolventFullCLM_sameMean_twoSource_bound
    lam t hlam ht f (sturmRealConstantEquilibrium lam hlam f) hsame
  rw [sturmRealPositiveResolventFullCLM_equilibrium_eigen lam t hlam ht f] at h
  exact h

#print axioms GegenbauerFock.Ultraspherical.sturmRealConstantEquilibrium_zero_coordinate
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_fixes_equilibrium
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_equilibrium_convergence
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_equilibrium_eigen
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_equilibrium_remainder_bound

end GegenbauerFock.Ultraspherical
