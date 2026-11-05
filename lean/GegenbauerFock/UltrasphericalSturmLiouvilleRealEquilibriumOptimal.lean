import GegenbauerFock.UltrasphericalSturmLiouvilleRealEquilibriumSharp

/-!
# V007 — optimality of full-L² equilibrium convergence and resolvent splitting

The normalized degree-one Gegenbauer eigenvector has zero constant
equilibrium component. It attains the sharp spectral gap for both the
heat semigroup and the genuine positive Sturm resolvent remainder.

The numerical constants are proved optimal on the entire weighted
real L² Hilbert space, not just on finite coordinate truncations.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The normalized first nonconstant Gegenbauer mode has zero
constant-equilibrium component. -/
theorem sturmRealConstantEquilibrium_first_mode_eq_zero
    (lam : ℝ) (hlam : 0 < lam) :
    sturmRealConstantEquilibrium lam hlam
      (sturmMonicEigenCandidate_realL2_normalized lam hlam 1) = 0 := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let u := sturmMonicEigenCandidate_realL2_normalized lam hlam 1
  have hb1 : b 1 = u := by
    simp only [b, u, sturmMonicEigenCandidate_realL2_hilbertBasis,
      HilbertBasis.coe_mkOfOrthogonalEqBot]
  have hu0 : (b.repr u) 0 = 0 := by
    rw [← hb1, HilbertBasis.repr_apply_apply]
    exact b.orthonormal.inner_eq_zero (by decide : (0 : ℕ) ≠ 1)
  change ((b.repr u) 0) •
    sturmMonicEigenCandidate_realL2_normalized lam hlam 0 = 0
  rw [hu0, zero_smul]

/-- The true first Gegenbauer mode attains the heat-flow
convergence-to-equilibrium bound at every nonnegative time. -/
theorem sturmRealHeatLimitCLM_equilibrium_bound_attained
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s) :
    ∃ f : SturmH lam, f ≠ 0 ∧
      ‖sturmRealHeatLimitCLM lam hlam s hs f -
        sturmRealConstantEquilibrium lam hlam f‖ =
      Real.exp (-s * (1 + 2 * lam)) *
        ‖f - sturmRealConstantEquilibrium lam hlam f‖ := by
  let u : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam 1
  have hu0 : sturmRealConstantEquilibrium lam hlam u = 0 :=
    sturmRealConstantEquilibrium_first_mode_eq_zero lam hlam
  have hunorm : ‖u‖ = 1 :=
    sturmMonicEigenCandidate_realL2_normalized_norm lam hlam 1
  have hune : u ≠ 0 := by
    intro heq
    rw [heq, norm_zero] at hunorm
    norm_num at hunorm
  refine ⟨u, hune, ?_⟩
  rw [hu0, sub_zero, sub_zero,
    sturmRealHeatLimitCLM_first_mode_norm lam hlam s hs, hunorm, mul_one]

/-- No smaller heat relaxation factor can control the full
weighted-L² deviation from constant equilibrium uniformly. -/
theorem sturmRealHeatLimitCLM_equilibrium_constant_optimal
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s) (C : ℝ)
    (hbound :
      ∀ f : SturmH lam,
        ‖sturmRealHeatLimitCLM lam hlam s hs f -
          sturmRealConstantEquilibrium lam hlam f‖ ≤
        C * ‖f - sturmRealConstantEquilibrium lam hlam f‖) :
    Real.exp (-s * (1 + 2 * lam)) ≤ C := by
  let u : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam 1
  have hu0 : sturmRealConstantEquilibrium lam hlam u = 0 :=
    sturmRealConstantEquilibrium_first_mode_eq_zero lam hlam
  have hunorm : ‖u‖ = 1 :=
    sturmMonicEigenCandidate_realL2_normalized_norm lam hlam 1
  have h := hbound u
  rw [hu0, sub_zero, sub_zero,
    sturmRealHeatLimitCLM_first_mode_norm lam hlam s hs, hunorm, mul_one] at h
  exact h

/-- The genuine full Sturm resolvent has exact first-mode norm,
with multiplier (t+1+2λ)⁻¹. -/
theorem sturmRealPositiveResolventFullCLM_first_mode_norm
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    ‖sturmRealPositiveResolventFullCLM lam t hlam ht
      (sturmMonicEigenCandidate_realL2_normalized lam hlam 1)‖ =
    (t + (1 + 2 * lam))⁻¹ := by
  have heig :
      sturmRealPositiveResolventFullCLM lam t hlam ht
        (sturmMonicEigenCandidate_realL2_normalized lam hlam 1) =
      (t + (1 + 2 * lam))⁻¹ •
        sturmMonicEigenCandidate_realL2_normalized lam hlam 1 := by
    simpa only [Nat.cast_one, one_mul] using
      sturmMonicRealHilbertBasis_full_resolvent_eigen lam t hlam ht 1
  have hc : 0 < t + (1 + 2 * lam) := by linarith
  rw [heig, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hc),
    sturmMonicEigenCandidate_realL2_normalized_norm, mul_one]

/-- The resolvent equilibrium-remainder inequality attains equality
on an actual nonzero weighted-real-L² Gegenbauer mode. -/
theorem sturmRealPositiveResolventFullCLM_equilibrium_bound_attained
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    ∃ f : SturmH lam, f ≠ 0 ∧
      (t + (1 + 2 * lam)) *
        ‖sturmRealPositiveResolventFullCLM lam t hlam ht f -
          t⁻¹ • sturmRealConstantEquilibrium lam hlam f‖ =
      ‖f - sturmRealConstantEquilibrium lam hlam f‖ := by
  let u : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam 1
  have hu0 : sturmRealConstantEquilibrium lam hlam u = 0 :=
    sturmRealConstantEquilibrium_first_mode_eq_zero lam hlam
  have hunorm : ‖u‖ = 1 :=
    sturmMonicEigenCandidate_realL2_normalized_norm lam hlam 1
  have hune : u ≠ 0 := by
    intro heq
    rw [heq, norm_zero] at hunorm
    norm_num at hunorm
  have hc : t + (1 + 2 * lam) ≠ 0 := by
    have hpos : 0 < t + (1 + 2 * lam) := by linarith
    exact hpos.ne'
  refine ⟨u, hune, ?_⟩
  rw [hu0, smul_zero, sub_zero, sub_zero,
    sturmRealPositiveResolventFullCLM_first_mode_norm lam t hlam ht, hunorm]
  exact mul_inv_cancel₀ hc

/-- No larger spectral-gap coefficient than t+1+2λ can hold
uniformly in the resolvent remainder estimate. -/
theorem sturmRealPositiveResolventFullCLM_equilibrium_constant_optimal
    (lam t C : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (hbound :
      ∀ f : SturmH lam,
        C * ‖sturmRealPositiveResolventFullCLM lam t hlam ht f -
          t⁻¹ • sturmRealConstantEquilibrium lam hlam f‖ ≤
        ‖f - sturmRealConstantEquilibrium lam hlam f‖) :
    C ≤ t + (1 + 2 * lam) := by
  let u : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam 1
  have hu0 : sturmRealConstantEquilibrium lam hlam u = 0 :=
    sturmRealConstantEquilibrium_first_mode_eq_zero lam hlam
  have hunorm : ‖u‖ = 1 :=
    sturmMonicEigenCandidate_realL2_normalized_norm lam hlam 1
  have hc : 0 < t + (1 + 2 * lam) := by linarith
  have h := hbound u
  rw [hu0, smul_zero, sub_zero, sub_zero,
    sturmRealPositiveResolventFullCLM_first_mode_norm lam t hlam ht,
    hunorm] at h
  apply (mul_le_mul_iff_of_pos_right (inv_pos.mpr hc)).mp
  calc
    C * (t + (1 + 2 * lam))⁻¹ ≤ 1 := h
    _ = (t + (1 + 2 * lam)) * (t + (1 + 2 * lam))⁻¹ :=
      (mul_inv_cancel₀ hc.ne').symm

#print axioms GegenbauerFock.Ultraspherical.sturmRealConstantEquilibrium_first_mode_eq_zero
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_equilibrium_bound_attained
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_equilibrium_constant_optimal
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_first_mode_norm
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_equilibrium_bound_attained
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_equilibrium_constant_optimal

end GegenbauerFock.Ultraspherical
