import SpecialImaginaryPoint.EulerianLegendreOrigin

/-! Actual fourth-order derivative jet of the Eulerian cumulant.
The inverse Taylor remainder and anisotropic limit are separate obligations. -/
namespace M14.EulerianLegendre
noncomputable section

theorem profile_fourth_identity (x : ℝ) :
    4 * (deriv (deriv (deriv profile))) x + x * (deriv (deriv (deriv (deriv profile)))) x = Real.sinh x := by
  have hf : (fun y : ℝ => 3 * (deriv (deriv profile)) y + y * (deriv (deriv (deriv profile))) y) =
      Real.cosh := funext profile_third_identity
  have hP2 : HasDerivAt (deriv (deriv profile)) ((deriv (deriv (deriv profile))) x) x :=
    (profile_analytic x).deriv.deriv.differentiableAt.hasDerivAt
  have hP3 : HasDerivAt (deriv (deriv (deriv profile))) ((deriv (deriv (deriv (deriv profile)))) x) x :=
    (profile_analytic x).deriv.deriv.deriv.differentiableAt.hasDerivAt
  have hd : HasDerivAt
      (fun y : ℝ => 3 * (deriv (deriv profile)) y + y * (deriv (deriv (deriv profile))) y)
      (3 * (deriv (deriv (deriv profile))) x + (1 * (deriv (deriv (deriv profile))) x + x * (deriv (deriv (deriv (deriv profile)))) x)) x :=
    (hP2.const_mul 3).add ((hasDerivAt_id x).mul hP3)
  rw [hf] at hd
  have he := hd.unique (Real.hasDerivAt_cosh x)
  linarith

theorem profile_fifth_identity (x : ℝ) :
    5 * (deriv (deriv (deriv (deriv profile)))) x + x * (deriv (deriv (deriv (deriv (deriv profile))))) x = Real.cosh x := by
  have hf : (fun y : ℝ => 4 * (deriv (deriv (deriv profile))) y + y * (deriv (deriv (deriv (deriv profile)))) y) =
      Real.sinh := funext profile_fourth_identity
  have hP3 : HasDerivAt (deriv (deriv (deriv profile))) ((deriv (deriv (deriv (deriv profile)))) x) x :=
    (profile_analytic x).deriv.deriv.deriv.differentiableAt.hasDerivAt
  have hP4 : HasDerivAt (deriv (deriv (deriv (deriv profile)))) ((deriv (deriv (deriv (deriv (deriv profile))))) x) x :=
    (profile_analytic x).deriv.deriv.deriv.deriv.differentiableAt.hasDerivAt
  have hd : HasDerivAt
      (fun y : ℝ => 4 * (deriv (deriv (deriv profile))) y + y * (deriv (deriv (deriv (deriv profile)))) y)
      (4 * (deriv (deriv (deriv (deriv profile)))) x + (1 * (deriv (deriv (deriv (deriv profile)))) x + x * (deriv (deriv (deriv (deriv (deriv profile))))) x)) x :=
    (hP3.const_mul 4).add ((hasDerivAt_id x).mul hP4)
  rw [hf] at hd
  have he := hd.unique (Real.hasDerivAt_sinh x)
  linarith

theorem profile_third_deriv_zero : (deriv (deriv (deriv profile))) 0 = 0 := by
  have h := profile_fourth_identity 0
  simp only [zero_mul, add_zero, Real.sinh_zero] at h
  linarith

theorem profile_fourth_deriv_zero : (deriv (deriv (deriv (deriv profile)))) 0 = 1 / 5 := by
  have h := profile_fifth_identity 0
  simp only [zero_mul, add_zero, Real.cosh_zero] at h
  linarith

theorem profile_mul_langevin (x : ℝ) : profile x * langevin x = deriv profile x := by
  have hp : profile x ≠ 0 := ne_of_gt (profile_positive x)
  rw [← profile_log_deriv_eq x]
  field_simp [hp]

theorem profile_langevin_first (x : ℝ) :
    deriv profile x * langevin x + profile x * deriv langevin x =
      (deriv (deriv profile)) x := by
  have hf : (fun y : ℝ => profile y * langevin y) = deriv profile :=
    funext profile_mul_langevin
  have hP0 : HasDerivAt profile ((deriv profile) x) x :=
    (profile_analytic x).differentiableAt.hasDerivAt
  have hP1 : HasDerivAt (deriv profile) ((deriv (deriv profile)) x) x :=
    (profile_analytic x).deriv.differentiableAt.hasDerivAt
  have hL0 : HasDerivAt langevin ((deriv langevin) x) x :=
    (langevin_analytic x).differentiableAt.hasDerivAt
  have hd := hP0.mul hL0
  rw [hf] at hd
  exact hd.unique hP1

theorem profile_langevin_second (x : ℝ) :
    (deriv (deriv profile)) x * langevin x + 2 * deriv profile x * deriv langevin x +
      profile x * (deriv (deriv langevin)) x = (deriv (deriv (deriv profile))) x := by
  have hf : (fun y : ℝ => deriv profile y * langevin y + profile y * deriv langevin y) =
      deriv (deriv profile) := funext profile_langevin_first
  have hP0 : HasDerivAt profile ((deriv profile) x) x :=
    (profile_analytic x).differentiableAt.hasDerivAt
  have hP1 : HasDerivAt (deriv profile) ((deriv (deriv profile)) x) x :=
    (profile_analytic x).deriv.differentiableAt.hasDerivAt
  have hP2 : HasDerivAt (deriv (deriv profile)) ((deriv (deriv (deriv profile))) x) x :=
    (profile_analytic x).deriv.deriv.differentiableAt.hasDerivAt
  have hL0 : HasDerivAt langevin ((deriv langevin) x) x :=
    (langevin_analytic x).differentiableAt.hasDerivAt
  have hL1 : HasDerivAt (deriv langevin) ((deriv (deriv langevin)) x) x :=
    (langevin_analytic x).deriv.differentiableAt.hasDerivAt
  have hd := (hP1.mul hL0).add (hP0.mul hL1)
  rw [hf] at hd
  have he := hd.unique hP2
  linarith

theorem profile_langevin_third (x : ℝ) :
    (deriv (deriv (deriv profile))) x * langevin x + 3 * (deriv (deriv profile)) x * deriv langevin x +
      3 * deriv profile x * (deriv (deriv langevin)) x + profile x * (deriv (deriv (deriv langevin))) x =
      (deriv (deriv (deriv (deriv profile)))) x := by
  have hf : (fun y : ℝ => (deriv (deriv profile)) y * langevin y + 2 * deriv profile y * deriv langevin y +
      profile y * (deriv (deriv langevin)) y) = deriv (deriv (deriv profile)) :=
    funext profile_langevin_second
  have hP0 : HasDerivAt profile ((deriv profile) x) x :=
    (profile_analytic x).differentiableAt.hasDerivAt
  have hP1 : HasDerivAt (deriv profile) ((deriv (deriv profile)) x) x :=
    (profile_analytic x).deriv.differentiableAt.hasDerivAt
  have hP2 : HasDerivAt (deriv (deriv profile)) ((deriv (deriv (deriv profile))) x) x :=
    (profile_analytic x).deriv.deriv.differentiableAt.hasDerivAt
  have hP3 : HasDerivAt (deriv (deriv (deriv profile))) ((deriv (deriv (deriv (deriv profile)))) x) x :=
    (profile_analytic x).deriv.deriv.deriv.differentiableAt.hasDerivAt
  have hL0 : HasDerivAt langevin ((deriv langevin) x) x :=
    (langevin_analytic x).differentiableAt.hasDerivAt
  have hL1 : HasDerivAt (deriv langevin) ((deriv (deriv langevin)) x) x :=
    (langevin_analytic x).deriv.differentiableAt.hasDerivAt
  have hL2 : HasDerivAt (deriv (deriv langevin)) ((deriv (deriv (deriv langevin))) x) x :=
    (langevin_analytic x).deriv.deriv.differentiableAt.hasDerivAt
  have hd := ((hP2.mul hL0).add ((hP1.const_mul 2).mul hL1)).add (hP0.mul hL2)
  rw [hf] at hd
  have he := hd.unique hP3
  linarith

theorem langevin_second_deriv_zero : (deriv (deriv langevin)) 0 = 0 := by
  have h := profile_langevin_second 0
  have hz : langevin 0 = 0 := by simp [langevin]
  rw [profile_second_deriv_zero, profile_deriv_zero, profile_zero, hz,
    profile_third_deriv_zero] at h
  linarith

theorem langevin_third_deriv_zero : (deriv (deriv (deriv langevin))) 0 = -(2 / 15) := by
  have h := profile_langevin_third 0
  have hz : langevin 0 = 0 := by simp [langevin]
  rw [profile_third_deriv_zero, profile_second_deriv_zero, profile_deriv_zero,
    profile_zero, hz, langevin_hasDerivAt_zero.deriv, profile_fourth_deriv_zero] at h
  linarith

theorem cumulant_deriv_eq_langevin : deriv cumulant = langevin :=
  funext fun x => (cumulant_hasDerivAt x).deriv

theorem cumulant_zero : cumulant 0 = 0 := by simp [cumulant, profile_zero]

theorem cumulant_first_deriv_zero : deriv cumulant 0 = 0 := by
  rw [cumulant_deriv_eq_langevin]
  simp [langevin]

theorem cumulant_second_deriv_zero : (deriv (deriv cumulant)) 0 = 1 / 3 := by
  rw [cumulant_deriv_eq_langevin]
  exact langevin_hasDerivAt_zero.deriv

theorem cumulant_third_deriv_zero : (deriv (deriv (deriv cumulant))) 0 = 0 := by
  rw [cumulant_deriv_eq_langevin]
  exact langevin_second_deriv_zero

theorem cumulant_fourth_deriv_zero : (deriv (deriv (deriv (deriv cumulant)))) 0 = -(2 / 15) := by
  rw [cumulant_deriv_eq_langevin]
  exact langevin_third_deriv_zero

theorem cumulant_fourth_coefficient : (deriv (deriv (deriv (deriv cumulant)))) 0 / 24 = -(1 / 180) := by
  rw [cumulant_fourth_deriv_zero]
  norm_num

end
end M14.EulerianLegendre

#print axioms M14.EulerianLegendre.profile_fourth_identity
#print axioms M14.EulerianLegendre.profile_fifth_identity
#print axioms M14.EulerianLegendre.profile_third_deriv_zero
#print axioms M14.EulerianLegendre.profile_fourth_deriv_zero
#print axioms M14.EulerianLegendre.profile_mul_langevin
#print axioms M14.EulerianLegendre.profile_langevin_first
#print axioms M14.EulerianLegendre.profile_langevin_second
#print axioms M14.EulerianLegendre.profile_langevin_third
#print axioms M14.EulerianLegendre.langevin_second_deriv_zero
#print axioms M14.EulerianLegendre.langevin_third_deriv_zero
#print axioms M14.EulerianLegendre.cumulant_deriv_eq_langevin
#print axioms M14.EulerianLegendre.cumulant_zero
#print axioms M14.EulerianLegendre.cumulant_first_deriv_zero
#print axioms M14.EulerianLegendre.cumulant_second_deriv_zero
#print axioms M14.EulerianLegendre.cumulant_third_deriv_zero
#print axioms M14.EulerianLegendre.cumulant_fourth_deriv_zero
#print axioms M14.EulerianLegendre.cumulant_fourth_coefficient
