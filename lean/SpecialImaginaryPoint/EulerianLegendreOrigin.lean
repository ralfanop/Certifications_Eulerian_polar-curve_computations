import SpecialImaginaryPoint.EulerianLegendreDuality

/-! Regularize the actual M14 profile at the origin via Mathlib's dslope.
The analytic inverse and order-six remainder are subsequent obligations. -/

namespace M14.EulerianLegendre
noncomputable section

theorem profile_eq_dslope : profile = dslope Real.sinh 0 := by
  funext x
  by_cases hx : x = 0
  · subst x
    rw [profile_zero, dslope_same, (Real.hasDerivAt_sinh 0).deriv]
    simp
  · rw [profile, if_neg hx, dslope_of_ne Real.sinh hx, slope_def_field]
    simp

theorem profile_analytic (x : ℝ) : AnalyticAt ℝ profile x := by
  rw [profile_eq_dslope]
  have h : AnalyticAt ℝ Real.sinh x := Real.analyticAt_sinh
  first
  | exact AnalyticAt.dslope h 0
  | exact h.dslope 0
  | have hh : AnalyticOnNhd ℝ Real.sinh Set.univ := fun y _ => Real.analyticAt_sinh
    exact AnalyticOnNhd.dslope hh 0 x (Set.mem_univ x)
  | by_cases hx : x = 0
    · subst x
      obtain ⟨p, hp⟩ := h
      first
      | exact ⟨p.fslope, hp.dslope_fslope⟩
      | exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
    · have hh : AnalyticWithinAt ℝ Real.sinh Set.univ x := h.analyticWithinAt
      exact analyticWithinAt_univ.mp (AnalyticWithinAt.dslope_of_ne hh hx)

theorem profile_mul_eq_sinh (x : ℝ) : x * profile x = Real.sinh x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [profile, if_neg hx]
    field_simp [hx]

theorem profile_first_identity (x : ℝ) :
    profile x + x * deriv profile x = Real.cosh x := by
  have hf : (fun y : ℝ => y * profile y) = Real.sinh :=
    funext profile_mul_eq_sinh
  have hd : HasDerivAt (fun y : ℝ => y * profile y)
      (1 * profile x + x * deriv profile x) x :=
    (hasDerivAt_id x).mul (profile_analytic x).differentiableAt.hasDerivAt
  rw [hf] at hd
  simpa using hd.unique (Real.hasDerivAt_sinh x)

theorem profile_second_identity (x : ℝ) :
    2 * deriv profile x + x * deriv (deriv profile) x = Real.sinh x := by
  have hf : (fun y : ℝ => profile y + y * deriv profile y) = Real.cosh :=
    funext profile_first_identity
  have h1 : HasDerivAt profile (deriv profile x) x :=
    (profile_analytic x).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (deriv profile) (deriv (deriv profile) x) x :=
    (profile_analytic x).deriv.differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun y : ℝ => profile y + y * deriv profile y)
      (deriv profile x + (1 * deriv profile x + x * deriv (deriv profile) x)) x :=
    h1.add ((hasDerivAt_id x).mul h2)
  rw [hf] at hd
  have he := hd.unique (Real.hasDerivAt_cosh x)
  linarith

theorem profile_third_identity (x : ℝ) :
    3 * deriv (deriv profile) x + x * deriv (deriv (deriv profile)) x =
      Real.cosh x := by
  have hf : (fun y : ℝ => 2 * deriv profile y + y * deriv (deriv profile) y) =
      Real.sinh := funext profile_second_identity
  have h2 : HasDerivAt (deriv profile) (deriv (deriv profile) x) x :=
    (profile_analytic x).deriv.differentiableAt.hasDerivAt
  have h3 : HasDerivAt (deriv (deriv profile)) (deriv (deriv (deriv profile)) x) x :=
    (profile_analytic x).deriv.deriv.differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun y : ℝ => 2 * deriv profile y + y * deriv (deriv profile) y)
      (2 * deriv (deriv profile) x +
        (1 * deriv (deriv profile) x + x * deriv (deriv (deriv profile)) x)) x :=
    (h2.const_mul 2).add ((hasDerivAt_id x).mul h3)
  rw [hf] at hd
  have he := hd.unique (Real.hasDerivAt_sinh x)
  linarith

theorem profile_deriv_zero : deriv profile 0 = 0 := by
  have h := profile_second_identity 0
  simp only [zero_mul, add_zero, Real.sinh_zero] at h
  linarith

theorem profile_second_deriv_zero : deriv (deriv profile) 0 = 1 / 3 := by
  have h := profile_third_identity 0
  simp only [zero_mul, add_zero, Real.cosh_zero] at h
  linarith

theorem cumulant_analytic (x : ℝ) : AnalyticAt ℝ cumulant x := by
  exact (profile_analytic x).log (profile_positive x)

theorem profile_log_deriv_eq (x : ℝ) : deriv profile x / profile x = langevin x := by
  by_cases hx : x = 0
  · subst x
    simp [profile_deriv_zero, langevin]
  · have hp : profile x ≠ 0 := ne_of_gt (profile_positive x)
    have hs := sinh_ne_of_ne x hx
    have hf : x * deriv profile x = Real.cosh x - profile x := by
      linarith [profile_first_identity x]
    calc
      deriv profile x / profile x =
          (x * deriv profile x) / (x * profile x) := by
        field_simp [hx, hp] <;> ring
      _ = (Real.cosh x - profile x) / Real.sinh x := by
        rw [hf, profile_mul_eq_sinh]
      _ = langevin x := by
        rw [profile, if_neg hx, langevin, if_neg hx, langevinRaw]
        field_simp [hx, hs] <;> ring

theorem cumulant_hasDerivAt (x : ℝ) : HasDerivAt cumulant (langevin x) x := by
  have hp : HasDerivAt profile (deriv profile x) x :=
    (profile_analytic x).differentiableAt.hasDerivAt
  have hd := hp.log (ne_of_gt (profile_positive x))
  rw [profile_log_deriv_eq] at hd
  exact hd

theorem langevin_analytic (x : ℝ) : AnalyticAt ℝ langevin x := by
  have hf : deriv cumulant = langevin := funext fun y => (cumulant_hasDerivAt y).deriv
  rw [← hf]
  exact (cumulant_analytic x).deriv

theorem langevin_hasDerivAt_zero : HasDerivAt langevin (1 / 3) 0 := by
  have h1 : HasDerivAt profile (deriv profile 0) 0 :=
    (profile_analytic 0).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (deriv profile) (deriv (deriv profile) 0) 0 :=
    (profile_analytic 0).deriv.differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun y : ℝ => deriv profile y / profile y)
      ((deriv (deriv profile) 0 * profile 0 - deriv profile 0 * deriv profile 0) /
        profile 0 ^ 2) 0 := h2.div h1 (ne_of_gt (profile_positive 0))
  have hf : (fun y : ℝ => deriv profile y / profile y) = langevin :=
    funext profile_log_deriv_eq
  rw [hf] at hd
  simpa [profile_zero, profile_deriv_zero, profile_second_deriv_zero] using hd

theorem langevin_strictMono : StrictMono langevin := by
  have hm : StrictMonoOn langevin (Set.univ : Set ℝ) := by
    apply strictMonoOn_of_deriv_pos convex_univ
    · intro x hx
      exact (langevin_analytic x).continuousAt.continuousWithinAt
    · intro x hx
      by_cases h : x = 0
      · subst x
        rw [langevin_hasDerivAt_zero.deriv]
        norm_num
      · exact langevin_deriv_positive_of_ne x h
  intro x y hxy
  exact hm (Set.mem_univ x) (Set.mem_univ y) hxy

end
end M14.EulerianLegendre

#print axioms M14.EulerianLegendre.profile_eq_dslope
#print axioms M14.EulerianLegendre.profile_analytic
#print axioms M14.EulerianLegendre.profile_mul_eq_sinh
#print axioms M14.EulerianLegendre.profile_first_identity
#print axioms M14.EulerianLegendre.profile_second_identity
#print axioms M14.EulerianLegendre.profile_third_identity
#print axioms M14.EulerianLegendre.profile_deriv_zero
#print axioms M14.EulerianLegendre.profile_second_deriv_zero
#print axioms M14.EulerianLegendre.cumulant_analytic
#print axioms M14.EulerianLegendre.profile_log_deriv_eq
#print axioms M14.EulerianLegendre.cumulant_hasDerivAt
#print axioms M14.EulerianLegendre.langevin_analytic
#print axioms M14.EulerianLegendre.langevin_hasDerivAt_zero
#print axioms M14.EulerianLegendre.langevin_strictMono
