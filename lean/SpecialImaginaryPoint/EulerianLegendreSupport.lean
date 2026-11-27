import SpecialImaginaryPoint.EulerianLegendreOrigin

/-! Actual global support and inverse on the range of the Langevin map.
No surjectivity onto (-1,1) or order-six remainder is asserted here. -/
namespace M14.EulerianLegendre
noncomputable section

theorem cumulant_support_strict (x y : ℝ) (hxy : y ≠ x) :
    cumulant x + langevin x * (y - x) < cumulant y := by
  let g : ℝ → ℝ := fun t => cumulant t - langevin x * t
  have hg (t : ℝ) : HasDerivAt g (langevin t - langevin x) t := by
    have hlin : HasDerivAt (fun y : ℝ => langevin x * y) (langevin x) t := by
      simpa only [mul_one, id_eq] using (hasDerivAt_id t).const_mul (langevin x)
    change HasDerivAt (fun y : ℝ => cumulant y - langevin x * y) (langevin t - langevin x) t
    exact (cumulant_hasDerivAt t).sub hlin
  rcases lt_or_gt_of_ne hxy with h | h
  · have hm : StrictMonoOn (fun t : ℝ => -g t) (Set.Iic x) := by
      apply strictMonoOn_of_deriv_pos (convex_Iic x)
      · intro t ht
        exact (hg t).neg.continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Iic] at ht
        have hn : HasDerivAt (fun y : ℝ => -g y) (-(langevin t - langevin x)) t := (hg t).neg
        rw [hn.deriv]
        have hh := langevin_strictMono (show t < x from ht)
        linarith
    have hh := hm (show y ∈ Set.Iic x from h.le) (Set.mem_Iic.mpr (le_refl x)) h
    dsimp [g] at hh
    linarith
  · have hm : StrictMonoOn g (Set.Ici x) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici x)
      · intro t ht
        exact (hg t).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        rw [(hg t).deriv]
        exact sub_pos.mpr (langevin_strictMono (show x < t from ht))
    have hh := hm (Set.mem_Ici.mpr (le_refl x)) (show y ∈ Set.Ici x from h.le) h
    dsimp [g] at hh
    linarith

theorem cumulant_support (x y : ℝ) :
    cumulant x + langevin x * (y - x) ≤ cumulant y := by
  by_cases h : y = x
  · subst y
    simp
  · exact (cumulant_support_strict x y h).le

theorem conjugate_langevin_eq_stationary (x : ℝ) :
    conjugate (langevin x) = stationary x := by
  rw [stationary]
  have h := conjugate_eq_of_support (langevin x) x (fun y => by
    linarith [cumulant_support x y])
  simpa [mul_comm] using h

theorem langevin_deriv_pos (x : ℝ) : 0 < deriv langevin x := by
  by_cases h : x = 0
  · subst x
    rw [langevin_hasDerivAt_zero.deriv]
    norm_num
  · exact langevin_deriv_positive_of_ne x h

def inverseLangevin : ℝ → ℝ := Function.invFun langevin

theorem inverseLangevin_left : Function.LeftInverse inverseLangevin langevin :=
  Function.leftInverse_invFun langevin_strictMono.injective

theorem inverseLangevin_hasStrictDerivAt (x : ℝ) :
    HasStrictDerivAt inverseLangevin (deriv langevin x)⁻¹ (langevin x) := by
  have h : HasStrictDerivAt langevin (deriv langevin x) x :=
    (langevin_analytic x).hasStrictDerivAt
  exact h.to_local_left_inverse (ne_of_gt (langevin_deriv_pos x))
    (Filter.Eventually.of_forall inverseLangevin_left)

theorem inverseLangevin_hasDerivAt_zero :
    HasDerivAt inverseLangevin 3 0 := by
  have h := (inverseLangevin_hasStrictDerivAt 0).hasDerivAt
  rw [langevin_hasDerivAt_zero.deriv] at h
  simpa [langevin] using h

theorem conjugate_eq_inverse_on_range (m : ℝ) (hm : m ∈ Set.range langevin) :
    conjugate m = m * inverseLangevin m - cumulant (inverseLangevin m) := by
  rcases hm with ⟨x, rfl⟩
  rw [inverseLangevin_left x, conjugate_langevin_eq_stationary, stationary, mul_comm]

end
end M14.EulerianLegendre

#print axioms M14.EulerianLegendre.cumulant_support_strict
#print axioms M14.EulerianLegendre.cumulant_support
#print axioms M14.EulerianLegendre.conjugate_langevin_eq_stationary
#print axioms M14.EulerianLegendre.langevin_deriv_pos
#print axioms M14.EulerianLegendre.inverseLangevin_left
#print axioms M14.EulerianLegendre.inverseLangevin_hasStrictDerivAt
#print axioms M14.EulerianLegendre.inverseLangevin_hasDerivAt_zero
#print axioms M14.EulerianLegendre.conjugate_eq_inverse_on_range
