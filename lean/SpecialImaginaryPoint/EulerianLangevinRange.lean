import SpecialImaginaryPoint.EulerianLegendreSupport
import Mathlib.Topology.Order.IntermediateValue

namespace M14.EulerianLegendre
noncomputable section

theorem langevin_positive_lower (x : ℝ) (hx : 0 < x) :
    1 - 1 / x < langevin x := by
  have hs : 0 < Real.sinh x := sinh_pos_of_pos x hx
  have hcs : Real.sinh x < Real.cosh x := by
    rw [Real.sinh_eq, Real.cosh_eq]
    linarith [Real.exp_pos (-x)]
  have hr : 1 < Real.cosh x / Real.sinh x := by
    apply (lt_div_iff₀ hs).2
    simpa using hcs
  rw [langevin, if_neg (ne_of_gt hx), langevinRaw]
  linarith

theorem langevin_positive_upper (x : ℝ) (hx : 0 < x) :
    langevin x < 1 := by
  have hs : 0 < Real.sinh x := sinh_pos_of_pos x hx
  have he : 2 * x + 1 < Real.exp (2 * x) := by
    first
    | exact Real.add_one_lt_exp (by linarith : 2*x ≠ 0)
    | exact Real.add_one_lt_exp (by linarith : 0 < 2*x)
    | linarith [Real.add_one_lt_exp (by linarith : 2*x ≠ 0)]
    | exact?
  have hE : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show 2*x = x+x by ring, Real.exp_add]
  have hprod : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hn : 0 < Real.exp (-x) := Real.exp_pos _
  have hm := mul_lt_mul_of_pos_right he hn
  rw [hE] at hm
  have hm' : (2*x+1) * Real.exp (-x) < Real.exp x := by
    calc
      (2*x+1) * Real.exp (-x) < (Real.exp x * Real.exp x) * Real.exp (-x) := hm
      _ = Real.exp x := by rw [mul_assoc, hprod, mul_one]
  have h : x * (Real.cosh x - Real.sinh x) < Real.sinh x := by
    rw [Real.cosh_eq, Real.sinh_eq]
    linarith
  rw [langevin, if_neg (ne_of_gt hx), langevinRaw]
  have hratio : Real.cosh x / Real.sinh x < 1 + 1 / x := by
    apply (div_lt_iff₀ hs).2
    have h' : Real.cosh x * x < (1 + 1 / x) * Real.sinh x * x := by
      have heq : (1 + 1 / x) * Real.sinh x * x = x * Real.sinh x + Real.sinh x := by
        field_simp [ne_of_gt hx]
        <;> ring
      rw [heq]
      linarith
    exact lt_of_mul_lt_mul_right h' hx.le
  linarith

theorem langevin_mem_open_interval (x : ℝ) : langevin x ∈ Set.Ioo (-1 : ℝ) 1 := by
  have odd : ∀ t : ℝ, langevin (-t) = -langevin t := by
    intro t
    by_cases ht : t = 0
    · simp [ht, langevin]
    · simp [langevin, langevinRaw, ht, Real.sinh_neg, Real.cosh_neg]
      ring
  have hzero : langevin 0 = 0 := by simp [langevin]
  rcases lt_trichotomy x 0 with h | h | h
  · have hp := langevin_positive_upper (-x) (neg_pos.mpr h)
    rw [odd] at hp
    have hn := langevin_strictMono h
    rw [hzero] at hn
    exact ⟨by linarith, by linarith⟩
  · subst x
    rw [hzero]
    norm_num
  · have hp := langevin_positive_upper x h
    have hn := langevin_strictMono h
    rw [hzero] at hn
    exact ⟨by linarith, hp⟩

theorem langevin_range_eq : Set.range langevin = Set.Ioo (-1 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact langevin_mem_open_interval x
  · intro m hm
    have odd : ∀ t : ℝ, langevin (-t) = -langevin t := by
      intro t
      by_cases ht : t = 0
      · simp [ht, langevin]
      · simp [langevin, langevinRaw, ht, Real.sinh_neg, Real.cosh_neg]
        ring
    have hgap : 0 < 1 - |m| := sub_pos.mpr (abs_lt.mpr ⟨hm.1, hm.2⟩)
    let R : ℝ := 2 / (1 - |m|)
    have hR : 0 < R := div_pos (by norm_num) hgap
    have hRinv : 1 / R = (1 - |m|) / 2 := by
      dsimp [R]
      field_simp [ne_of_gt hgap]
    have hL := langevin_positive_lower R hR
    rw [hRinv] at hL
    have hpos : m ≤ langevin R := by linarith [le_abs_self m]
    have hneg : langevin (-R) ≤ m := by
      rw [odd]
      linarith [neg_abs_le m]
    have hc : Continuous langevin := continuous_iff_continuousAt.mpr
      (fun x => (langevin_analytic x).continuousAt)
    have hh := intermediate_value_Icc (by linarith : -R ≤ R) hc.continuousOn
      (show m ∈ Set.Icc (langevin (-R)) (langevin R) from ⟨hneg, hpos⟩)
    rcases hh with ⟨x, hx, he⟩
    exact ⟨x, he⟩

theorem inverseLangevin_right_on_interval (m : ℝ) (hm : m ∈ Set.Ioo (-1 : ℝ) 1) :
    langevin (inverseLangevin m) = m := by
  rw [← langevin_range_eq] at hm
  rcases hm with ⟨x, rfl⟩
  rw [inverseLangevin_left x]

theorem conjugate_eq_inverse_on_interval (m : ℝ) (hm : m ∈ Set.Ioo (-1 : ℝ) 1) :
    conjugate m = m * inverseLangevin m - cumulant (inverseLangevin m) :=
  conjugate_eq_inverse_on_range m (langevin_range_eq.symm ▸ hm)

end
end M14.EulerianLegendre

#print axioms M14.EulerianLegendre.langevin_positive_lower
#print axioms M14.EulerianLegendre.langevin_positive_upper
#print axioms M14.EulerianLegendre.langevin_mem_open_interval
#print axioms M14.EulerianLegendre.langevin_range_eq
#print axioms M14.EulerianLegendre.inverseLangevin_right_on_interval
#print axioms M14.EulerianLegendre.conjugate_eq_inverse_on_interval
