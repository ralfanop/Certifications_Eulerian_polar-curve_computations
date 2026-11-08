import Mathlib

/-!
# Manuscript 14, version 14.118 (8 November 2026): the Langevin magnetisation curve of Section 4.5

Kernel-checked statements behind Section 4.5 and the caption of Figure 1 (equation numbers of version
14.118). `langevin x = coth x - 1/x` is the Langevin function and `magn H = 1/2 + langevin (H/2)/2` the
magnetisation curve (44). The numerical values of Section 4.5, Table 1 and Figures 1-3 are certified in
`numerics/arb/manuscript14_v14118_section45_figures_arb.py`.

* `langevin_neg`: the Langevin function is odd;
* `magn_neg`: the symmetry `m(-H) = 1 - m(H)` used in Section 4.5;
* `coth_half`: `coth(H/2) = (e^H + 1)/(e^H - 1)` for `H ≠ 0`;
* `magn_exact`: `m(H) = 1 + 1/(e^H - 1) - 1/H` for `H ≠ 0`;
* `magn_bounds`: `1 - 1/H < m(H) < 1` for `H > 0`;
* `magn_bounds_neg`: `0 < m(H) < -1/H` for `H < 0`;
* `mul_one_sub_magn`: `H (1 - m(H)) = 1 - H/(e^H - 1)` for `H ≠ 0`;
* `tendsto_mul_one_sub_magn`, `tendsto_neg_mul_magn`: `H (1 - m(H)) → 1` as `H → +∞` and
  `-H m(H) → 1` as `H → -∞`, the saturation values `1` and `0` of the caption of Figure 1 approached
  as `1/|H|` when `|H| → ∞`.
-/

namespace SpecialImaginaryPoint.V14118Section45

open Filter Topology

/-- The Langevin function `coth x - 1/x`. -/
noncomputable def langevin (x : ℝ) : ℝ := Real.cosh x / Real.sinh x - 1 / x

/-- The magnetisation curve (44), `m(H) = 1/2 + L(H/2)/2`. -/
noncomputable def magn (H : ℝ) : ℝ := 1 / 2 + langevin (H / 2) / 2

theorem langevin_neg (x : ℝ) : langevin (-x) = -langevin x := by
  unfold langevin
  rw [Real.cosh_neg, Real.sinh_neg, div_neg, div_neg]
  ring

theorem magn_neg (H : ℝ) : magn (-H) = 1 - magn H := by
  unfold magn
  rw [neg_div, langevin_neg]
  ring

theorem exp_sub_one_ne_zero {H : ℝ} (hH : H ≠ 0) : Real.exp H - 1 ≠ 0 := by
  intro h
  apply hH
  have h1 : Real.exp H = 1 := by linarith
  simpa using h1

theorem coth_half (H : ℝ) (hH : H ≠ 0) :
    Real.cosh (H / 2) / Real.sinh (H / 2) = (Real.exp H + 1) / (Real.exp H - 1) := by
  have hsq : Real.exp H = Real.exp (H / 2) * Real.exp (H / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpq : Real.exp (H / 2) * Real.exp (-(H / 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hs : Real.sinh (H / 2) ≠ 0 := by
    intro h
    apply hH
    have h2 : H / 2 = 0 := by simpa using h
    linarith
  rw [div_eq_div_iff hs (exp_sub_one_ne_zero hH), Real.cosh_eq, Real.sinh_eq, hsq]
  linear_combination (Real.exp (H / 2)) * hpq

theorem magn_exact (H : ℝ) (hH : H ≠ 0) :
    magn H = 1 + 1 / (Real.exp H - 1) - 1 / H := by
  have he1 : Real.exp H - 1 ≠ 0 := exp_sub_one_ne_zero hH
  unfold magn langevin
  rw [coth_half H hH]
  field_simp <;> ring

theorem magn_bounds (H : ℝ) (hH : 0 < H) : 1 - 1 / H < magn H ∧ magn H < 1 := by
  have he : H + 1 < Real.exp H := Real.add_one_lt_exp hH.ne'
  have hpos : 0 < Real.exp H - 1 := by linarith
  rw [magn_exact H hH.ne']
  constructor
  · have h1 : 0 < 1 / (Real.exp H - 1) := one_div_pos.mpr hpos
    linarith
  · have h1 : 1 / (Real.exp H - 1) < 1 / H := one_div_lt_one_div_of_lt hH (by linarith)
    linarith

theorem magn_bounds_neg (H : ℝ) (hH : H < 0) : 0 < magn H ∧ magn H < -1 / H := by
  have h := magn_bounds (-H) (by linarith)
  rw [magn_neg] at h
  obtain ⟨h1, h2⟩ := h
  have h3 : 1 / -H = -1 / H := by rw [div_neg, neg_div]
  constructor
  · linarith
  · linarith

theorem mul_one_sub_magn (H : ℝ) (hH : H ≠ 0) :
    H * (1 - magn H) = 1 - H / (Real.exp H - 1) := by
  have he1 : Real.exp H - 1 ≠ 0 := exp_sub_one_ne_zero hH
  rw [magn_exact H hH]
  field_simp <;> ring

theorem tendsto_mul_one_sub_magn :
    Tendsto (fun H : ℝ => H * (1 - magn H)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun H : ℝ => H ^ 1 * Real.exp (-H)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h2 : Tendsto (fun H : ℝ => 1 - Real.exp (-H)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero
  rw [sub_zero] at h2
  have h3 : Tendsto (fun H : ℝ => 1 - H ^ 1 * Real.exp (-H) / (1 - Real.exp (-H))) atTop
      (𝓝 (1 - 0 / 1)) :=
    tendsto_const_nhds.sub (h1.div h2 one_ne_zero)
  rw [zero_div, sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with H hH
  show 1 - H ^ 1 * Real.exp (-H) / (1 - Real.exp (-H)) = H * (1 - magn H)
  rw [mul_one_sub_magn H hH.ne', pow_one]
  congr 1
  have he1 : Real.exp H - 1 ≠ 0 := exp_sub_one_ne_zero hH.ne'
  have hlt : Real.exp (-H) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hq : 1 - Real.exp (-H) ≠ 0 := (by linarith : (0 : ℝ) < 1 - Real.exp (-H)).ne'
  have hpq : Real.exp (-H) * Real.exp H = 1 := by
    rw [← Real.exp_add]
    simp
  rw [div_eq_div_iff hq he1]
  linear_combination H * hpq

theorem tendsto_neg_mul_magn :
    Tendsto (fun H : ℝ => -H * magn H) atBot (𝓝 1) := by
  refine (tendsto_mul_one_sub_magn.comp tendsto_neg_atBot_atTop).congr (fun H => ?_)
  show -H * (1 - magn (-H)) = -H * magn H
  rw [magn_neg]
  ring

end SpecialImaginaryPoint.V14118Section45

#print axioms SpecialImaginaryPoint.V14118Section45.langevin_neg
#print axioms SpecialImaginaryPoint.V14118Section45.magn_neg
#print axioms SpecialImaginaryPoint.V14118Section45.coth_half
#print axioms SpecialImaginaryPoint.V14118Section45.magn_exact
#print axioms SpecialImaginaryPoint.V14118Section45.magn_bounds
#print axioms SpecialImaginaryPoint.V14118Section45.magn_bounds_neg
#print axioms SpecialImaginaryPoint.V14118Section45.mul_one_sub_magn
#print axioms SpecialImaginaryPoint.V14118Section45.tendsto_mul_one_sub_magn
#print axioms SpecialImaginaryPoint.V14118Section45.tendsto_neg_mul_magn
