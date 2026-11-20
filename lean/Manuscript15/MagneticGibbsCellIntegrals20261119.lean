import Mathlib

/-! M15 §8.4, actual Lebesgue interval integrals for the exponential
density's nearest odd-site rounding cost. This is the local analytic
evaluation; the global countable-cell integral decomposition and
magnetic convergence remain separate obligations. -/

open MeasureTheory Set
noncomputable section
namespace Manuscript15.MagneticGibbs.CellIntegrals

def primitive1 (r x : ℝ) : ℝ :=
  Real.exp (-r*x) * (-(x-1)/r - 1/r^2)

def primitive2 (r x : ℝ) : ℝ :=
  Real.exp (-r*x) * (-(x-1)^2/r - 2*(x-1)/r^2 - 2/r^3)

theorem primitive1_deriv (r x : ℝ) (hr : r ≠ 0) :
    HasDerivAt (primitive1 r) (Real.exp (-r*x)*(x-1)) x := by
  unfold primitive1
  have he := ((hasDerivAt_id x).const_mul (-r)).exp
  have hp := (((hasDerivAt_id x).sub_const 1).neg.div_const r).sub_const (1/r^2)
  have h : HasDerivAt (fun t : ℝ => Real.exp (-r*t) * (-(t-1)/r - 1/r^2))
      (Real.exp (-r*x)*(-r*1) * (-(x-1)/r - 1/r^2) +
        Real.exp (-r*x)*(-1/r)) x := by
    first | exact he.mul hp | simpa [id] using he.mul hp
  convert h using 1 <;> first | rfl | (field_simp [hr] <;> ring)

theorem primitive2_deriv (r x : ℝ) (hr : r ≠ 0) :
    HasDerivAt (primitive2 r) (Real.exp (-r*x)*(x-1)^2) x := by
  unfold primitive2
  have he := ((hasDerivAt_id x).const_mul (-r)).exp
  have hp := ((((hasDerivAt_id x).sub_const 1).pow 2).neg.div_const r).sub
    (((hasDerivAt_id x).sub_const 1).const_mul 2 |>.div_const (r^2))
  have h := hp.sub_const (2/r^3)
  have hm : HasDerivAt (fun t : ℝ => Real.exp (-r*t) *
      (-(t-1)^2/r - 2*(t-1)/r^2 - 2/r^3))
      (Real.exp (-r*x)*(-r*1) * (-(x-1)^2/r - 2*(x-1)/r^2 - 2/r^3) +
        Real.exp (-r*x)*(-(2*(x-1)^1*1)/r - 2*1/r^2)) x := by
    first | exact he.mul h | simpa [id] using he.mul h
  convert hm using 1 <;> first | rfl | (field_simp [hr] <;> ring)

theorem signed_cell_integral (r a b : ℝ) (hr : r ≠ 0) :
    (∫ x in a..b, Real.exp (-r*x)*(x-1)) =
      primitive1 r b - primitive1 r a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    exact primitive1_deriv r x hr
  · exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (-r*x)*(x-1))).intervalIntegrable a b

theorem square_cell_integral (r a b : ℝ) (hr : r ≠ 0) :
    (∫ x in a..b, Real.exp (-r*x)*(x-1)^2) =
      primitive2 r b - primitive2 r a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    exact primitive2_deriv r x hr
  · exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (-r*x)*(x-1)^2)).intervalIntegrable a b

theorem absolute_cell_integral (r : ℝ) (hr : r ≠ 0) :
    (∫ x in (0:ℝ)..2, Real.exp (-r*x)*|x-1|) =
      (1-Real.exp (-2*r))/r -
      (1-2*Real.exp (-r)+Real.exp (-2*r))/r^2 := by
  have hc : Continuous (fun x : ℝ => Real.exp (-r*x)*|x-1|) := by fun_prop
  have hl : (∫ x in (0:ℝ)..1, Real.exp (-r*x)*|x-1|) =
      -(∫ x in (0:ℝ)..1, Real.exp (-r*x)*(x-1)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    change Real.exp (-r*x)*|x-1| = -(Real.exp (-r*x)*(x-1))
    rw [abs_of_nonpos (by linarith [hx.2] : x-1 ≤ 0)]
    ring
  have hh : (∫ x in (1:ℝ)..2, Real.exp (-r*x)*|x-1|) =
      (∫ x in (1:ℝ)..2, Real.exp (-r*x)*(x-1)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    change Real.exp (-r*x)*|x-1| = Real.exp (-r*x)*(x-1)
    rw [abs_of_nonneg (by linarith [hx.1] : 0 ≤ x-1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 1) (hc.intervalIntegrable 1 2), hl, hh,
    signed_cell_integral r 0 1 hr, signed_cell_integral r 1 2 hr]
  unfold primitive1
  simp only [mul_zero, Real.exp_zero, mul_one]
  rw [show -r * (2:ℝ) = -2*r by ring]
  field_simp [hr] <;> ring

theorem quadratic_cell_integral (r : ℝ) (hr : r ≠ 0) :
    (∫ x in (0:ℝ)..2, Real.exp (-r*x)*(x-1)^2) =
      (1-Real.exp (-2*r))/r -
      2*(1+Real.exp (-2*r))/r^2 +
      2*(1-Real.exp (-2*r))/r^3 := by
  rw [square_cell_integral r 0 2 hr]
  unfold primitive2
  simp only [mul_zero, Real.exp_zero, mul_one]
  rw [show -r * (2:ℝ) = -2*r by ring]
  field_simp [hr] <;> ring

theorem normalized_absolute_cell_integral (r : ℝ) (hr : 0 < r) :
    r/(1-Real.exp (-2*r)) * (∫ x in (0:ℝ)..2, Real.exp (-r*x)*|x-1|) =
      1-(1-Real.exp (-r))/(r*(1+Real.exp (-r))) := by
  rw [absolute_cell_integral r hr.ne']
  have hq : Real.exp (-2*r) = Real.exp (-r)^2 := by
    rw [show -2*r = -r + -r by ring, Real.exp_add, pow_two]
  have h₁ : 1-Real.exp (-2*r) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  have h₂ : 1+Real.exp (-r) ≠ 0 := by positivity
  rw [hq] at h₁ ⊢
  field_simp [hr.ne',h₁,h₂] <;> ring

theorem normalized_quadratic_cell_integral (r : ℝ) (hr : 0 < r) :
    r/(1-Real.exp (-2*r)) * (∫ x in (0:ℝ)..2, Real.exp (-r*x)*(x-1)^2) =
      1 + 2/r^2 - (2/r)*((1+Real.exp (-2*r))/(1-Real.exp (-2*r))) := by
  rw [quadratic_cell_integral r hr.ne']
  have hq : 1-Real.exp (-2*r) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  set q := Real.exp (-2*r) at hq ⊢
  field_simp [hr.ne',hq] <;> ring

end Manuscript15.MagneticGibbs.CellIntegrals

#print axioms Manuscript15.MagneticGibbs.CellIntegrals.primitive1_deriv
#print axioms Manuscript15.MagneticGibbs.CellIntegrals.primitive2_deriv
#print axioms Manuscript15.MagneticGibbs.CellIntegrals.signed_cell_integral
#print axioms Manuscript15.MagneticGibbs.CellIntegrals.square_cell_integral
#print axioms Manuscript15.MagneticGibbs.CellIntegrals.absolute_cell_integral
#print axioms Manuscript15.MagneticGibbs.CellIntegrals.quadratic_cell_integral
#print axioms Manuscript15.MagneticGibbs.CellIntegrals.normalized_absolute_cell_integral
#print axioms Manuscript15.MagneticGibbs.CellIntegrals.normalized_quadratic_cell_integral
