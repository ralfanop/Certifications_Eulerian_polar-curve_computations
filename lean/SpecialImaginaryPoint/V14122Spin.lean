import Mathlib
noncomputable section
namespace Manuscript14V14122Spin

/-- Spin-one ideal magnetisation relative to saturation, in the variable y=exp(t). -/
def alignment (y : ℝ) : ℝ := (y^2-1)/(y^2+y+1)

theorem saturation_strict (y : ℝ) (hy : 0 < y) : alignment y < 1 := by
  unfold alignment
  apply (div_lt_iff₀ (by positivity : 0 < y^2+y+1)).2
  nlinarith

theorem inverse_positive (q : ℝ) (hq : 0 ≤ q) (h1 : q < 1) :
    ∃ t : ℝ, alignment (Real.exp t) = q := by
  let s := Real.sqrt (4-3*q^2)
  have hrad : 0 < 4-3*q^2 := by
    nlinarith [mul_nonneg hq (sub_nonneg.mpr h1.le)]
  have hs : s^2 = 4-3*q^2 := Real.sq_sqrt hrad.le
  have hspos : 0 < s := Real.sqrt_pos.2 hrad
  let y := (q+s)/(2*(1-q))
  have hd : 0 < 1-q := by linarith
  have hy : 0 < y := by
    dsimp [y]
    exact div_pos (by linarith) (by positivity)
  have he : 2*(1-q)*y = q+s := by
    dsimp [y]
    field_simp [hd.ne'] <;> ring
  have hh : (2*(1-q)*y-q)^2 = 4-3*q^2 := by
    rw [he, show q+s-q = s by ring, hs]
  have hz : (1-q)*((1-q)*y^2-q*y-(1+q)) = 0 := by
    linear_combination hh / 4
  have hp : (1-q)*y^2-q*y-(1+q) = 0 :=
    (mul_eq_zero.mp hz).resolve_left hd.ne'
  refine ⟨Real.log y, ?_⟩
  rw [Real.exp_log hy]
  unfold alignment
  apply (div_eq_iff (by positivity : y^2+y+1 ≠ 0)).2
  linear_combination hp

theorem inverse_explicit (q : ℝ) (hq : 0 ≤ q) (h1 : q < 1) :
    alignment (Real.exp (Real.log ((q+Real.sqrt (4-3*q^2))/(2*(1-q))))) = q := by
  let s := Real.sqrt (4-3*q^2)
  have hrad : 0 < 4-3*q^2 := by
    nlinarith [mul_nonneg hq (sub_nonneg.mpr h1.le)]
  have hs : s^2 = 4-3*q^2 := Real.sq_sqrt hrad.le
  have hspos : 0 < s := Real.sqrt_pos.2 hrad
  let y := (q+s)/(2*(1-q))
  have hd : 0 < 1-q := by linarith
  have hy : 0 < y := by
    dsimp [y]
    exact div_pos (by linarith) (by positivity)
  change alignment (Real.exp (Real.log y)) = q
  rw [Real.exp_log hy]
  have he : 2*(1-q)*y = q+s := by
    dsimp [y]
    field_simp [hd.ne'] <;> ring
  have hh : (2*(1-q)*y-q)^2 = 4-3*q^2 := by
    rw [he, show q+s-q = s by ring, hs]
  have hz : (1-q)*((1-q)*y^2-q*y-(1+q)) = 0 := by
    linear_combination hh / 4
  have hp := (mul_eq_zero.mp hz).resolve_left hd.ne'
  unfold alignment
  apply (div_eq_iff (by positivity : y^2+y+1 ≠ 0)).2
  linear_combination hp

theorem spin_one_hyperbolic (t : ℝ) :
    alignment (Real.exp t) = 2*Real.sinh t/(1+2*Real.cosh t) := by
  have h : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hden : Real.exp t ^ 2 + Real.exp t + 1 ≠ 0 := by positivity
  have hc : 1+2*Real.cosh t ≠ 0 := by
    nlinarith [Real.cosh_pos t]
  rw [alignment, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  field_simp [h] <;> ring

/-- Exact rational effective-to-saturation moment ratio from the printed constants. -/
theorem printed_moment_ratio :
    (26400:ℚ)/18548 = 6600/4637 := by norm_num

#print axioms saturation_strict
#print axioms inverse_positive
#print axioms inverse_explicit
#print axioms spin_one_hyperbolic
#print axioms printed_moment_ratio
end Manuscript14V14122Spin
