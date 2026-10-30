import EulerianGrothendieck.Geometry
import Mathlib.Analysis.Complex.Norm

noncomputable section
namespace EulerianGrothendieck

/-- A uniform quadratic remainder for the complex modulus; no analyticity or
Taylor estimate is left as a hypothesis. -/
theorem complex_modulus_remainder (w : ℂ) (hw : ‖w‖ ≤ 1/2) :
    0 ≤ ‖1+w‖-1-w.re ∧ ‖1+w‖-1-w.re ≤ ‖w‖^2 := by
  have hr := Complex.re_le_norm (1+w)
  have ha := Complex.abs_re_le_norm w
  have hb := Complex.sq_norm w
  have hc := Complex.sq_norm (1+w)
  simp only [Complex.add_re, Complex.one_re] at hr
  rw [Complex.normSq_apply] at hb hc
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_add] at hc
  have hamin : -(1/2:ℝ) ≤ w.re := by
    have hh := (abs_le.mp (ha.trans hw)).1
    linarith
  have he : (‖1+w‖-1-w.re)*(‖1+w‖+1+w.re) = w.im^2 := by nlinarith [hc]
  have he0 : 0 ≤ ‖1+w‖-1-w.re := by linarith
  have hd : 1 ≤ ‖1+w‖+1+w.re := by linarith
  refine ⟨he0, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hd he0
  nlinarith [sq_nonneg w.re]

/-- Squaring the modulus deviation gives a uniform cubic error. -/
theorem complex_modulus_squared_remainder (w : ℂ) (hw : ‖w‖ ≤ 1/2) :
    |(‖1+w‖-1)^2-w.re^2| ≤ 3*‖w‖^3 := by
  obtain ⟨h0,h1⟩ := complex_modulus_remainder w hw
  have ha := Complex.abs_re_le_norm w
  have hn := norm_nonneg w
  have hab : |‖1+w‖-1| ≤ ‖w‖ := by
    simpa using abs_norm_sub_norm_le (1+w) (1:ℂ)
  have he : (‖1+w‖-1)^2-w.re^2 =
      (‖1+w‖-1-w.re)*((‖1+w‖-1)+w.re) := by ring
  rw [he, abs_mul, abs_of_nonneg h0]
  calc
    _ ≤ ‖w‖^2*(|(‖1+w‖-1)|+|w.re|) :=
      mul_le_mul h1 (abs_add_le _ _) (abs_nonneg _) (sq_nonneg _)
    _ ≤ ‖w‖^2*(‖w‖+‖w‖) := mul_le_mul_of_nonneg_left (add_le_add hab ha) (sq_nonneg _)
    _ ≤ 3*‖w‖^3 := by nlinarith [pow_nonneg hn 3]

end EulerianGrothendieck
