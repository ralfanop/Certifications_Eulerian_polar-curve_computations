import Mathlib
open intervalIntegral
open scoped Real
noncomputable section
namespace Manuscript14V14122Fourier

def entireBox (z : ℂ) : ℂ := if z = 0 then 1 else (Complex.exp z-1)/z
def principalBox (u : ℂ) : ℂ := if u = 1 then 1 else (u-1)/Complex.log u

theorem entire_box_integral (z : ℂ) :
    (∫ t : ℝ in (0:ℝ)..(1:ℝ), Complex.exp (z*(t:ℂ))) = entireBox z := by
  by_cases hz : z = 0
  · subst z
    simp [entireBox]
  · rw [entireBox, if_neg hz]
    simpa using (integral_exp_mul_complex (a := (0:ℝ)) (b := (1:ℝ)) (c := z) hz)

theorem global_transform (H θ : ℝ) :
    (∫ t : ℝ in (0:ℝ)..(1:ℝ),
      Complex.exp (((H:ℂ)-Complex.I*(θ:ℂ))*(t:ℂ))) =
      entireBox ((H:ℂ)-Complex.I*(θ:ℂ)) :=
  entire_box_integral _

theorem principal_branch (z : ℂ) (hl : -Real.pi < z.im) (hu : z.im ≤ Real.pi) :
    principalBox (Complex.exp z) = entireBox z := by
  by_cases hz : z = 0
  · subst z
    simp [entireBox,principalBox]
  · have he : Complex.exp z ≠ 1 := by
      intro h
      apply hz
      rw [← Complex.log_exp hl hu, h, Complex.log_one]
    simp [principalBox,entireBox,he,hz,Complex.log_exp hl hu]

/-- The exact counterexample to a global principal-log substitution. -/
theorem counterexample_two_pi :
    entireBox (-(2*(Real.pi:ℂ)*Complex.I)) = 0 ∧
    principalBox (Complex.exp (-(2*(Real.pi:ℂ)*Complex.I))) = 1 := by
  have hz : -(2*(Real.pi:ℂ)*Complex.I) ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  have he : Complex.exp (-(2*(Real.pi:ℂ)*Complex.I)) = 1 := by
    rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  simp [entireBox,principalBox,hz,he]

/-- Normalised Fourier factor for any finite number of independent boxes. -/
theorem normalized_product (z h : ℂ) (n : ℕ) (hn : entireBox h ≠ 0) :
    (entireBox z)^n / (entireBox h)^n = (entireBox z / entireBox h)^n := by
  exact (div_pow _ _ _).symm

#print axioms entire_box_integral
#print axioms global_transform
#print axioms principal_branch
#print axioms counterexample_two_pi
#print axioms normalized_product
end Manuscript14V14122Fourier
