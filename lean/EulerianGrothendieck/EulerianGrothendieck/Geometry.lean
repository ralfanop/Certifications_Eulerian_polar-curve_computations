import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
namespace EulerianGrothendieck

/-- The phase obstruction underlying strictness of the four-vector example. -/
theorem phase_constraints_impossible (z u : ℂ)
    (hz : z.im ≠ 0) (hu : Complex.normSq u = 1)
    (h0 : u.re = 0) (h1 : (z * u).re = 0) : False := by
  have hmul : z.im * u.im = 0 := by
    rw [Complex.mul_re, h0] at h1
    linarith
  have hi : u.im = 0 := (mul_eq_zero.mp hmul).resolve_left hz
  rw [Complex.normSq_apply, h0, hi] at hu
  norm_num at hu

/-- Determinant of VV*, with r=Re(z), and |z|=1 accounted for algebraically. -/
theorem frame_determinant_identity (p r : ℝ) :
    (1 + 2 * p) * (3 - 2 * p) - p * (1 - p) * (2 + 2 * r) =
      3 + 2 * p * (1 - p) * (1 - r) := by ring

theorem frame_determinant_positive (p r : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : r ≤ 1) :
    0 < 3 + 2 * p * (1 - p) * (1 - r) := by
  have h1 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have h2 : 0 ≤ 1 - r := sub_nonneg.mpr hr
  positivity

/-- Linear algebra on Hermitian coordinates after the two diagonal constraints. -/
theorem hermitian_offdiagonal_identification (s c t u v : ℝ)
    (hs : s ≠ 0) (ht : t ≠ 0)
    (h3 : 2 * s * u = 0) (h4 : 2 * s * (c * u - t * v) = 0) :
    u = 0 ∧ v = 0 := by
  have h2s : 2 * s ≠ 0 := mul_ne_zero (by norm_num) hs
  have hu : u = 0 := (mul_eq_zero.mp h3).resolve_left h2s
  have hv0 : c * u - t * v = 0 := (mul_eq_zero.mp h4).resolve_left h2s
  have htv : t * v = 0 := by rw [hu] at hv0; linarith
  exact ⟨hu, (mul_eq_zero.mp htv).resolve_left ht⟩

theorem quadratic_phase_identity (x y C S : ℝ) :
    (x*C+y*S)^2 + (x*C-y*S)^2 - ((x*C+y*S)+(x*C-y*S))^2/3 =
      (2/3 : ℝ)*C^2*x^2 + 2*S^2*y^2 := by ring

theorem circle_quadratic_lower (A B x y : ℝ) (hxy : x^2+y^2=1) :
    min A B ≤ A*x^2+B*y^2 := by
  have hA := min_le_left A B
  have hB := min_le_right A B
  have h1 := mul_le_mul_of_nonneg_right hA (sq_nonneg x)
  have h2 := mul_le_mul_of_nonneg_right hB (sq_nonneg y)
  calc
    min A B = min A B * x^2 + min A B * y^2 := by rw [← mul_add, hxy, mul_one]
    _ ≤ A*x^2+B*y^2 := add_le_add h1 h2

theorem eulerian_phase_branch :
    min ((2/3 : ℝ)*Real.pi^2/(Real.pi^2+1)) (2/(Real.pi^2+1)) =
      2/(Real.pi^2+1) := by
  apply min_eq_right
  have hp := Real.pi_gt_three
  have hd : (0 : ℝ) < Real.pi^2+1 := by positivity
  apply (div_le_div_iff_of_pos_right hd).2
  nlinarith

theorem quadratic_circle_isLeast (A B : ℝ) :
    IsLeast {v : ℝ | ∃ x y : ℝ, x^2+y^2=1 ∧ v=A*x^2+B*y^2} (min A B) := by
  constructor
  · by_cases h : A ≤ B
    · refine ⟨1, 0, by norm_num, ?_⟩
      simp [min_eq_left h]
    · refine ⟨0, 1, by norm_num, ?_⟩
      simp [min_eq_right (le_of_not_ge h)]
  · intro z hz
    obtain ⟨x,y,hxy,rfl⟩ := hz
    exact circle_quadratic_lower A B x y hxy

end EulerianGrothendieck

