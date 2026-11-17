import Mathlib

/-! M14 §2.1 and §8.5: pole modulus and exact local quartic algebra.
The analytic classification and real projective normalization are separate
obligations, not consequences of the polynomial identities alone. -/
namespace Manuscript14.DominantPole

noncomputable def kappa : ℝ := Real.pi / Real.sqrt 8

noncomputable def arcModulus (θ : ℝ) : ℝ :=
  |θ| / (2 * Real.sin (|θ| / 2))

theorem sin_ratio_strict (x y : ℝ) (hx : 0 < x) (hxy : x < y)
    (hy : y < Real.pi) : x / Real.sin x < y / Real.sin y := by
  have hy0 : 0 < y := hx.trans hxy
  have hr : 0 < x / y := div_pos hx hy0
  have hr1 : x / y < 1 := (div_lt_one hy0).2 hxy
  have hc : (1 - x / y) * Real.sin 0 + (x / y) * Real.sin y <
      Real.sin ((1 - x / y) * 0 + (x / y) * y) := by
    have h := Real.strictConcaveOn_sin_Icc.2
      (show (0 : ℝ) ∈ Set.Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
      (show y ∈ Set.Icc 0 Real.pi from ⟨hy0.le, hy.le⟩)
      (ne_of_lt hy0) (sub_pos.mpr hr1) hr
      (show 1 - x / y + x / y = 1 by ring)
    simpa only [smul_eq_mul] using h
  have he : (x / y) * y = x := by field_simp [ne_of_gt hy0]
  simp only [Real.sin_zero, mul_zero, zero_add, he] at hc
  apply (div_lt_div_iff₀ (Real.sin_pos_of_pos_of_lt_pi hx (hxy.trans hy))
      (Real.sin_pos_of_pos_of_lt_pi hy0 hy)).2
  calc
    x * Real.sin y = y * ((x / y) * Real.sin y) := by field_simp [ne_of_gt hy0] <;> ring
    _ < y * Real.sin x := mul_lt_mul_of_pos_left hc hy0

theorem sqrt_eight : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

theorem endpoint_ratio : (Real.pi / 4) / Real.sin (Real.pi / 4) = kappa := by
  rw [Real.sin_pi_div_four, kappa, sqrt_eight]
  have h : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp <;> ring

theorem arc_modulus_eq_ratio (θ : ℝ) :
    arcModulus θ = (|θ| / 2) / Real.sin (|θ| / 2) := by
  unfold arcModulus
  rw [div_div]

theorem arc_minimum (θ : ℝ) (hlo : Real.pi / 2 ≤ |θ|)
    (hhi : |θ| < Real.pi) :
    kappa ≤ arcModulus θ := by
  rw [arc_modulus_eq_ratio, ← endpoint_ratio]
  have h : Real.pi / 4 ≤ |θ| / 2 := by linarith
  rcases h.eq_or_lt with he | hlt
  · rw [he]
  · exact (sin_ratio_strict _ _ (by positivity) hlt (by linarith [Real.pi_pos])).le

theorem arc_minimum_eq_iff (θ : ℝ) (hlo : Real.pi / 2 ≤ |θ|)
    (hhi : |θ| < Real.pi) :
    arcModulus θ = kappa ↔ |θ| = Real.pi / 2 := by
  rw [arc_modulus_eq_ratio, ← endpoint_ratio]
  constructor
  · intro he
    by_contra hn
    have hlt : Real.pi / 4 < |θ| / 2 := by
      have h : Real.pi / 2 < |θ| := lt_of_le_of_ne hlo (Ne.symm hn)
      linarith
    have h := sin_ratio_strict _ _ (by positivity : 0 < Real.pi / 4) hlt
      (by linarith [Real.pi_pos] : |θ| / 2 < Real.pi)
    linarith
  · intro he
    rw [he]
    congr 1 <;> ring

theorem arc_endpoint_positive : arcModulus (Real.pi / 2) = kappa := by
  apply (arc_minimum_eq_iff _ (by rw [abs_of_pos (by positivity : 0 < Real.pi / 2)])
    (by rw [abs_of_pos (by positivity : 0 < Real.pi / 2)]; linarith [Real.pi_pos])).2
  exact abs_of_pos (by positivity)

theorem arc_endpoint_negative : arcModulus (-Real.pi / 2) = kappa := by
  have h : |-Real.pi / 2| = Real.pi / 2 := by
    rw [neg_div, abs_neg, abs_of_pos (by positivity : 0 < Real.pi / 2)]
  apply (arc_minimum_eq_iff _ (by rw [h]) (by rw [h]; linarith [Real.pi_pos])).2 h

theorem arc_isLeast : IsLeast (arcModulus '' {θ : ℝ | Real.pi / 2 ≤ |θ| ∧ |θ| < Real.pi}) kappa := by
  constructor
  · refine ⟨Real.pi / 2, ?_, arc_endpoint_positive⟩
    change Real.pi / 2 ≤ |Real.pi / 2| ∧ |Real.pi / 2| < Real.pi
    rw [abs_of_pos (by positivity : 0 < Real.pi / 2)]
    exact ⟨le_rfl, by linarith [Real.pi_pos]⟩
  · rintro z ⟨θ, ⟨hlo, hhi⟩, rfl⟩
    exact arc_minimum θ hlo hhi

/-- The principal numerator is strictly smaller than any shifted numerator.
The assumption on j is satisfied by every nonzero integer. -/
theorem unique_numerator (θ j : ℝ) (hθ : |θ| < Real.pi) (hj : 1 ≤ |j|) :
    |θ| < |θ + 2 * Real.pi * j| := by
  have h := abs_add_le (θ + 2 * Real.pi * j) (-θ)
  have he : θ + 2 * Real.pi * j + -θ = 2 * Real.pi * j := by ring
  rw [he, abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos Real.pi_pos] at h
  nlinarith [mul_le_mul_of_nonneg_left hj (show 0 ≤ 2 * Real.pi by positivity)]

theorem separation_lower (d : ℝ) (hd : 0 < d) (h : d ≤ Real.sqrt 2) :
    4 * kappa ≤ 2 * Real.pi / d := by
  rw [kappa, sqrt_eight]
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have he : 4 * (Real.pi / (2 * Real.sqrt 2)) = 2 * Real.pi / Real.sqrt 2 := by
    field_simp <;> ring
  rw [he]
  exact div_le_div_of_nonneg_left (by positivity) hd h

#print axioms sin_ratio_strict
#print axioms sqrt_eight
#print axioms endpoint_ratio
#print axioms arc_modulus_eq_ratio
#print axioms arc_minimum
#print axioms arc_minimum_eq_iff
#print axioms arc_endpoint_positive
#print axioms arc_endpoint_negative
#print axioms arc_isLeast
#print axioms unique_numerator
#print axioms separation_lower
end Manuscript14.DominantPole

namespace Manuscript14.QuarticE6

def Q (u v : ℝ) : ℝ := u^4 - u^2*v^2/2 + v^4/32 + v^3

def A (u w : ℝ) : ℝ :=
  1 + u^4/41472 - u^2*w/1728 - u^2/108 + w^2/192 + w/12

def B (u w : ℝ) : ℝ := 1 + u^2/48 - w/32

theorem local_factorization (u w : ℝ) :
    Q u (u^2/6-w) = u^4*A u w - w^3*B u w := by
  unfold Q A B
  ring

theorem unit_values : A 0 0 = 1 ∧ B 0 0 = 1 := by
  norm_num [A, B]

theorem unit_continuity : Continuous (fun p : ℝ × ℝ => A p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => B p.1 p.2) := by
  unfold A B
  constructor <;> fun_prop

def D (t : ℝ) : ℝ := 1-t^2/2+t^4/32

theorem denominator_near_origin (t : ℝ) (h : |t| ≤ 1) : 1/2 ≤ D t := by
  unfold D
  have h1 := abs_le.mp h
  have h2 : t^2 ≤ 1 := by nlinarith [mul_nonneg (show 0 ≤ 1-t by linarith [h1.2])
    (show 0 ≤ 1+t by linarith [h1.1])]
  nlinarith [sq_nonneg (t^2)]

theorem parameterization (t : ℝ) (h : D t ≠ 0) :
    Q (t^3 / D t) (-t^4 / D t) = 0 := by
  unfold Q
  field_simp [h] <;> unfold D <;> ring

theorem parameterization_near_origin (t : ℝ) (h : |t| ≤ 1) :
    Q (t^3 / D t) (-t^4 / D t) = 0 := by
  apply parameterization
  have hd := denominator_near_origin t h
  linarith

#print axioms local_factorization
#print axioms unit_values
#print axioms unit_continuity
#print axioms denominator_near_origin
#print axioms parameterization
#print axioms parameterization_near_origin
end Manuscript14.QuarticE6
