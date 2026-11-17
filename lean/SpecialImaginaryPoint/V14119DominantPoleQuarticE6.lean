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
    have h := strictConcaveOn_sin_Icc.2
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

noncomputable def phase (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

noncomputable def pole (θ j : ℝ) : ℂ :=
  (Complex.log (phase θ) + ((2 * Real.pi * j : ℝ) : ℂ) * Complex.I) / (phase θ - 1)

theorem chord_sq (θ : ℝ) : ‖phase θ - 1‖ ^ 2 = 2 - 2 * Real.cos θ := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [phase, Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem chord (θ : ℝ) (hθ : |θ| < Real.pi) :
    ‖phase θ - 1‖ = 2 * Real.sin (|θ| / 2) := by
  have hs : 0 ≤ Real.sin (|θ| / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hs)).mp
  rw [chord_sq]
  have hcos := Real.cos_two_mul_eq_one_sub (|θ| / 2)
  rw [show 2 * (|θ| / 2) = |θ| by ring, Real.cos_abs] at hcos
  nlinarith

theorem principal_log (θ : ℝ) (hθ : |θ| < Real.pi) :
    Complex.log (phase θ) = (θ : ℂ) * Complex.I := by
  unfold phase
  apply Complex.log_exp
  · simpa [Complex.mul_im] using (abs_lt.mp hθ).1
  · simpa [Complex.mul_im] using (abs_lt.mp hθ).2.le

theorem shifted_pole_norm (θ j : ℝ) (hθ : |θ| < Real.pi) :
    ‖pole θ j‖ = |θ + 2 * Real.pi * j| / (2 * Real.sin (|θ| / 2)) := by
  unfold pole
  rw [principal_log θ hθ, ← add_mul, ← Complex.ofReal_add, norm_div, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, chord θ hθ]

theorem complex_pole_minimum (θ : ℝ) (hlo : Real.pi / 2 ≤ |θ|)
    (hhi : |θ| < Real.pi) : kappa ≤ ‖pole θ 0‖ := by
  rw [shifted_pole_norm θ 0 hhi]
  simp only [mul_zero, add_zero]
  exact arc_minimum θ hlo hhi

theorem complex_pole_minimum_eq_iff (θ : ℝ) (hlo : Real.pi / 2 ≤ |θ|)
    (hhi : |θ| < Real.pi) : ‖pole θ 0‖ = kappa ↔ |θ| = Real.pi / 2 := by
  rw [shifted_pole_norm θ 0 hhi]
  simp only [mul_zero, add_zero]
  exact arc_minimum_eq_iff θ hlo hhi

theorem complex_unique_pole (θ : ℝ) (j : ℤ) (hθ : |θ| < Real.pi)
    (h0 : 0 < |θ|) (hj : j ≠ 0) : ‖pole θ 0‖ < ‖pole θ (j : ℝ)‖ := by
  rw [shifted_pole_norm θ 0 hθ, shifted_pole_norm θ (j : ℝ) hθ]
  simp only [mul_zero, add_zero]
  have hj' : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj
  have hp : 0 < Real.sin (|θ| / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  exact div_lt_div_of_pos_right (unique_numerator θ (j : ℝ) hθ hj') (by positivity)

theorem pole_diff_norm (θ j : ℝ) :
    ‖pole θ j - pole θ 0‖ = 2 * Real.pi * |j| / ‖phase θ - 1‖ := by
  have h : pole θ j - pole θ 0 =
      ((2 * Real.pi * j : ℝ) : ℂ) * Complex.I / (phase θ - 1) := by
    unfold pole
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, add_zero]
    ring
  rw [h, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]

theorem right_semicircle_chord_bound (θ : ℝ) (hθ : 0 ≤ Real.cos θ) :
    ‖phase θ - 1‖ ≤ Real.sqrt 2 := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg 2)).mp
  rw [chord_sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

theorem exact_pole_separation (θ : ℝ) (hθ : |θ| < Real.pi) (h0 : 0 < |θ|) :
    IsLeast ((fun j : ℤ => ‖pole θ (j : ℝ) - pole θ 0‖) '' {j : ℤ | j ≠ 0})
      (2 * Real.pi / ‖phase θ - 1‖) := by
  constructor
  · refine ⟨1, by norm_num, ?_⟩
    rw [pole_diff_norm]
    norm_num
  · rintro z ⟨j, hj, rfl⟩
    rw [pole_diff_norm]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    have hj' : (1 : ℝ) ≤ |(j : ℝ)| := by
      exact_mod_cast Int.one_le_abs (show j ≠ 0 from hj)
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hj' (show 0 ≤ 2 * Real.pi by positivity)

theorem complex_separation_lower (θ : ℝ) (hθ : |θ| < Real.pi)
    (h0 : 0 < |θ|) (hc : 0 ≤ Real.cos θ) :
    4 * kappa ≤ 2 * Real.pi / ‖phase θ - 1‖ := by
  apply separation_lower
  · rw [chord θ hθ]
    have : 0 < Real.sin (|θ| / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    positivity
  · exact right_semicircle_chord_bound θ hc

#print axioms chord_sq
#print axioms chord
#print axioms principal_log
#print axioms shifted_pole_norm
#print axioms complex_pole_minimum
#print axioms complex_pole_minimum_eq_iff
#print axioms complex_unique_pole
#print axioms pole_diff_norm
#print axioms right_semicircle_chord_bound
#print axioms exact_pole_separation
#print axioms complex_separation_lower
end Manuscript14.DominantPole

namespace Manuscript14.QuarticE6

noncomputable def Q (u v : ℝ) : ℝ := u^4 - u^2*v^2/2 + v^4/32 + v^3

noncomputable def A (u w : ℝ) : ℝ :=
  1 + u^4/41472 - u^2*w/1728 - u^2/108 + w^2/192 + w/12

noncomputable def B (u w : ℝ) : ℝ := 1 + u^2/48 - w/32

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

noncomputable def D (t : ℝ) : ℝ := 1-t^2/2+t^4/32

theorem denominator_near_origin (t : ℝ) (h : |t| ≤ 1) : 1/2 ≤ D t := by
  unfold D
  have h1 := abs_le.mp h
  have hprod : 0 ≤ (1-t)*(1+t) := mul_nonneg (by linarith [h1.2]) (by linarith [h1.1])
  have h2 : t^2 ≤ 1 := by nlinarith
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
