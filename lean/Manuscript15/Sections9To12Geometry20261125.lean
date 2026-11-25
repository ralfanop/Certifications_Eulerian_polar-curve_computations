import Mathlib

/-! M15 §§9–12, 25 Nov 2026, EQ499_508_SEPARATE revision.
First exact algebraic and scalar layer. Stable TeX labels identify the
statements independently of editorial equation renumbering. -/

namespace Manuscript15.Sections9To12

noncomputable section

-- §9: prop:ridge-metric. The tangent vectors are written in the
-- rotating orthonormal radial, azimuthal, vertical frame.
theorem ridge_metric_determinant (R Rp Zp r rp q : ℝ) :
    (Zp^2 + Rp^2*r^2 + R^2*r^2*q^2)*(R^2*(r^2+rp^2)) -
      (R*Rp*r*rp + R^2*r^2*q)^2 =
    R^2*(Zp^2*(r^2+rp^2) + r^2*(Rp*r-R*q*rp)^2) := by
  ring

theorem ridge_metric_positive (R Rp Zp r rp q : ℝ)
    (hR : 0 < R) (hZ : 0 < Zp) (hr : 0 < r) :
    0 < R^2*(Zp^2*(r^2+rp^2) + r^2*(Rp*r-R*q*rp)^2) := by
  positivity

theorem ridge_normal_orthogonal_x (R Rp Zp r rp q : ℝ) :
    (Zp*r)*(Rp*r) + (-Zp*rp)*(R*r*q) +
      (-r*(Rp*r-R*q*rp))*Zp = 0 := by
  ring

theorem ridge_normal_orthogonal_theta (R Zp r rp : ℝ) :
    (Zp*r)*(R*rp) + (-Zp*rp)*(R*r) = 0 := by
  ring

theorem ridge_normal_squared (R Rp Zp r rp q : ℝ) :
    (Zp*r)^2 + (-Zp*rp)^2 + (-r*(Rp*r-R*q*rp))^2 =
      Zp^2*(r^2+rp^2) + r^2*(Rp*r-R*q*rp)^2 := by
  ring

-- cor:ridge-crease: vanishing criterion for the displayed scalar
-- curvature formula, not yet the differential-geometric derivation.
theorem neck_curvature_zero_iff (a d k : ℝ) (ha : 0 < a)
    (hd : 0 < d) (hk : 0 ≤ k) :
    d*|1-k^2|/(a*(1+d^2*k^2)) = 0 ↔ k = 1 := by
  have hden : 0 < a*(1+d^2*k^2) := by positivity
  constructor
  · intro h
    have hn : d*|1-k^2| = 0 := (div_eq_zero_iff.mp h).resolve_right (ne_of_gt hden)
    have hz : |1-k^2| = 0 := (mul_eq_zero.mp hn).resolve_left (ne_of_gt hd)
    have hsq : 1-k^2 = 0 := abs_eq_zero.mp hz
    nlinarith
  · intro h
    subst k
    simp

-- eq:ridge-agnesi: actual self-dual orbit differential.
theorem self_dual_agnesi (x : ℝ) :
    (1 / Real.sqrt 2) /
      Real.sqrt ((1+x^2)*(1+x^2-(1/Real.sqrt 2)^2)) =
    1 / Real.sqrt ((1+x^2)*(1+2*x^2)) := by
  have h2 : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hb : (1/Real.sqrt (2:ℝ))^2 = 1/2 := by
    rw [div_pow, one_pow, hs]
  rw [hb]
  have hA : 0 ≤ (1+x^2)*(1+x^2-1/2) := by
    apply mul_nonneg <;> nlinarith [sq_nonneg x]
  have hB : (1+x^2)*(1+2*x^2) = 2*((1+x^2)*(1+x^2-1/2)) := by ring
  rw [hB, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  ring

-- §10: prop:ridge-maxwell. Actual 3 x 3 tensor, inverse and determinant.
def tensor (s u v : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1+s^2*u^2, s^2*u*v, -s^2*u;
     s^2*u*v, 1+s^2*v^2, -s^2*v;
     -s^2*u, -s^2*v, s^2]

def inverseTensor (s u v : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, u; 0, 1, v; u, v, 1/s^2+u^2+v^2]

theorem tensor_det (s u v : ℝ) : (tensor s u v).det = s^2 := by
  simp [tensor, Matrix.det_fin_three]
  <;> ring

theorem tensor_inverse_right (s u v : ℝ) (hs : s ≠ 0) :
    tensor s u v * inverseTensor s u v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tensor, inverseTensor, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;>
    field_simp [hs] <;> ring

theorem tensor_inverse_left (s u v : ℝ) (hs : s ≠ 0) :
    inverseTensor s u v * tensor s u v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tensor, inverseTensor, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;>
    field_simp [hs] <;> ring

theorem tensor_quadratic_form (s u v A B C : ℝ) :
    (1+s^2*u^2)*A^2 + (1+s^2*v^2)*B^2 + s^2*C^2 +
      2*s^2*u*v*A*B - 2*s^2*u*A*C - 2*s^2*v*B*C =
    A^2+B^2+s^2*(u*A+v*B-C)^2 := by ring

theorem tensor_quadratic_positive (s u v A B C : ℝ)
    (hs : s ≠ 0) (hn : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    0 < A^2+B^2+s^2*(u*A+v*B-C)^2 := by
  rcases hn with hA | hB | hC
  · have h : 0 < A^2 := sq_pos_of_ne_zero hA
    positivity
  · have h : 0 < B^2 := sq_pos_of_ne_zero hB
    positivity
  · by_cases hA : A = 0
    · by_cases hB : B = 0
      · subst A
        subst B
        simp only [mul_zero, add_zero, zero_add, zero_sub, neg_sq]
        exact mul_pos (sq_pos_of_ne_zero hs) (sq_pos_of_ne_zero hC)
      · have h : 0 < B^2 := sq_pos_of_ne_zero hB
        positivity
    · have h : 0 < A^2 := sq_pos_of_ne_zero hA
      positivity

theorem throat_characteristic (u v t : ℝ) :
    (t • (1 : Matrix (Fin 3) (Fin 3) ℝ) - tensor 1 u v).det =
      (t-1)*(t^2-(2+u^2+v^2)*t+1) := by
  simp [tensor, Matrix.det_fin_three, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  <;> ring

theorem golden_throat_roots :
    let g := (1+Real.sqrt 5)/2
    g^2 + 1/g^2 = 3 ∧ g^2*(1/g^2) = 1 := by
  dsimp
  have hs : (Real.sqrt (5:ℝ))^2 = 5 := Real.sq_sqrt (by norm_num)
  have hg : 0 < (1+Real.sqrt (5:ℝ))/2 := by positivity
  have hq : ((1+Real.sqrt (5:ℝ))/2)^2 =
      (1+Real.sqrt (5:ℝ))/2+1 := by nlinarith
  constructor
  · field_simp [ne_of_gt hg]
    nlinarith [congrArg (fun y : ℝ => y^2) hq]
  · field_simp [ne_of_gt hg]

-- prop:ridge-node-new: local algebraic normal form, not the
-- inverse-function theorem or its analytic gluing.
theorem node_factorization (h f g : ℝ) :
    (h-f)*(h-g) = (h-(f+g)/2)^2-((f-g)/2)^2 := by ring

-- prop:ridge-area-new: quartic smoothing polynomial and its primitive.
theorem quartic_difference (t : ℝ) :
    (3+6*t^2-t^4)/8-t = (1-t)^3*(t+3)/8 := by ring

theorem quartic_difference_nonnegative (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (3+6*t^2-t^4)/8-t := by
  rw [quartic_difference]
  positivity

theorem quartic_area_primitive :
    (3*(1:ℝ)/8 - (1:ℝ)^2/2 + (1:ℝ)^3/4 - (1:ℝ)^5/40) -
    (3*(0:ℝ)/8 - (0:ℝ)^2/2 + (0:ℝ)^3/4 - (0:ℝ)^5/40) = 1/10 := by
  norm_num

theorem quartic_central_height_squared (d : ℝ) :
    (3*(2/Real.pi^2)*d/8)^2 = 9*d^2/(16*Real.pi^4) := by
  field_simp [Real.pi_ne_zero]
  <;> ring

-- prop:ridge-error-test-new: rigorous conditional a posteriori bound.
theorem selectivity_error_bound
    (C w S S0 Sh Sh0 B e e0 : ℝ) (hw : 0 < w)
    (hr : |S-S0-w*C| ≤ B) (h1 : |Sh-S| ≤ e) (h0 : |Sh0-S0| ≤ e0) :
    |C-(Sh-Sh0)/w| ≤ (B+e+e0)/w := by
  have h := abs_le.mp hr
  have ha := abs_le.mp h1
  have hb := abs_le.mp h0
  rw [← sub_div' (ne_of_gt hw), abs_div, abs_of_pos hw]
  apply (div_le_div_iff_of_pos_right hw).2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

-- §11: prop:grav-hyd-comparison. Consequences of the geometric
-- perimeter estimate; the integral inequality is a separate obligation.
theorem hydraulic_pi_bound : 1+Real.pi^2/64 < (2:ℝ) := by
  have h := mul_pos (sub_pos.mpr Real.pi_lt_four)
    (show 0 < 4+Real.pi by positivity)
  nlinarith

theorem hydraulic_euler_base (D : ℝ) (hD : 0 < D)
    (hbound : D^2 ≤ 1+Real.pi^2/64) :
    1 < Real.sqrt 2/D := by
  have hs : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have ht : D < Real.sqrt 2 := by
    by_contra! hn
    have hm := mul_nonneg (sub_nonneg.mpr hn)
      (show 0 ≤ D+Real.sqrt 2 by positivity)
    nlinarith [hydraulic_pi_bound]
  exact (lt_div_iff₀ hD).2 (by simpa using ht)

theorem hydraulic_deltoid_base : Real.pi/4 < (1:ℝ) := by
  linarith [Real.pi_lt_four]

theorem hydraulic_euler_velocity (D : ℝ) (hD : 0 < D)
    (hbound : D^2 ≤ 1+Real.pi^2/64) :
    1 < (Real.sqrt 2/D) ^ (2/3:ℝ) :=
  Real.one_lt_rpow (hydraulic_euler_base D hD hbound) (by norm_num)

theorem hydraulic_deltoid_velocity : (Real.pi/4) ^ (2/3:ℝ) < 1 := by
  have h := Real.rpow_lt_rpow (show 0 ≤ Real.pi/4 by positivity)
    hydraulic_deltoid_base (show (0:ℝ) < 2/3 by norm_num)
  simpa using h

-- §12: cor:cross-amplitude15, exact pointwise normalized potential
-- identity. Fourth root is expressed as two nonnegative square roots.
theorem quartic_potential_bridge (b bp x : ℝ) (hb : 0 < b)
    (hp : 0 < bp) (hc : bp^2 = 1-b^2) :
    b / Real.sqrt ((1+x^2)*(1+x^2-b^2)) =
    (b/bp)*Real.sqrt (Real.sqrt ((1/(1+x^2))^2 *
      (bp^2/(x^2+bp^2))^2)) := by
  have hX : 0 < 1+x^2 := by positivity
  have hY : 0 < x^2+bp^2 := by positivity
  have hZ : 0 < (1+x^2)*(x^2+bp^2) := mul_pos hX hY
  have hden : 0 < Real.sqrt ((1+x^2)*(x^2+bp^2)) := Real.sqrt_pos.2 hZ
  have hsq : (Real.sqrt ((1+x^2)*(x^2+bp^2)))^2 = (1+x^2)*(x^2+bp^2) :=
    Real.sq_sqrt hZ.le
  have he : 1+x^2-b^2 = x^2+bp^2 := by linarith
  rw [he]
  have hprod : (1/(1+x^2))^2*(bp^2/(x^2+bp^2))^2 =
      ((bp/Real.sqrt ((1+x^2)*(x^2+bp^2)))^2)^2 := by
    rw [div_pow, hsq]
    field_simp [ne_of_gt hX, ne_of_gt hY] <;> ring
  rw [hprod, Real.sqrt_sq (sq_nonneg _),
      Real.sqrt_sq (div_nonneg hp.le hden.le)]
  field_simp [ne_of_gt hp, ne_of_gt hden]

end

end Manuscript15.Sections9To12

#print axioms Manuscript15.Sections9To12.ridge_metric_determinant
#print axioms Manuscript15.Sections9To12.ridge_metric_positive
#print axioms Manuscript15.Sections9To12.ridge_normal_orthogonal_x
#print axioms Manuscript15.Sections9To12.ridge_normal_orthogonal_theta
#print axioms Manuscript15.Sections9To12.ridge_normal_squared
#print axioms Manuscript15.Sections9To12.neck_curvature_zero_iff
#print axioms Manuscript15.Sections9To12.self_dual_agnesi
#print axioms Manuscript15.Sections9To12.tensor_det
#print axioms Manuscript15.Sections9To12.tensor_inverse_right
#print axioms Manuscript15.Sections9To12.tensor_inverse_left
#print axioms Manuscript15.Sections9To12.tensor_quadratic_form
#print axioms Manuscript15.Sections9To12.tensor_quadratic_positive
#print axioms Manuscript15.Sections9To12.throat_characteristic
#print axioms Manuscript15.Sections9To12.golden_throat_roots
#print axioms Manuscript15.Sections9To12.node_factorization
#print axioms Manuscript15.Sections9To12.quartic_difference
#print axioms Manuscript15.Sections9To12.quartic_difference_nonnegative
#print axioms Manuscript15.Sections9To12.quartic_area_primitive
#print axioms Manuscript15.Sections9To12.quartic_central_height_squared
#print axioms Manuscript15.Sections9To12.selectivity_error_bound
#print axioms Manuscript15.Sections9To12.hydraulic_pi_bound
#print axioms Manuscript15.Sections9To12.hydraulic_euler_base
#print axioms Manuscript15.Sections9To12.hydraulic_deltoid_base
#print axioms Manuscript15.Sections9To12.hydraulic_euler_velocity
#print axioms Manuscript15.Sections9To12.hydraulic_deltoid_velocity
#print axioms Manuscript15.Sections9To12.quartic_potential_bridge
