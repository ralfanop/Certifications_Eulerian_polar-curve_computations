import Mathlib

/-! M14 (14.120), Proposition 11.1, equations (263)--(265).
Exact algebraic prerequisites only. The actual analytic Legendre jet,
the uniform remainder, and the locally uniform limit are separate obligations. -/

namespace M14QuarticLegendre

theorem inverse_jet_cubic (s : ℝ) :
    (s + s^3/5) - (s + s^3/5)^3/5 =
      s - 3*s^5/25 - 3*s^7/125 - s^9/625 := by
  ring

theorem rate_jet_derivative (s : ℝ) :
    HasDerivAt (fun x : ℝ => x^2/2 + x^4/20) (s+s^3/5) s := by
  convert (((hasDerivAt_id s).pow 2).div_const 2).add
    (((hasDerivAt_id s).pow 4).div_const 20) using 1 <;> ring

theorem orthogonal_quadratic (u w q : ℝ) (hq : q^2 = 1/2) :
    ((u+w)*q)^2 + ((u-w)*q)^2 = u^2+w^2 := by
  calc
    _ = 2*q^2*(u^2+w^2) := by ring
    _ = _ := by rw [hq]; ring

theorem orthogonal_product (u w q : ℝ) (hq : q^2 = 1/2) :
    ((u+w)*q)*((u-w)*q) = (u^2-w^2)/2 := by
  calc
    _ = q^2*(u^2-w^2) := by ring
    _ = _ := by rw [hq]; ring

theorem orthogonal_quartic (u w q : ℝ) (hq : q^2 = 1/2) :
    ((u+w)*q)^4 + ((u-w)*q)^4 =
      (u^4+6*u^2*w^2+w^4)/2 := by
  have h4 : q^4 = 1/4 := by
    calc
      q^4 = (q^2)^2 := by ring
      _ = 1/4 := by rw [hq]; norm_num
  calc
    _ = 2*q^4*(u^4+6*u^2*w^2+w^4) := by ring
    _ = _ := by rw [h4]; ring

def jet (s : ℝ) : ℝ := s^2/2+s^4/20

theorem coupled_jet (u w q : ℝ) (hq : q^2 = 1/2) :
    jet ((u+w)*q) + jet ((u-w)*q) - ((u+w)*q)*((u-w)*q) =
      w^2+(u^4+6*u^2*w^2+w^4)/40 := by
  calc
    _ = (((u+w)*q)^2+((u-w)*q)^2)/2 +
        (((u+w)*q)^4+((u-w)*q)^4)/20 -
        ((u+w)*q)*((u-w)*q) := by unfold jet; ring
    _ = _ := by
      rw [orthogonal_quadratic u w q hq, orthogonal_quartic u w q hq,
        orthogonal_product u w q hq]
      ring

theorem coupling_exact (e l : ℝ) (hd : 1+12*l*e^2 ≠ 0) :
    1-1/(1+12*l*e^2) = 12*l*e^2/(1+12*l*e^2) := by
  field_simp [hd] <;> ring

theorem coupling_remainder (e l : ℝ) (hd : 1+12*l*e^2 ≠ 0) :
    1-1/(1+12*l*e^2)-12*l*e^2 =
      -(144*l^2*e^4)/(1+12*l*e^2) := by
  field_simp [hd] <;> ring

/-- Exact error identity for the scaled quartic jet; valid without a limit. -/
theorem scaled_jet_error (e v z l : ℝ) (hd : 1+12*l*e^2 ≠ 0) :
    z^2+(v^4+6*e^2*v^2*z^2+e^4*z^4)/40
      +6*l*(v^2-e^2*z^2)/(1+12*l*e^2)
      -(z^2+v^4/40+6*l*v^2) =
    (6*e^2*v^2*z^2+e^4*z^4)/40
      -6*l*e^2*(z^2+12*l*v^2)/(1+12*l*e^2) := by
  field_simp [hd] <;> ring

/-- Avoids division by the scale, so it is also valid at zero. -/
theorem scaled_jet_factor (e v z l : ℝ) (hd : 1+12*l*e^2 ≠ 0) :
    (e^2*z)^2 + ((e*v)^4+6*(e*v)^2*(e^2*z)^2+(e^2*z)^4)/40
      +(1-1/(1+12*l*e^2))*((e*v)^2-(e^2*z)^2)/2 =
    e^4*(z^2+(v^4+6*e^2*v^2*z^2+e^4*z^4)/40
      +6*l*(v^2-e^2*z^2)/(1+12*l*e^2)) := by
  rw [coupling_exact e l hd]
  field_simp [hd] <;> ring

end M14QuarticLegendre

#print axioms M14QuarticLegendre.inverse_jet_cubic
#print axioms M14QuarticLegendre.rate_jet_derivative
#print axioms M14QuarticLegendre.orthogonal_quadratic
#print axioms M14QuarticLegendre.orthogonal_product
#print axioms M14QuarticLegendre.orthogonal_quartic
#print axioms M14QuarticLegendre.coupled_jet
#print axioms M14QuarticLegendre.coupling_exact
#print axioms M14QuarticLegendre.coupling_remainder
#print axioms M14QuarticLegendre.scaled_jet_error
#print axioms M14QuarticLegendre.scaled_jet_factor
