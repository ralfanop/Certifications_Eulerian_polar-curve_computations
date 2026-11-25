import Mathlib
import Manuscript13.EllisFourier20261124
import EulerianGrothendieck.CriticalWindowGammaVacuum

/-! M13, revision 2026-11-25, prop:cross-throat13.
Source ZIP SHA256 283b38ea4d3ed2380ff7018ba9cdd6d1c5625246d8eb9713970cbd6ad810b8e8.
Source 13/13.tex SHA256 4febb370e6329cae2c94e88f4171e652bdeed6616b976fa728f83259e7b275f9.
The actual normalized potential is imported unchanged from #558.
The quarter-power weight is related to nested square roots, its scale
is removed by a genuine Lebesgue substitution, and the tangent
substitution is targeted as a genuine integral equality.  The M12
quartic normalization and self-dual elliptic evaluation are explicit
inputs until linked to their respective independent formalizations.
-/
open MeasureTheory Set
open scoped ENNReal
namespace Manuscript13.CrossThroatElliptic20261125
noncomputable section
open Manuscript13.EllisFourier20261124 (potential)

def complementary (b : ℝ) := Real.sqrt (1-b^2)
def factor (a u : ℝ) := a^2/(u^2+a^2)
def normalized (a u : ℝ) := potential a u / potential a 0
def weight (a c u : ℝ) := (normalized a u * normalized (a*c) u) ^ (1/4 : ℝ)
def scaledWeight (c x : ℝ) := Real.sqrt (factor 1 x * factor c x)

theorem complementary_pos (b : ℝ) (hb : 0 ≤ b) (hb1 : b < 1) :
    0 < complementary b := by
  unfold complementary
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg b]

theorem complementary_sq (b : ℝ) (hb : 0 ≤ b) (hb1 : b < 1) :
    complementary b ^ 2 = 1-b^2 := by
  unfold complementary
  exact Real.sq_sqrt (by nlinarith [sq_nonneg b])

theorem potential_origin (a : ℝ) (ha : 0 < a) :
    potential a 0 = 1/a^2 := by
  unfold potential
  simp only [zero_pow (by decide : (2:ℕ) ≠ 0), zero_add]
  field_simp [ne_of_gt ha]

theorem factor_nonneg (a u : ℝ) : 0 ≤ factor a u := by
  unfold factor
  positivity

theorem normalized_eq_sq (a u : ℝ) (ha : 0 < a) :
    normalized a u = factor a u ^ 2 := by
  unfold normalized factor
  rw [potential_origin a ha]
  unfold potential
  have hd : u^2+a^2 ≠ 0 := by positivity
  field_simp [ne_of_gt ha, hd] <;> ring

theorem quarter_square (x : ℝ) (hx : 0 ≤ x) :
    (x^2) ^ (1/4:ℝ) = Real.sqrt x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, Real.sqrt_eq_rpow]
  norm_num

theorem weight_eq_sqrt (a c u : ℝ) (ha : 0 < a) (hc : 0 < c) :
    weight a c u = Real.sqrt (factor a u * factor (a*c) u) := by
  unfold weight
  rw [normalized_eq_sq a u ha, normalized_eq_sq (a*c) u (mul_pos ha hc), ← mul_pow]
  exact quarter_square _ (mul_nonneg (factor_nonneg _ _) (factor_nonneg _ _))

theorem factor_scale (a c x : ℝ) (ha : 0 < a) (hc : 0 < c) :
    factor (a*c) (a*x) = factor c x := by
  unfold factor
  have h : x^2+c^2 ≠ 0 := by positivity
  have h' : (a*x)^2+(a*c)^2 ≠ 0 := by positivity
  field_simp [ne_of_gt ha,h,h'] <;> ring

theorem weight_scale (a c x : ℝ) (ha : 0 < a) (hc : 0 < c) :
    weight a c (a*x) = scaledWeight c x := by
  rw [weight_eq_sqrt a c (a*x) ha hc, factor_scale a c x ha hc]
  have h := factor_scale a 1 x ha (by norm_num)
  rw [mul_one] at h
  rw [h]
  rfl

theorem overlap_scale (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    (1/a)*(∫ u in Ioi (0:ℝ), weight a c u) =
      ∫ x in Ioi (0:ℝ), scaledWeight c x := by
  have h := integral_comp_mul_left_Ioi (weight a c) 0 ha
  simp only [mul_zero, smul_eq_mul] at h
  have he : (∫ x in Ioi (0:ℝ), weight a c (a*x)) =
      ∫ x in Ioi (0:ℝ), scaledWeight c x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    exact weight_scale a c x ha hc
  rw [← he, h]
  ring

theorem scaledWeight_formula (c x : ℝ) (hc : 0 < c) :
    scaledWeight c x = c / Real.sqrt ((1+x^2)*(c^2+x^2)) := by
  have h1 : 0 < 1+x^2 := by positivity
  have h2 : 0 < c^2+x^2 := by positivity
  unfold scaledWeight factor
  have hden : (1+x^2)*(c^2+x^2) ≠ 0 := ne_of_gt (mul_pos h1 h2)
  have he : (1:ℝ)^2/(x^2+1^2)*(c^2/(x^2+c^2)) = c^2/((1+x^2)*(c^2+x^2)) := by
    field_simp [ne_of_gt h1,ne_of_gt h2,hden,show x^2+1^2 ≠ 0 by positivity,
      show x^2+c^2 ≠ 0 by positivity] <;> ring
  rw [he, Real.sqrt_div (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_pos hc]

def ellipticIntegrand (b θ : ℝ) := 1/Real.sqrt (1-b^2*Real.sin θ^2)
def ellipticK (b : ℝ) := ∫ θ in (0:ℝ)..(Real.pi/2), ellipticIntegrand b θ

theorem tangent_jacobian (b θ : ℝ) (hb : 0 ≤ b) (hb1 : b < 1)
    (hθ : θ ∈ Ioo (0:ℝ) (Real.pi/2)) :
    HasDerivWithinAt (fun t => complementary b * Real.tan t)
      (complementary b / Real.cos θ^2) (Ioo (0:ℝ) (Real.pi/2)) θ := by
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hθ.1], hθ.2⟩
  have h := (Real.hasDerivAt_tan (ne_of_gt hcos)).const_mul (complementary b)
  convert h.hasDerivWithinAt using 1
  ring

theorem tangent_weight (b θ : ℝ) (hb : 0 ≤ b) (hb1 : b < 1)
    (hθ : θ ∈ Ioo (0:ℝ) (Real.pi/2)) :
    (complementary b / Real.cos θ^2) *
      scaledWeight (complementary b) (complementary b * Real.tan θ) =
      complementary b * ellipticIntegrand b θ := by
  let c := complementary b
  have hc : 0 < c := complementary_pos b hb hb1
  have hc2 : c^2 = 1-b^2 := complementary_sq b hb hb1
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hθ.1], hθ.2⟩
  have htrig := Real.sin_sq_add_cos_sq θ
  have hsin : Real.sin θ^2 ≤ 1 := by nlinarith [sq_nonneg (Real.cos θ)]
  have hb2 : b^2 < 1 := by nlinarith [sq_nonneg b]
  have harg : 0 < 1-b^2*Real.sin θ^2 := by
    have h := mul_le_mul_of_nonneg_left hsin (sq_nonneg b)
    linarith
  have hA : 1+(c*Real.tan θ)^2 =
      (1-b^2*Real.sin θ^2)/Real.cos θ^2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hcos]
    nlinarith [hc2, htrig, congrArg (fun x : ℝ => x*Real.sin θ^2) hc2]
  have hB : c^2+(c*Real.tan θ)^2 = c^2/Real.cos θ^2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [ne_of_gt hcos]
    nlinarith [congrArg (fun x : ℝ => c^2*x) htrig]
  have hroot : Real.sqrt ((1+(c*Real.tan θ)^2)*(c^2+(c*Real.tan θ)^2)) =
      c*Real.sqrt (1-b^2*Real.sin θ^2)/Real.cos θ^2 := by
    rw [hA,hB]
    have he : (1-b^2*Real.sin θ^2)/Real.cos θ^2*(c^2/Real.cos θ^2) =
      (1-b^2*Real.sin θ^2)*(c^2)/(Real.cos θ^2)^2 := by ring
    rw [he, Real.sqrt_div (mul_nonneg harg.le (sq_nonneg c)),
      Real.sqrt_mul harg.le, Real.sqrt_sq_eq_abs, abs_of_pos hc,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]
    ring
  change c/Real.cos θ^2 * scaledWeight c (c*Real.tan θ) =
    c*ellipticIntegrand b θ
  rw [scaledWeight_formula c _ hc,hroot]
  unfold ellipticIntegrand
  field_simp [ne_of_gt hc,ne_of_gt hcos,ne_of_gt (Real.sqrt_pos.2 harg)]

/-- The M12 period identity is an explicit classical input here; this
is not an independent proof of the binary-quartic normalization. -/
theorem quartic_bridge (b T Z : ℝ) (hT : T = complementary b * ellipticK b)
    (hK : ellipticK b = Real.sqrt (2*Real.pi/5)*Z) :
    T = Real.sqrt (2*Real.pi/5)*complementary b*Z := by rw [hT,hK]; ring

def criticalF0 := (1/(2*Real.sqrt Real.pi)) * (∫ x : ℝ, M12CriticalGamma.quarticProfile x)

theorem criticalF0_gamma :
    criticalF0 = (40:ℝ)^(1/4:ℝ)*Real.Gamma (1/4)/(4*Real.sqrt Real.pi) :=
  M12CriticalGamma.critical_constant

theorem self_dual_complement :
    complementary (1/Real.sqrt 2) = 1/Real.sqrt 2 := by
  unfold complementary
  have h : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := by positivity
  have he : 1-(1/Real.sqrt 2)^2 = (1/Real.sqrt 2)^2 := by
    field_simp [ne_of_gt hp]
    nlinarith
  rw [he, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

/-- Conditional on the exact M12 self-dual quartic normalization.
Uses the actual imported quartic critical constant, not a new
uninterpreted symbol for Fcrit(0). -/
theorem self_dual_bridge (T : ℝ)
    (hT : T = complementary (1/Real.sqrt 2)*ellipticK (1/Real.sqrt 2))
    (hK : ellipticK (1/Real.sqrt 2) = Real.sqrt (2*Real.pi/5)*criticalF0^2) :
    T = Real.sqrt (Real.pi/5)*criticalF0^2 := by
  rw [hT,hK,self_dual_complement]
  have h2 : Real.sqrt (2*Real.pi/5) = Real.sqrt 2 * Real.sqrt (Real.pi/5) := by
    rw [show 2*Real.pi/5 = 2*(Real.pi/5) by ring, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [h2]
  field_simp [show Real.sqrt (2:ℝ) ≠ 0 by positivity]

end
end Manuscript13.CrossThroatElliptic20261125
#print axioms Manuscript13.CrossThroatElliptic20261125.complementary_pos
#print axioms Manuscript13.CrossThroatElliptic20261125.complementary_sq
#print axioms Manuscript13.CrossThroatElliptic20261125.potential_origin
#print axioms Manuscript13.CrossThroatElliptic20261125.factor_nonneg
#print axioms Manuscript13.CrossThroatElliptic20261125.normalized_eq_sq
#print axioms Manuscript13.CrossThroatElliptic20261125.quarter_square
#print axioms Manuscript13.CrossThroatElliptic20261125.weight_eq_sqrt
#print axioms Manuscript13.CrossThroatElliptic20261125.factor_scale
#print axioms Manuscript13.CrossThroatElliptic20261125.weight_scale
#print axioms Manuscript13.CrossThroatElliptic20261125.overlap_scale
#print axioms Manuscript13.CrossThroatElliptic20261125.scaledWeight_formula
#print axioms Manuscript13.CrossThroatElliptic20261125.tangent_jacobian
#print axioms Manuscript13.CrossThroatElliptic20261125.tangent_weight
#print axioms Manuscript13.CrossThroatElliptic20261125.quartic_bridge
#print axioms Manuscript13.CrossThroatElliptic20261125.criticalF0_gamma
#print axioms Manuscript13.CrossThroatElliptic20261125.self_dual_complement
#print axioms Manuscript13.CrossThroatElliptic20261125.self_dual_bridge
