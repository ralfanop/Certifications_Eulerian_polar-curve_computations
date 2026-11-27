import Manuscript13.CrossThroatLemniscate20261126
import Manuscript15.CrossQuarticImproperPeriod20261125

/-! M12 Prop. 9.20, (384), (387): actual complete elliptic integral.
Reuse the exact-head certified tangent substitution and lemniscatic Beta
integral of M13 and the improper period of M15. No assumption of the
general binary-quartic normalization (385). -/
noncomputable section
namespace M12SelfDualElliptic
open MeasureTheory Set
open Manuscript13.CrossThroatElliptic20261125
open Manuscript13.CrossThroatLemniscate20261126
open Manuscript15.CrossQuarticImproperPeriod20261125

def quarticDensity (t : ℝ) : ℝ := 1/Real.sqrt (1+t^4)

theorem quarticDensity_integrable : Integrable quarticDensity := by
  have hc : Continuous quarticDensity := by
    unfold quarticDensity
    exact continuous_const.div (by fun_prop) (fun t => ne_of_gt (Real.sqrt_pos.2 (by positivity)))
  apply (integrable_inv_one_add_sq.const_mul (Real.sqrt 2)).mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  have hp : 0 < Real.sqrt (1+t^4) := Real.sqrt_pos.2 (by positivity)
  have hq : 0 < 1+t^2 := by positivity
  have hsq : (Real.sqrt 2*Real.sqrt (1+t^4))^2 = 2*(1+t^4) := by
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sq_sqrt (by positivity)]
  have hle : 1+t^2 ≤ Real.sqrt 2*Real.sqrt (1+t^4) := by
    nlinarith [sq_nonneg (t^2-1),Real.sqrt_nonneg (2:ℝ),Real.sqrt_nonneg (1+t^4)]
  change ‖quarticDensity t‖ ≤ Real.sqrt 2*(1+t^2)⁻¹
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold quarticDensity; positivity),quarticDensity,← div_eq_mul_inv]
  exact (div_le_div_iff₀ hp hq).2 (by simpa using hle)

theorem reciprocal_image :
    (fun t : ℝ => t⁻¹) '' Ioo (0:ℝ) 1 = Ioi 1 := by
  ext y
  constructor
  · rintro ⟨t,ht,rfl⟩
    change 1 < t⁻¹
    rw [← one_div]
    exact (lt_div_iff₀ ht.1).2 (by simpa using ht.2)
  · intro hy
    have hy0 : 0 < y := lt_trans (by norm_num) hy
    refine ⟨y⁻¹,⟨inv_pos.mpr hy0,?_⟩,inv_inv _⟩
    rw [← one_div]
    exact (div_lt_iff₀ hy0).2 (by simpa using hy)

theorem reciprocal_weight (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    |-(t^2)⁻¹| • quarticDensity t⁻¹ = quarticDensity t := by
  have hp : 0 < t := ht.1
  have hs : 0 < Real.sqrt (1+t^4) := Real.sqrt_pos.2 (by positivity)
  have he : 1+(t⁻¹)^4 = (1+t^4)/(t^2)^2 := by
    field_simp [ne_of_gt hp] <;> ring
  have hr : Real.sqrt (1+(t⁻¹)^4) = Real.sqrt (1+t^4)/t^2 := by
    rw [he,Real.sqrt_div (by positivity),Real.sqrt_sq_eq_abs,abs_of_nonneg (sq_nonneg t)]
  rw [abs_neg,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t)),smul_eq_mul]
  unfold quarticDensity
  rw [hr]
  field_simp [ne_of_gt hp,ne_of_gt hs]

theorem reciprocal_period :
    (∫ t in Ioi (1:ℝ),quarticDensity t) =
      ∫ t in Ioo (0:ℝ) 1,quarticDensity t := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun t ht => hasDerivWithinAt_inv (ne_of_gt ht.1) (Ioo (0:ℝ) 1))
    (fun x hx y hy hxy => inv_injective hxy) quarticDensity
  rw [reciprocal_image] at h
  rw [h]
  exact setIntegral_congr_fun measurableSet_Ioo reciprocal_weight

theorem quartic_half_period :
    (∫ t in Ioi (0:ℝ),quarticDensity t) =
      2*(∫ t in (0:ℝ)..1,quarticDensity t) := by
  have hu : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext t
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (h|h)
      · exact h.1
      · linarith
    · intro ht
      by_cases h : t ≤ 1
      · exact Or.inl ⟨ht,h⟩
      · exact Or.inr (lt_of_not_ge h)
  have hd : Disjoint (Ioc (0:ℝ) 1) (Ioi 1) :=
    Set.disjoint_left.2 (fun t ht ht' => not_lt_of_ge ht.2 ht')
  rw [← hu,setIntegral_union hd measurableSet_Ioi quarticDensity_integrable.integrableOn
    quarticDensity_integrable.integrableOn,reciprocal_period,← integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  ring

theorem selfdual_weight (x : ℝ) :
    scaledWeight c x = 1/Real.sqrt ((1+x^2)*(1+2*x^2)) := by
  have hc : 0 < c := by unfold c; positivity
  have hs : 0 < Real.sqrt (2:ℝ) := by positivity
  have hp : 0 < Real.sqrt ((1+x^2)*(1+2*x^2)) := Real.sqrt_pos.2 (by positivity)
  rw [scaledWeight_formula c x hc,selfdual_sq]
  rw [show (1+x^2)*(1/2+x^2) = ((1+x^2)*(1+2*x^2))/2 by ring,
    Real.sqrt_div (by positivity)]
  unfold c
  field_simp [ne_of_gt hs,ne_of_gt hp]

theorem selfdual_K_from_weight :
    (∫ x in Ioi (0:ℝ),scaledWeight c x) = c*ellipticK c := by
  have hc : 0 < c := by unfold c; positivity
  have hc1 : c < 1 := by
    have hs : 1 < Real.sqrt (2:ℝ) := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
    unfold c
    exact (div_lt_one (by positivity)).2 hs
  have he : complementary c = c := self_dual_complement
  simpa only [he] using scaled_integral_elliptic c hc.le hc1

theorem equation_387 :
    ellipticK (1/Real.sqrt 2) = ∫ t in Ioi (0:ℝ),1/Real.sqrt (1+t^4) := by
  change ellipticK c = ∫ t in Ioi (0:ℝ),quarticDensity t
  have h := selfdual_K_from_weight
  simp_rw [selfdual_weight] at h
  rw [cross_curve_period15_literal] at h
  have hc : Real.sqrt 2*c=1 := by unfold c; field_simp [show Real.sqrt (2:ℝ)≠0 by positivity]
  calc
    ellipticK c = Real.sqrt 2*(c*ellipticK c) := by rw [← mul_assoc,hc,one_mul]
    _ = Real.sqrt 2*(Real.sqrt 2*(∫ t in (0:ℝ)..1,quarticDensity t)) := by rw [← h]; rfl
    _ = 2*(∫ t in (0:ℝ)..1,quarticDensity t) := by
      rw [← mul_assoc,← pow_two,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    _ = _ := quartic_half_period.symm

theorem selfdual_K_gamma :
    ellipticK (1/Real.sqrt 2) = Real.sqrt (2*Real.pi/5)*criticalF0^2 := by
  change ellipticK c = _
  have h : lemPeriod = c*ellipticK c := lem_period.symm.trans selfdual_K_from_weight
  have hc : Real.sqrt 2*c=1 := by unfold c; field_simp [show Real.sqrt (2:ℝ)≠0 by positivity]
  have hs : Real.sqrt (2*Real.pi/5) = Real.sqrt 2*Real.sqrt (Real.pi/5) := by
    rw [show 2*Real.pi/5 = 2*(Real.pi/5) by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  calc
    ellipticK c = Real.sqrt 2*(c*ellipticK c) := by rw [← mul_assoc,hc,one_mul]
    _ = Real.sqrt 2*lemPeriod := by rw [h]
    _ = _ := by rw [lem_gamma_of_beta,← critical_gamma_exact,hs]; ring

end M12SelfDualElliptic
#print axioms M12SelfDualElliptic.quarticDensity_integrable
#print axioms M12SelfDualElliptic.reciprocal_image
#print axioms M12SelfDualElliptic.reciprocal_weight
#print axioms M12SelfDualElliptic.reciprocal_period
#print axioms M12SelfDualElliptic.quartic_half_period
#print axioms M12SelfDualElliptic.selfdual_weight
#print axioms M12SelfDualElliptic.selfdual_K_from_weight
#print axioms M12SelfDualElliptic.equation_387
#print axioms M12SelfDualElliptic.selfdual_K_gamma
