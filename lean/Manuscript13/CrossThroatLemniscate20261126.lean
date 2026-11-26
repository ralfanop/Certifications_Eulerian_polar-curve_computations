import Mathlib
import Manuscript13.CrossThroatElliptic20261125

/-! M13 Prop. 4.13, revised equations (78)–(81).
Actual improper change of variables x=t/sqrt(1-t²) and s=t⁴.
The first reduction to the lemniscatic integral is independent of any
Gauss/AGM evaluation. The final Gamma and critical-quartic identities
use the actual Euler Beta integral. The AGM analytic identity and the
general M12 binary-quartic normalization remain separate obligations.
-/
open MeasureTheory Set
namespace Manuscript13.CrossThroatLemniscate20261126
noncomputable section
open Manuscript13.CrossThroatElliptic20261125

def c : ℝ := 1/Real.sqrt 2
def lemMap (t : ℝ) := t/Real.sqrt (1-t^2)
def lemProfile (t : ℝ) := 1/Real.sqrt (1-t^4)
def lemPeriod : ℝ := ∫ t in Ioo (0:ℝ) 1, lemProfile t

theorem selfdual_sq : c^2 = 1/2 := by
  unfold c
  rw [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

theorem lem_map_sq (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    lemMap t ^ 2 = t^2/(1-t^2) := by
  have hq : 0 < 1-t^2 := by nlinarith [ht.1,ht.2]
  unfold lemMap
  rw [div_pow,Real.sq_sqrt hq.le]

theorem lem_map_pos (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : 0 < lemMap t := by
  unfold lemMap
  exact div_pos ht.1 (Real.sqrt_pos.2 (by nlinarith [ht.1,ht.2]))

theorem lem_map_jacobian (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivWithinAt lemMap (1/(Real.sqrt (1-t^2))^3) (Ioo (0:ℝ) 1) t := by
  have hq : 0 < 1-t^2 := by nlinarith [ht.1,ht.2]
  have hs : 0 < Real.sqrt (1-t^2) := Real.sqrt_pos.2 hq
  have hs2 := Real.sq_sqrt hq.le
  have hd : HasDerivAt (fun x : ℝ => 1-x^2) (-2*t) t := by
    convert ((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)) using 1 <;> ring
  have h := (hasDerivAt_id t).div (hd.sqrt (ne_of_gt hq)) (ne_of_gt hs)
  unfold lemMap
  convert h.hasDerivWithinAt using 1
  field_simp [ne_of_gt hs]
  nlinarith [hs2]

theorem lem_map_inj : InjOn lemMap (Ioo (0:ℝ) 1) := by
  intro t ht s hs h
  have htq : 0 < 1-t^2 := by nlinarith [ht.1,ht.2]
  have hsq : 0 < 1-s^2 := by nlinarith [hs.1,hs.2]
  have he := congrArg (fun x : ℝ => x^2) h
  rw [lem_map_sq t ht,lem_map_sq s hs] at he
  field_simp [ne_of_gt htq,ne_of_gt hsq] at he
  have he2 : t^2 = s^2 := by nlinarith only [he]
  nlinarith [ht.1,hs.1]

theorem lem_map_image : lemMap '' Ioo (0:ℝ) 1 = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact lem_map_pos t ht
  · intro hx
    let r := Real.sqrt (1+x^2)
    have hr : 0 < r := by dsimp [r]; positivity
    have hr2 : r^2 = 1+x^2 := Real.sq_sqrt (by positivity)
    have hxr : x < r := by nlinarith [show 0 < x from hx,hr2]
    let t := x/r
    have ht : t ∈ Ioo (0:ℝ) 1 :=
      ⟨div_pos hx hr,(div_lt_one hr).2 hxr⟩
    refine ⟨t,ht,?_⟩
    have htq : 0 < 1-t^2 := by nlinarith [ht.1,ht.2]
    have htsq : t^2 = x^2/(1+x^2) := by dsimp [t]; rw [div_pow,hr2]
    have he : lemMap t ^ 2 = x^2 := by
      rw [lem_map_sq t ht,htsq]
      have hp : (1:ℝ)+x^2 ≠ 0 := by positivity
      have hq : 1-x^2/(1+x^2) ≠ 0 := by
        rw [← htsq]; exact ne_of_gt htq
      field_simp [hp,hq] <;> ring
    nlinarith [lem_map_pos t ht,show 0 < x from hx]

theorem lem_weight (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    (1/(Real.sqrt (1-t^2))^3) * scaledWeight c (lemMap t) = lemProfile t := by
  have hq : 0 < 1-t^2 := by nlinarith [ht.1,ht.2]
  have hs : 0 < Real.sqrt (1-t^2) := Real.sqrt_pos.2 hq
  have ht4 : 0 < 1-t^4 := by
    have hh := mul_pos hq (show 0 < 1+t^2 by positivity)
    nlinarith only [hh]
  have hc : 0 < c := by unfold c; positivity
  have hD : (1+lemMap t^2)*(c^2+lemMap t^2) = (1-t^4)/(2*(1-t^2)^2) := by
    rw [lem_map_sq t ht,selfdual_sq]
    field_simp [ne_of_gt hq] <;> ring
  have hDpos : 0 < (1+lemMap t^2)*(c^2+lemMap t^2) := by positivity
  have hs6 : (Real.sqrt (1-t^2)^3)^2 = (1-t^2)^3 := by
    rw [← pow_mul,show (3:ℕ)*2 = 2*3 by decide,pow_mul,Real.sq_sqrt hq.le]
  rw [scaledWeight_formula c _ hc]
  unfold lemProfile
  have hL : 0 ≤ (1/(Real.sqrt (1-t^2))^3) * (c/Real.sqrt ((1+lemMap t^2)*(c^2+lemMap t^2))) := by positivity
  have hR : 0 ≤ 1/Real.sqrt (1-t^4) := by positivity
  have he : ((1/(Real.sqrt (1-t^2))^3) * (c/Real.sqrt ((1+lemMap t^2)*(c^2+lemMap t^2))))^2 =
      (1/Real.sqrt (1-t^4))^2 := by
    rw [mul_pow,div_pow,div_pow,div_pow,hs6,Real.sq_sqrt hDpos.le,selfdual_sq,hD,Real.sq_sqrt ht4.le]
    field_simp [ne_of_gt hq,ne_of_gt ht4] <;> ring
  nlinarith only [he,hL,hR]

theorem lem_period :
    (∫ x in Ioi (0:ℝ), scaledWeight c x) = lemPeriod := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    lem_map_jacobian lem_map_inj (scaledWeight c)
  rw [lem_map_image] at h
  rw [h]
  unfold lemPeriod
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  rw [abs_of_nonneg (by positivity : 0 ≤ 1/(Real.sqrt (1-t^2))^3),smul_eq_mul]
  exact lem_weight t ht

theorem actual_throat_lemniscate (a : ℝ) (ha : 0 < a) :
    (1/a)*(∫ u in Ioi (0:ℝ), weight a (complementary c) u) = lemPeriod := by
  have hc : 0 < c := by unfold c; positivity
  have he : complementary c = c := self_dual_complement
  rw [he,overlap_scale a c ha hc,lem_period]

theorem critical_gamma_exact :
    Real.sqrt (Real.pi/5)*criticalF0^2 = Real.Gamma (1/4)^2/(4*Real.sqrt (2*Real.pi)) := by
  rw [criticalF0_gamma]
  have h40 : ((40:ℝ)^(1/4:ℝ))^2 = Real.sqrt 40 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.sqrt_eq_rpow]
    norm_num
  have hs : Real.sqrt (Real.pi/5)*Real.sqrt 40 = 2*Real.sqrt (2*Real.pi) := by
    rw [← Real.sqrt_mul (by positivity),show Real.pi/5*40=2^2*(2*Real.pi) by ring,
      Real.sqrt_mul (by positivity),Real.sqrt_sq (by norm_num)]
  have hsq : Real.sqrt (2*Real.pi)^2 = 2*Real.pi := Real.sq_sqrt (by positivity)
  have hpi : Real.sqrt Real.pi^2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  rw [div_pow,mul_pow,h40,mul_pow,hpi]
  field_simp
  rw [show (4:ℝ)*Real.sqrt (Real.pi/5)*Real.sqrt 40*Real.sqrt (2*Real.pi) =
    4*(Real.sqrt (Real.pi/5)*Real.sqrt 40)*Real.sqrt (2*Real.pi) by ring,hs]
  nlinarith only [hsq]

def betaProfile (s : ℝ) := s^(-3/4:ℝ)*(1-s)^(-1/2:ℝ)

theorem beta_map_inj : InjOn (fun t : ℝ => t^4) (Ioo (0:ℝ) 1) := by
  intro t ht s hs h
  have ht0 : 0 < t := ht.1
  have hs0 : 0 < s := hs.1
  have he : t^2 = s^2 := by
    have h' : (t^2)^2 = (s^2)^2 := by simpa only [← pow_mul,show (2:ℕ)*2=4 by decide] using h
    nlinarith [sq_nonneg t,sq_nonneg s]
  nlinarith

theorem beta_map_image : (fun t : ℝ => t^4) '' Ioo (0:ℝ) 1 = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact ⟨by positivity [ht.1],pow_lt_one₀ ht.1.le ht.2 (by decide)⟩
  · intro hx
    let t := Real.sqrt (Real.sqrt x)
    have ht0 : 0 < t := by dsimp [t]; positivity [hx.1]
    have h2 : t^2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg x)
    have h4 : t^4 = x := by rw [show (4:ℕ)=2*2 by decide,pow_mul,h2,Real.sq_sqrt hx.1.le]
    have ht1 : t < 1 := by
      by_contra! hn
      have hh : 1 ≤ t^4 := one_le_pow₀ hn
      linarith [hx.2]
    exact ⟨t,⟨ht0,ht1⟩,h4⟩

theorem beta_map_jacobian (t : ℝ) (_ : t ∈ Ioo (0:ℝ) 1) :
    HasDerivWithinAt (fun s : ℝ => s^4) (4*t^3) (Ioo (0:ℝ) 1) t := by
  convert ((hasDerivAt_id t).pow 4).hasDerivWithinAt using 1 <;> ring

theorem beta_weight (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    (4*t^3)*betaProfile (t^4) = 4*lemProfile t := by
  have ht0 : 0 < t := ht.1
  have hq : 0 < 1-t^4 := by have h := pow_lt_one₀ ht0.le ht.2 (by decide : (4:ℕ) ≠ 0); linarith
  unfold betaProfile lemProfile
  have h1 : (t^4)^(-3/4:ℝ) = (t^3)⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul ht0.le]
    norm_num [Real.rpow_neg ht0.le,Real.rpow_natCast]
  have h2 : (1-t^4)^(-1/2:ℝ) = (Real.sqrt (1-t^4))⁻¹ := by
    rw [show (-1/2:ℝ)=-(1/2) by norm_num,Real.rpow_neg hq.le,← Real.sqrt_eq_rpow]
  rw [h1,h2]
  field_simp [ne_of_gt ht0,ne_of_gt (Real.sqrt_pos.2 hq)]

theorem lem_beta_integral :
    (∫ s in Ioo (0:ℝ) 1,betaProfile s) = 4*lemPeriod := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    beta_map_jacobian beta_map_inj betaProfile
  rw [beta_map_image] at h
  rw [h]
  unfold lemPeriod
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  rw [abs_of_nonneg (by positivity [ht.1] : 0 ≤ 4*t^3),smul_eq_mul]
  exact beta_weight t ht

/-- Convert the actual complex Beta integral to a real integral using
the nonnegative bases on the open unit interval. -/
theorem gamma_beta_ratio :
    (∫ s in Ioo (0:ℝ) 1,betaProfile s) =
      Real.Gamma (1/4)*Real.Gamma (1/2)/Real.Gamma (3/4) := by
  have h := Complex.betaIntegral_eq_Gamma_mul_div (1/4:ℂ) (1/2:ℂ) (by norm_num) (by norm_num)
  unfold Complex.betaIntegral at h
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),integral_Ioc_eq_integral_Ioo] at h
  have he : (∫ s in Ioo (0:ℝ) 1, (betaProfile s : ℂ)) =
      ∫ s in Ioo (0:ℝ) 1, (s:ℂ)^((1/4:ℂ)-1)*(1-(s:ℂ))^((1/2:ℂ)-1) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    unfold betaProfile
    rw [Complex.ofReal_mul,Complex.ofReal_cpow hs.1.le,
      Complex.ofReal_cpow (sub_nonneg.mpr hs.2.le)]
    push_cast
    congr 1 <;> ring_nf
  rw [← he] at h
  have hcast : (∫ s in Ioo (0:ℝ) 1,(betaProfile s : ℂ)) =
      ((∫ s in Ioo (0:ℝ) 1,betaProfile s):ℂ) := by
    first | exact Complex.ofReal_integral.symm | exact?
  rw [hcast] at h
  rw [← Complex.ofReal_inj]
  push_cast
  simpa only [Complex.Gamma_ofReal,Complex.ofReal_div,Complex.ofReal_mul,
    show (1/4:ℂ)+(1/2:ℂ)=3/4 by ring] using h

theorem lem_gamma_of_beta :
    lemPeriod = Real.Gamma (1/4)^2/(4*Real.sqrt (2*Real.pi)) := by
  have h := gamma_beta_ratio
  rw [lem_beta_integral] at h
  have hg := Real.Gamma_mul_Gamma_add_half (1/4:ℝ)
  norm_num at hg
  rw [show (2:ℝ)^(1/2:ℝ)=Real.sqrt 2 by rw [Real.sqrt_eq_rpow]] at hg
  have hhalf : Real.Gamma (1/2) = Real.sqrt Real.pi := by exact?
  rw [hhalf] at h hg
  have hq : 0 < Real.Gamma (3/4) := Real.Gamma_pos_of_pos (by norm_num)
  have hp : 0 < Real.sqrt Real.pi := by positivity
  have h2 : 0 < Real.sqrt 2 := by positivity
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  field_simp [ne_of_gt hq,ne_of_gt hp,ne_of_gt h2] at h ⊢
  nlinarith [congrArg (fun x : ℝ => lemPeriod*x) hg]

theorem actual_throat_gamma (a : ℝ) (ha : 0 < a) :
    (1/a)*(∫ u in Ioi (0:ℝ), weight a (complementary c) u) =
      Real.Gamma (1/4)^2/(4*Real.sqrt (2*Real.pi)) := by
  rw [actual_throat_lemniscate a ha,lem_gamma_of_beta]

theorem actual_throat_critical (a : ℝ) (ha : 0 < a) :
    (1/a)*(∫ u in Ioi (0:ℝ), weight a (complementary c) u) =
      Real.sqrt (Real.pi/5)*criticalF0^2 := by
  rw [actual_throat_gamma a ha,critical_gamma_exact]

end
end Manuscript13.CrossThroatLemniscate20261126
#print axioms Manuscript13.CrossThroatLemniscate20261126.selfdual_sq
#print axioms Manuscript13.CrossThroatLemniscate20261126.lem_map_sq
#print axioms Manuscript13.CrossThroatLemniscate20261126.lem_map_pos
#print axioms Manuscript13.CrossThroatLemniscate20261126.lem_map_jacobian
#print axioms Manuscript13.CrossThroatLemniscate20261126.lem_map_inj
#print axioms Manuscript13.CrossThroatLemniscate20261126.lem_map_image
#print axioms Manuscript13.CrossThroatLemniscate20261126.lem_weight
#print axioms Manuscript13.CrossThroatLemniscate20261126.lem_period
#print axioms Manuscript13.CrossThroatLemniscate20261126.actual_throat_lemniscate
#print axioms Manuscript13.CrossThroatLemniscate20261126.critical_gamma_exact
#print axioms Manuscript13.CrossThroatLemniscate20261126.beta_map_inj
#print axioms Manuscript13.CrossThroatLemniscate20261126.beta_map_image
#print axioms Manuscript13.CrossThroatLemniscate20261126.beta_map_jacobian
#print axioms Manuscript13.CrossThroatLemniscate20261126.beta_weight
#print axioms Manuscript13.CrossThroatLemniscate20261126.lem_beta_integral
#print axioms Manuscript13.CrossThroatLemniscate20261126.gamma_beta_ratio
#print axioms Manuscript13.CrossThroatLemniscate20261126.lem_gamma_of_beta
#print axioms Manuscript13.CrossThroatLemniscate20261126.actual_throat_gamma
#print axioms Manuscript13.CrossThroatLemniscate20261126.actual_throat_critical
