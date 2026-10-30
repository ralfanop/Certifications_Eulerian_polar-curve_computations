import EulerianGrothendieck.ModulusRemainder

noncomputable section
namespace EulerianGrothendieck

def frameDistance (e : ℝ) (z a b : ℂ) : ℝ :=
  (‖a‖-1)^2+(‖b‖-1)^2+
  (‖(e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*b‖-1)^2+
  (‖(e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*star z*b‖-1)^2

theorem frameDistance_nonneg (e : ℝ) (z a b : ℂ) : 0 ≤ frameDistance e z a b := by
  unfold frameDistance
  positivity

/-- Every point in a small sublevel set is localized, regardless of its phases.
In particular this applies to every minimizer, without assuming uniqueness. -/
theorem frameDistance_sublevel_localization (e : ℝ) (z a b : ℂ)
    (he : 0 ≤ e) (h : frameDistance e z a b ≤ 16*e^2) :
    |‖a‖-1| ≤ 4*e ∧ |‖b‖-1| ≤ 4*e := by
  have ha : (‖a‖-1)^2 ≤ 16*e^2 := by
    unfold frameDistance at h
    nlinarith [sq_nonneg (‖b‖-1),
      sq_nonneg (‖(e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*b‖-1),
      sq_nonneg (‖(e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*star z*b‖-1)]
  have hb : (‖b‖-1)^2 ≤ 16*e^2 := by
    unfold frameDistance at h
    nlinarith [sq_nonneg (‖a‖-1),
      sq_nonneg (‖(e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*b‖-1),
      sq_nonneg (‖(e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*star z*b‖-1)]
  constructor <;> apply (abs_le).2 <;> constructor <;> nlinarith

theorem sqrt_unit_loss (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    |Real.sqrt (1-e^2)-1| ≤ e^2 := by
  have hd : 0 ≤ 1-e^2 := by nlinarith
  have hs := Real.sq_sqrt hd
  have hs0 := Real.sqrt_nonneg (1-e^2)
  have hs1 : Real.sqrt (1-e^2) ≤ 1 := by nlinarith
  rw [abs_of_nonpos (by linarith)]
  nlinarith

/-- A unit pair provides a uniform O(e^2) trial value for every unit phase. -/
theorem frameDistance_unit_trial (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (z a b : ℂ) (hz : ‖z‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    frameDistance e z a b ≤ 8*e^2 := by
  have hq := sqrt_unit_loss e he0 he1
  have hbound : ∀ v : ℂ, ‖v‖=1 →
      |‖(e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*v‖-1| ≤ 2*e := by
    intro v hv
    have hn := abs_norm_sub_norm_le ((e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*v) v
    rw [hv] at hn
    have heq : (e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*v-v =
        (e:ℂ)*a+((Real.sqrt (1-e^2)-1:ℝ):ℂ)*v := by push_cast; ring
    rw [heq] at hn
    have ht := norm_add_le ((e:ℂ)*a) (((Real.sqrt (1-e^2)-1:ℝ):ℂ)*v)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, ha, hv, mul_one,
      abs_of_nonneg he0] at ht
    nlinarith
  have h1 := hbound b hb
  have hz' : ‖star z*b‖ = 1 := by simp [norm_mul, hz, hb]
  have h2 := hbound (star z*b) hz'
  have hs1 : (‖(e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*b‖-1)^2 ≤ 4*e^2 := by
    have hab := abs_nonneg (‖(e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*b‖-1)
    nlinarith [sq_abs (‖(e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*b‖-1)]
  have hs2 : (‖(e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*star z*b‖-1)^2 ≤ 4*e^2 := by
    have hab := abs_nonneg (‖(e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*star z*b‖-1)
    rw [mul_assoc] at *
    nlinarith [sq_abs (‖(e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*(star z*b)‖-1)]
  unfold frameDistance
  rw [ha,hb]
  nlinarith

end EulerianGrothendieck
