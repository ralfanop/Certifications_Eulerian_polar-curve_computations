import EulerianGrothendieck.RescaledObjective

noncomputable section
namespace EulerianGrothendieck
set_option maxHeartbeats 1500000

theorem unit_mul_star (z : ℂ) (hz : ‖z‖ = 1) : z * star z = 1 := by
  have h : Complex.normSq z = 1 := by rw [← Complex.sq_norm, hz]; norm_num
  simpa only [Complex.star_def, Complex.mul_conj, h, Complex.ofReal_one]

theorem frameDistance_rotate (e : ℝ) (z a b t : ℂ) (ht : ‖t‖=1) :
    frameDistance e z (a*t) (b*t) = frameDistance e z a b := by
  have h1 : (e:ℂ)*(a*t)+(Real.sqrt (1-e^2):ℂ)*(b*t) =
      ((e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*b)*t := by ring
  have h2 : (e:ℂ)*(a*t)+(Real.sqrt (1-e^2):ℂ)*star z*(b*t) =
      ((e:ℂ)*a+(Real.sqrt (1-e^2):ℂ)*star z*b)*t := by ring
  simp only [frameDistance, h1, h2, norm_mul, ht, mul_one]

theorem frameDistance_coordinates (e u v : ℝ) (z y : ℂ)
    (hu : 0 ≤ 1+e*u) (hv : 0 ≤ 1+e*v) (hy : ‖y‖=1) (hz : ‖z‖=1) :
    frameDistance e z (((1+e*u:ℝ):ℂ)*y) ((1+e*v:ℝ):ℂ) =
      coordinateDistance e z u v y := by
  have h1 : (e:ℂ)*(((1+e*u:ℝ):ℂ)*y)+(Real.sqrt (1-e^2):ℂ)*((1+e*v:ℝ):ℂ) =
      1+coordinatePerturbation e u v y := by unfold coordinatePerturbation; push_cast; ring
  have h2 : z*((e:ℂ)*(((1+e*u:ℝ):ℂ)*y)+
      (Real.sqrt (1-e^2):ℂ)*star z*((1+e*v:ℝ):ℂ)) =
      1+coordinatePerturbation e u v (z*y) := by
    have hs := unit_mul_star z hz
    calc
      _ = (e:ℂ)*(((1+e*u:ℝ):ℂ)*(z*y))+
          (Real.sqrt (1-e^2):ℂ)*(z*star z)*((1+e*v:ℝ):ℂ) := by ring
      _ = _ := by rw [hs]; unfold coordinatePerturbation; push_cast; ring
  have hn2 := congrArg norm h2
  rw [norm_mul, hz, one_mul] at hn2
  unfold frameDistance coordinateDistance
  rw [h1, hn2]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hy, mul_one,
    abs_of_nonneg hu, abs_of_nonneg hv]
  ring

/-- Every sufficiently small sublevel point admits bounded radial coordinates;
the phase is arbitrary, not chosen to minimize the quadratic model. -/
theorem frameDistance_sublevel_coordinates (e : ℝ) (z a b : ℂ)
    (he : 0 < e) (he1 : e ≤ 1/12) (hz : ‖z‖=1)
    (hd : frameDistance e z a b ≤ 16*e^2) :
    ∃ u v : ℝ, ∃ y : ℂ, |u| ≤ 4 ∧ |v| ≤ 4 ∧ ‖y‖=1 ∧
      frameDistance e z a b = coordinateDistance e z u v y := by
  obtain ⟨ha,hb⟩ := frameDistance_sublevel_localization e z a b he.le hd
  have ha0 : 0 < ‖a‖ := by have := (abs_le.mp ha).1; linarith
  have hb0 : 0 < ‖b‖ := by have := (abs_le.mp hb).1; linarith
  let u : ℝ := (‖a‖-1)/e
  let v : ℝ := (‖b‖-1)/e
  let t : ℂ := b / (‖b‖:ℂ)
  let y : ℂ := (a / (‖a‖:ℂ)) / t
  have ht : ‖t‖=1 := by
    dsimp [t]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0.le]
    exact div_self hb0.ne'
  have ht0 : t ≠ 0 := by intro h; rw [h, norm_zero] at ht; norm_num at ht
  have hy : ‖y‖=1 := by
    dsimp [y]
    rw [norm_div, norm_div, ht, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ha0.le, div_self ha0.ne', div_one]
  have hu : 1+e*u = ‖a‖ := by dsimp [u]; field_simp; ring
  have hv : 1+e*v = ‖b‖ := by dsimp [v]; field_simp; ring
  have hca : (((1+e*u:ℝ):ℂ)*y)*t = a := by
    rw [hu]
    dsimp [y]
    have hn : (‖a‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0.ne'
    field_simp
  have hcb : ((1+e*v:ℝ):ℂ)*t = b := by
    rw [hv]
    dsimp [t]
    have hn : (‖b‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb0.ne'
    field_simp
  refine ⟨u,v,y,?_,?_,hy,?_⟩
  · dsimp [u]; rw [abs_div, abs_of_pos he]; exact (div_le_iff₀ he).mpr ha
  · dsimp [v]; rw [abs_div, abs_of_pos he]; exact (div_le_iff₀ he).mpr hb
  · rw [← hca, ← hcb, frameDistance_rotate e z _ _ t ht]
    exact frameDistance_coordinates e u v z y (by rw [hu]; positivity)
      (by rw [hv]; positivity) hy hz

end EulerianGrothendieck
