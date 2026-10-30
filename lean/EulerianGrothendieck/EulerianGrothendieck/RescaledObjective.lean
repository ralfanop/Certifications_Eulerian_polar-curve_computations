import EulerianGrothendieck.GlobalLocalization

noncomputable section
namespace EulerianGrothendieck
set_option maxHeartbeats 1000000

theorem modulus_linearized_square_bound (e a : ℝ) (w : ℂ)
    (he0 : 0 ≤ e) (he1 : e ≤ 1/12) (ha : |a| ≤ 5)
    (hw : ‖w‖ ≤ 6*e) (hlin : |w.re-e*a| ≤ 6*e^2) :
    |(‖1+w‖-1)^2-e^2*a^2| ≤ 1000*e^3 := by
  have hsmall : ‖w‖ ≤ 1/2 := by linarith
  have hbase := complex_modulus_squared_remainder w hsmall
  have hpow := pow_le_pow_left₀ (norm_nonneg w) hw 3
  have hre : |w.re| ≤ 6*e := (Complex.abs_re_le_norm w).trans hw
  have hea : |e*a| ≤ 5*e := by rw [abs_mul, abs_of_nonneg he0]; nlinarith
  have hsq : |w.re^2-(e*a)^2| ≤ (6*e^2)*(11*e) := by
    rw [show w.re^2-(e*a)^2 = (w.re-e*a)*(w.re+e*a) by ring, abs_mul]
    apply mul_le_mul hlin _ (abs_nonneg _) (by positivity)
    exact (abs_add_le _ _).trans (by linarith)
  calc
    |(‖1+w‖-1)^2-e^2*a^2| =
        |((‖1+w‖-1)^2-w.re^2)+(w.re^2-(e*a)^2)| := by congr 1; ring
    _ ≤ |(‖1+w‖-1)^2-w.re^2|+|w.re^2-(e*a)^2| := abs_add_le _ _
    _ ≤ 3*‖w‖^3+(6*e^2)*(11*e) := add_le_add hbase hsq
    _ ≤ 3*(6*e)^3+(6*e^2)*(11*e) := by nlinarith
    _ ≤ 1000*e^3 := by nlinarith [pow_nonneg he0 3]

def coordinatePerturbation (e u v : ℝ) (y : ℂ) : ℂ :=
  (e:ℂ)*(1+e*u)*y + ((Real.sqrt (1-e^2)*(1+e*v)-1:ℝ):ℂ)

theorem coordinatePerturbation_split (e u v : ℝ) (y : ℂ) :
    coordinatePerturbation e u v y - (e:ℂ)*((v:ℂ)+y) =
      ((e^2*u:ℝ):ℂ)*y + (((Real.sqrt (1-e^2)-1)*(1+e*v):ℝ):ℂ) := by
  unfold coordinatePerturbation
  push_cast
  ring

theorem coordinatePerturbation_residual (e u v : ℝ) (y : ℂ)
    (he0 : 0 ≤ e) (he1 : e ≤ 1/12) (hu : |u| ≤ 4) (hv : |v| ≤ 4) (hy : ‖y‖=1) :
    ‖coordinatePerturbation e u v y - (e:ℂ)*((v:ℂ)+y)‖ ≤ 6*e^2 := by
  rw [coordinatePerturbation_split]
  have hq := sqrt_unit_loss e he0 (by linarith)
  have ht := norm_add_le (((e^2*u:ℝ):ℂ)*y)
    ((((Real.sqrt (1-e^2)-1)*(1+e*v):ℝ):ℂ))
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hy, mul_one, abs_mul,
    abs_pow, abs_of_nonneg he0] at ht
  have hv1 : |1+e*v| ≤ 1+4*e := by
    calc
      _ ≤ |(1:ℝ)|+|e*v| := abs_add_le _ _
      _ ≤ 1+4*e := by rw [abs_mul, abs_of_nonneg he0]; norm_num; nlinarith
  have ht1 := mul_le_mul hq hv1 (abs_nonneg _) (sq_nonneg e)
  have ht2 := mul_le_mul_of_nonneg_left hu (sq_nonneg e)
  nlinarith [mul_nonneg (sq_nonneg e) (show 0 ≤ 1/2-4*e by linarith)]

theorem coordinatePerturbation_bounds (e u v : ℝ) (y : ℂ)
    (he0 : 0 ≤ e) (he1 : e ≤ 1/12) (hu : |u| ≤ 4) (hv : |v| ≤ 4) (hy : ‖y‖=1) :
    ‖coordinatePerturbation e u v y‖ ≤ 6*e ∧
    |(coordinatePerturbation e u v y).re-e*(v+y.re)| ≤ 6*e^2 := by
  have hr := coordinatePerturbation_residual e u v y he0 he1 hu hv hy
  have hn : ‖(e:ℂ)*((v:ℂ)+y)‖ ≤ 5*e := by
    have ht := norm_add_le (v:ℂ) y
    simp only [Complex.norm_real, Real.norm_eq_abs, hy] at ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he0]
    nlinarith
  constructor
  · have htri := norm_add_le
      (coordinatePerturbation e u v y-(e:ℂ)*((v:ℂ)+y)) ((e:ℂ)*((v:ℂ)+y))
    rw [sub_add_cancel] at htri
    nlinarith [mul_nonneg he0 (show 0 ≤ 1-6*e by linarith)]
  · have h := (Complex.abs_re_le_norm
      (coordinatePerturbation e u v y-(e:ℂ)*((v:ℂ)+y))).trans hr
    simpa only [Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using h

def coordinateDistance (e : ℝ) (z : ℂ) (u v : ℝ) (y : ℂ) : ℝ :=
  e^2*u^2+e^2*v^2 + (‖1+coordinatePerturbation e u v y‖-1)^2 +
    (‖1+coordinatePerturbation e u v (z*y)‖-1)^2

def limitingObjective (z : ℂ) (u v : ℝ) (y : ℂ) : ℝ :=
  u^2+v^2+(v+y.re)^2+(v+(z*y).re)^2

theorem coordinateDistance_uniform_remainder (e : ℝ) (z y : ℂ) (u v : ℝ)
    (he0 : 0 ≤ e) (he1 : e ≤ 1/12) (hu : |u| ≤ 4) (hv : |v| ≤ 4)
    (hy : ‖y‖=1) (hz : ‖z‖=1) :
    |coordinateDistance e z u v y-e^2*limitingObjective z u v y| ≤ 2000*e^3 := by
  have hzy : ‖z*y‖=1 := by rw [norm_mul, hz, hy, one_mul]
  have hb := coordinatePerturbation_bounds e u v y he0 he1 hu hv hy
  have hb' := coordinatePerturbation_bounds e u v (z*y) he0 he1 hu hv hzy
  have ha : |v+y.re| ≤ 5 := (abs_add_le _ _).trans (by have := Complex.abs_re_le_norm y; linarith)
  have ha' : |v+(z*y).re| ≤ 5 := (abs_add_le _ _).trans (by have := Complex.abs_re_le_norm (z*y); linarith)
  have h1 := modulus_linearized_square_bound e (v+y.re) _ he0 he1 ha hb.1 hb.2
  have h2 := modulus_linearized_square_bound e (v+(z*y).re) _ he0 he1 ha' hb'.1 hb'.2
  have he : coordinateDistance e z u v y-e^2*limitingObjective z u v y =
      ((‖1+coordinatePerturbation e u v y‖-1)^2-e^2*(v+y.re)^2)+
      ((‖1+coordinatePerturbation e u v (z*y)‖-1)^2-e^2*(v+(z*y).re)^2) := by
    unfold coordinateDistance limitingObjective
    ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

end EulerianGrothendieck
