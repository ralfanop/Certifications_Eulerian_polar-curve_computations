import Mathlib

/-! Frozen M14.119 §2.1, labels eq:eulerian-bgf and eq:eulerian-poles.
Actual meromorphic order of the Eulerian bivariate generating function.
A pole of order one is expressed as meromorphicOrderAt = -1, so the
totalized division value at the pole does not obscure the punctured germ. -/
noncomputable section
namespace Manuscript14.EulerianMeromorphicPoles

def denominator (u z : ℂ) : ℂ := Complex.exp ((u-1)*z)-u

def pole (u : ℂ) (j : ℤ) : ℂ :=
  (Complex.log u + (j:ℂ)*(2*(Real.pi:ℂ)*Complex.I))/(u-1)

def generating (u z : ℂ) : ℂ :=
  if u = 1 then 1/(1-z) else u*(1-u)/denominator u z

theorem denominator_analytic (u z : ℂ) :
    AnalyticAt ℂ (denominator u) z := by
  unfold denominator
  fun_prop

theorem denominator_derivative (u z : ℂ) :
    HasDerivAt (denominator u) ((u-1)*Complex.exp ((u-1)*z)) z := by
  have h := (Complex.hasDerivAt_exp ((u-1)*z)).comp z
    ((hasDerivAt_id z).const_mul (u-1))
  have hf : (fun x : ℂ => Complex.exp (x * (u - 1)) - u) = denominator u := by
    funext x
    simp [denominator, mul_comm]
  rw [← hf]
  simpa [mul_comm] using h.sub_const u

theorem denominator_zero_iff (u z : ℂ) (hu : u ≠ 0) (hu1 : u ≠ 1) :
    denominator u z = 0 ↔ ∃ j : ℤ, z = pole u j := by
  have hd : u-1 ≠ 0 := sub_ne_zero.mpr hu1
  unfold denominator
  rw [sub_eq_zero]
  have he := Complex.exp_eq_exp_iff_exists_int (x := (u-1)*z) (y := Complex.log u)
  rw [Complex.exp_log hu] at he
  rw [he]
  constructor
  · rintro ⟨j,hj⟩
    refine ⟨j, ?_⟩
    unfold pole
    apply (eq_div_iff hd).2
    simpa [mul_comm z (u-1)] using hj
  · rintro ⟨j,rfl⟩
    refine ⟨j, ?_⟩
    unfold pole
    field_simp [hd] <;> ring

theorem denominator_simple (u z : ℂ) (hu1 : u ≠ 1)
    (hz : denominator u z = 0) :
    analyticOrderAt (denominator u) z = 1 := by
  apply (denominator_analytic u z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz
  rw [(denominator_derivative u z).deriv]
  exact mul_ne_zero (sub_ne_zero.mpr hu1) (Complex.exp_ne_zero _)

theorem denominator_order (u z : ℂ) (hu1 : u ≠ 1) :
    meromorphicOrderAt (denominator u) z =
      if denominator u z = 0 then 1 else 0 := by
  rw [(denominator_analytic u z).meromorphicOrderAt_eq]
  by_cases hz : denominator u z = 0
  · rw [if_pos hz, denominator_simple u z hu1 hz]
    norm_num [ENat.map_natCast]
  · rw [if_neg hz, (denominator_analytic u z).analyticOrderAt_eq_zero.mpr hz]
    simp

theorem generating_meromorphic (u z : ℂ) :
    MeromorphicAt (generating u) z := by
  by_cases h : u = 1
  · have hf : generating u = (fun _ : ℂ => (1:ℂ)) / (fun w => 1-w) := by
      funext w
      simp [generating, h]
    rw [hf]
    exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1:ℂ)) z).meromorphicAt.div
      (show AnalyticAt ℂ (fun w : ℂ => 1-w) z by fun_prop).meromorphicAt
  · have hf : generating u = (fun _ : ℂ => u*(1-u)) / denominator u := by
      funext w
      simp [generating, h]
    rw [hf]
    exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => u*(1-u)) z).meromorphicAt.div
      (denominator_analytic u z).meromorphicAt

theorem generating_order (u z : ℂ) (hu : u ≠ 0) (hu1 : u ≠ 1) :
    meromorphicOrderAt (generating u) z =
      if denominator u z = 0 then -1 else 0 := by
  have hn : u*(1-u) ≠ 0 := mul_ne_zero hu (sub_ne_zero.mpr (Ne.symm hu1))
  have hf : generating u = (fun _ : ℂ => u*(1-u)) / denominator u := by
    funext w
    simp [generating, hu1]
  rw [hf, meromorphicOrderAt_div
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => u*(1-u)) z).meromorphicAt
    (denominator_analytic u z).meromorphicAt,
    meromorphicOrderAt_const, if_neg hn, denominator_order u z hu1]
  split <;> norm_num

/-- The entire pole set is exactly the logarithmic lattice, every pole simple. -/
theorem generating_simple_pole_iff (u z : ℂ) (hu : u ≠ 0) (hu1 : u ≠ 1) :
    meromorphicOrderAt (generating u) z = (-1 : WithTop ℤ) ↔
      ∃ j : ℤ, z = pole u j := by
  rw [generating_order u z hu hu1, ← denominator_zero_iff u z hu hu1]
  split <;> simp_all

theorem generating_analytic_away (u z : ℂ) (hu1 : u ≠ 1)
    (hz : denominator u z ≠ 0) : AnalyticAt ℂ (generating u) z := by
  have hf : generating u = fun w => u*(1-u)/denominator u w := by
    funext w
    simp [generating, hu1]
  rw [hf]
  exact analyticAt_const.div (denominator_analytic u z) hz

theorem unit_parameter_order (z : ℂ) :
    meromorphicOrderAt (generating 1) z = if z = 1 then -1 else 0 := by
  let d : ℂ → ℂ := fun w => 1-w
  have ha : AnalyticAt ℂ d z := by dsimp [d]; fun_prop
  have hd : deriv d z = -1 := by
    simpa [d] using ((hasDerivAt_const z (1:ℂ)).sub (hasDerivAt_id z)).deriv
  have hf : generating 1 = (fun _ : ℂ => (1:ℂ)) / d := by
    funext w
    simp [generating, d]
  rw [hf, meromorphicOrderAt_div
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1:ℂ)) z).meromorphicAt
    ha.meromorphicAt, meromorphicOrderAt_const, if_neg one_ne_zero, ha.meromorphicOrderAt_eq]
  by_cases hz : z = 1
  · rw [if_pos hz, ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp [d,hz]) (by rw [hd]; norm_num)]
    norm_num [ENat.map_natCast]
  · rw [if_neg hz, ha.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr (Ne.symm hz))]
    simp

#print axioms denominator_analytic
#print axioms denominator_derivative
#print axioms denominator_zero_iff
#print axioms denominator_simple
#print axioms denominator_order
#print axioms generating_meromorphic
#print axioms generating_order
#print axioms generating_simple_pole_iff
#print axioms generating_analytic_away
#print axioms unit_parameter_order

end Manuscript14.EulerianMeromorphicPoles
