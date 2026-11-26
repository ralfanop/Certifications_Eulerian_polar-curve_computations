import Mathlib

/-!
Manuscript 11, revision 2026-11-25, Proposition 3.17, p. 28.
Actual centred uniform law represented by its unit-density interval integral.
Candidate first tranche: real MGF, removable value, moments and algebraic jet.
The analytic O(h^6) remainder and identification with the analytic log derivative
are separate obligations; the formal polynomial identity alone does not prove them.
-/
open Real MeasureTheory Set intervalIntegral
noncomputable section

namespace EulerianCert.M11StandardizedCumulant

def mgf (h : ℝ) : ℝ :=
  ∫ u in (-1 / 2 : ℝ)..(1 / 2), Real.exp (Real.sqrt 12 * h * u)

def moment (n : ℕ) : ℝ :=
  ∫ u in (-1 / 2 : ℝ)..(1 / 2), (Real.sqrt 12 * u) ^ n

lemma sqrt12_eq : Real.sqrt 12 = 2 * Real.sqrt 3 := by
  rw [show (12 : ℝ) = 4 * 3 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

theorem mgf_zero : mgf 0 = 1 := by
  norm_num [mgf]

/-- The closed form away from the removable singularity, Eq. (116). -/
theorem mgf_eq_sinh (h : ℝ) (hh : h ≠ 0) :
    mgf h = Real.sinh (Real.sqrt 3 * h) / (Real.sqrt 3 * h) := by
  let c : ℝ := Real.sqrt 12 * h
  have hc : c ≠ 0 := mul_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num))) hh
  have D : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.exp (c * y) / c)
      (Real.exp (c * x)) x := by
    intro x
    have hd := ((Real.hasDerivAt_exp (c * x)).comp x
      ((hasDerivAt_id x).const_mul c)).div_const c
    have hcancel : Real.exp (c * x) * (c * 1) / c = Real.exp (c * x) := by
      rw [mul_one, mul_div_cancel_right₀ _ hc]
    rw [hcancel] at hd
    exact hd
  have he : (∫ x in (-1 / 2 : ℝ)..(1 / 2), Real.exp (c * x)) =
      Real.exp (c * (1 / 2)) / c - Real.exp (c * (-1 / 2)) / c := by
    rw [intervalIntegral.integral_deriv_eq_sub' _ (funext fun x => (D x).deriv)
      (fun x _ => (D x).differentiableAt)]
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hc' : c = 2 * (Real.sqrt 3 * h) := by
    simp [c, sqrt12_eq]
    ring
  change (∫ x in (-1 / 2 : ℝ)..(1 / 2), Real.exp (c * x)) = _
  rw [he, hc', Real.sinh_eq]
  rw [show 2 * (Real.sqrt 3 * h) * (1 / 2) = Real.sqrt 3 * h by ring,
      show 2 * (Real.sqrt 3 * h) * (-1 / 2) = -(Real.sqrt 3 * h) by ring]
  have hz : Real.sqrt 3 * h ≠ 0 := mul_ne_zero
    (ne_of_gt (Real.sqrt_pos.2 (by norm_num))) hh
  field_simp

/-- Joint total version of (116) and (117); division by zero in Lean is not the extension. -/
theorem mgf_eq_total (h : ℝ) :
    mgf h = if h = 0 then 1 else Real.sinh (Real.sqrt 3 * h) / (Real.sqrt 3 * h) := by
  by_cases hh : h = 0
  · subst h
    simp [mgf_zero]
  · simpa [hh] using mgf_eq_sinh h hh

theorem moment_eq (n : ℕ) : moment n =
    (Real.sqrt 12) ^ n * (((1 / 2 : ℝ) ^ (n + 1) -
      (-1 / 2 : ℝ) ^ (n + 1)) / ((n : ℝ) + 1)) := by
  unfold moment
  simp only [mul_pow]
  rw [intervalIntegral.integral_const_mul, integral_pow]

theorem moment_one : moment 1 = 0 := by
  rw [moment_eq]
  norm_num

theorem moment_two : moment 2 = 1 := by
  rw [moment_eq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
  norm_num

theorem moment_four : moment 4 = 9 / 5 := by
  have hs : (Real.sqrt 12) ^ 4 = 144 := by
    calc
      (Real.sqrt 12) ^ 4 = ((Real.sqrt 12) ^ 2) ^ 2 := by ring
      _ = 144 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]; norm_num
  rw [moment_eq, hs]
  norm_num

/-- Eq. (119), through the actual centered standardized moments.
    The identification with the fourth derivative of log mgf is not yet claimed. -/
theorem fourth_centered_cumulant : moment 4 - 3 * (moment 2) ^ 2 = -6 / 5 := by
  rw [moment_four, moment_two]
  norm_num

/-- Algebraic precursor for (118), not an analytic remainder estimate. -/
theorem quartic_log_jet (h : ℝ) :
    (h ^ 2 / 2 + 3 * h ^ 4 / 40) - (h ^ 2 / 2) ^ 2 / 2 =
    h ^ 2 / 2 - h ^ 4 / 20 := by ring

theorem fourth_log_coefficient : (Nat.factorial 4 : ℝ) * (-1 / 20) = -6 / 5 := by
  norm_num [Nat.factorial]

#print axioms EulerianCert.M11StandardizedCumulant.mgf_zero
#print axioms EulerianCert.M11StandardizedCumulant.mgf_eq_sinh
#print axioms EulerianCert.M11StandardizedCumulant.mgf_eq_total
#print axioms EulerianCert.M11StandardizedCumulant.moment_eq
#print axioms EulerianCert.M11StandardizedCumulant.moment_one
#print axioms EulerianCert.M11StandardizedCumulant.moment_two
#print axioms EulerianCert.M11StandardizedCumulant.moment_four
#print axioms EulerianCert.M11StandardizedCumulant.fourth_centered_cumulant
#print axioms EulerianCert.M11StandardizedCumulant.quartic_log_jet
#print axioms EulerianCert.M11StandardizedCumulant.fourth_log_coefficient

end EulerianCert.M11StandardizedCumulant


/-! ## Analytic completion of Proposition 3.17 (candidate until exact-head CI).
The remainder is an analytic factor, not a formal truncated series. -/

open Filter Topology Asymptotics
open scoped ContDiff

namespace EulerianCert.M11StandardizedCumulant

def complexNumerator (z : ℂ) : ℂ :=
  (Complex.exp z - Complex.exp (-z)) / 2

def complexMGF (z : ℂ) : ℂ :=
  dslope complexNumerator 0 ((Real.sqrt 3 : ℂ) * z)

lemma complexNumerator_analytic (z : ℂ) : AnalyticAt ℂ complexNumerator z := by
  unfold complexNumerator
  fun_prop

lemma complexNumerator_zero : complexNumerator 0 = 0 := by
  simp [complexNumerator]

lemma complexNumerator_deriv_zero : deriv complexNumerator 0 = 1 := by
  have hp := Complex.hasDerivAt_exp (0 : ℂ)
  have hm := (Complex.hasDerivAt_exp (-(0 : ℂ))).comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
  have hd := (hp.sub hm).div_const (2 : ℂ)
  change deriv (fun z : ℂ => (Complex.exp z - Complex.exp (-z)) / 2) 0 = 1
  simpa [Function.comp_def] using hd.deriv

theorem complexMGF_zero : complexMGF 0 = 1 := by
  rw [complexMGF, mul_zero, dslope_same, complexNumerator_deriv_zero]

theorem complexMGF_eq_sinh (z : ℂ) (hz : z ≠ 0) :
    complexMGF z = Complex.sinh ((Real.sqrt 3 : ℂ) * z) / ((Real.sqrt 3 : ℂ) * z) := by
  have hc : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)))
  rw [complexMGF, dslope_of_ne _ (mul_ne_zero hc hz)]
  simp [slope, complexNumerator, Complex.sinh, div_eq_inv_mul]

theorem complexMGF_entire (z : ℂ) : AnalyticAt ℂ complexMGF z := by
  have hd : DifferentiableOn ℂ complexNumerator Set.univ :=
    fun w _ => (complexNumerator_analytic w).differentiableAt.differentiableWithinAt
  have hds : Differentiable ℂ (dslope complexNumerator 0) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope
      (s := Set.univ) (c := (0 : ℂ)) (by simp)).2 hd)
  have hda : Differentiable ℂ complexMGF := by
    unfold complexMGF
    have hlin : Differentiable ℂ (fun w : ℂ => (Real.sqrt 3 : ℂ) * w) := by fun_prop
    exact hds.comp hlin
  exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    (Filter.Eventually.of_forall hda) (hda z).continuousAt

theorem complexMGF_restrict_real (h : ℝ) : complexMGF (h : ℂ) = (mgf h : ℂ) := by
  by_cases hh : h = 0
  · subst h
    simp [complexMGF_zero, mgf_zero]
  · have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
    rw [complexMGF_eq_sinh _ hc, mgf_eq_sinh h hh]
    push_cast

/-- Taylor expansion of the actual real exponential, with an analytic seventh-order factor. -/
lemma exp_jet7 (c : ℝ) :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧ ∀ h : ℝ,
      Real.exp (c*h) =
        1 + c*h + (c*h)^2/2 + (c*h)^3/6 + (c*h)^4/24 +
        (c*h)^5/120 + (c*h)^6/720 + h^7*R h := by
  have ha : AnalyticAt ℝ (fun h : ℝ => Real.exp (c*h)) 0 := by fun_prop
  obtain ⟨R,hR,hEq⟩ := ha.exists_eq_sum_add_pow_mul 7
  refine ⟨R,hR,fun h => ?_⟩
  have H := hEq h
  simp only [iteratedDeriv_exp_const_mul, mul_zero, Real.exp_zero, mul_one,
    smul_eq_mul] at H
  norm_num [Finset.sum_range_succ] at H
  convert H using 1 <;> ring

/-- Actual MGF: the even fourth-degree jet and analytic sixth-order factor. -/
theorem mgf_analytic_jet :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧ ∀ h : ℝ,
      mgf h = 1 + h^2/2 + 3*h^4/40 + h^6*R h := by
  let c : ℝ := Real.sqrt 3
  have hc : c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hc2 : c^2 = 3 := Real.sq_sqrt (by norm_num)
  have hc4 : c^4 = 9 := by calc
    c^4 = (c^2)^2 := by ring
    _ = 9 := by rw [hc2]; norm_num
  obtain ⟨P,hP,hp⟩ := exp_jet7 c
  obtain ⟨N,hN,hn⟩ := exp_jet7 (-c)
  refine ⟨fun h => (P h - N h)/(2*c), (hP.sub hN).div_const, ?_⟩
  intro h
  by_cases hh : h = 0
  · subst h
    simp [mgf_zero]
  · have hd : Real.exp (c*h) - Real.exp ((-c)*h) =
        2*c*h*(1+c^2*h^2/6+c^4*h^4/120+h^6*((P h-N h)/(2*c))) := by
      rw [hp h, hn h]
      field_simp [hc]
      ring
    have hs : mgf h = Real.sinh (c*h)/(c*h) := mgf_eq_sinh h hh
    rw [hs, Real.sinh_eq, show -(c*h) = (-c)*h by ring, hd, hc2, hc4]
    field_simp [hc,hh]
    ring

theorem mgf_analyticAt_zero : AnalyticAt ℝ mgf 0 := by
  obtain ⟨R,hR,h⟩ := mgf_analytic_jet
  rw [show mgf = (fun x => 1+x^2/2+3*x^4/40+x^6*R x) from funext h]
  fun_prop

lemma log_one_add_jet :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧ ∀ t : ℝ,
      Real.log (1+t) = t-t^2/2+t^3*R t := by
  have ha : AnalyticAt ℝ (fun t : ℝ => Real.log (1+t)) 0 := by
    have hl : AnalyticAt ℝ Real.log (1 : ℝ) :=
      (Real.contDiffAt_log (n := ω)).2 (by norm_num) |>.analyticAt
    have hlin : AnalyticAt ℝ (fun t : ℝ => 1+t) 0 := by fun_prop
    exact hl.comp_of_eq hlin (by norm_num)
  have hd : deriv (fun t : ℝ => Real.log (1+t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => (1+t)⁻¹ := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)] with t ht
    have hz : (1+t : ℝ) ≠ 0 := by linarith [ht.1]
    have H := ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).log hz
    simpa [one_div] using H.deriv
  have h1 : iteratedDeriv 1 (fun t : ℝ => Real.log (1+t)) 0 = 1 := by
    rw [iteratedDeriv_one]
    simpa using hd.self_of_nhds
  have h2 : iteratedDeriv 2 (fun t : ℝ => Real.log (1+t)) 0 = -1 := by
    rw [show (2 : ℕ) = 1+1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq]
    have H := (hasDerivAt_inv (by norm_num : (1+(0 : ℝ)) ≠ 0)).comp (0 : ℝ)
      ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_id (0 : ℝ)))
    simpa [Function.comp_def] using H.deriv
  obtain ⟨R,hR,hEq⟩ := ha.exists_eq_sum_add_pow_mul 3
  refine ⟨R,hR,fun t => ?_⟩
  have H := hEq t
  norm_num [Finset.sum_range_succ, smul_eq_mul, h1,h2] at H
  convert H using 1 <;> ring

/-- Stronger than Eq. (118): exact equality with an analytic sixth-order factor. -/
theorem log_mgf_analytic_jet :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧ ∀ h : ℝ,
      Real.log (mgf h) = h^2/2-h^4/20+h^6*R h := by
  obtain ⟨R,hR,hr⟩ := mgf_analytic_jet
  obtain ⟨S,hS,hs⟩ := log_one_add_jet
  let B : ℝ → ℝ := fun h => 3/40+h^2*R h
  let A : ℝ → ℝ := fun h => 1/2+h^2*B h
  let u : ℝ → ℝ := fun h => h^2*A h
  have hB : AnalyticAt ℝ B 0 := by dsimp [B]; fun_prop
  have hA : AnalyticAt ℝ A 0 := by dsimp [A]; fun_prop
  have hu : AnalyticAt ℝ u 0 := by dsimp [u]; fun_prop
  have hu0 : u 0 = 0 := by simp [u]
  have hSu : AnalyticAt ℝ (fun h => S (u h)) 0 := by
    have h := hS
    rw [← hu0] at h
    exact h.comp hu
  have hA' : AnalyticAt ℝ (fun h => A h + 1/2) 0 := by fun_prop
  have hBA : AnalyticAt ℝ (fun h => B h * (A h + 1/2)/2) 0 :=
    (hB.mul hA').div_const
  have hprod : AnalyticAt ℝ (fun h => (A h)^3 * S (u h)) 0 :=
    (hA.pow 3).mul hSu
  refine ⟨fun h => R h-B h*(A h+1/2)/2+(A h)^3*S (u h),
    (hR.sub hBA).add hprod, ?_⟩
  intro h
  have hm : mgf h = 1+u h := by rw [hr h]; dsimp [u,A,B]; ring
  rw [hm, hs (u h)]
  dsimp [u,A,B]
  ring

theorem log_mgf_bigO :
    (fun h : ℝ => Real.log (mgf h) - (h^2/2-h^4/20)) =O[𝓝 (0 : ℝ)]
      (fun h : ℝ => h^6) := by
  obtain ⟨R,hR,hr⟩ := log_mgf_analytic_jet
  refine Asymptotics.IsBigO.of_bound (‖R 0‖+1) ?_
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hR.continuousAt 1 (by norm_num)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
  have hd : dist (R h) (R 0) < 1 := hclose (Metric.mem_ball.mp hh)
  have hb : ‖R h‖ ≤ ‖R 0‖+1 := by
    rw [dist_eq_norm] at hd
    calc
      ‖R h‖ = ‖(R h-R 0)+R 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖R h-R 0‖+‖R 0‖ := norm_add_le _ _
      _ ≤ ‖R 0‖+1 := by linarith
  rw [hr h, add_sub_cancel_left, norm_mul]
  calc
    ‖h^6‖ * ‖R h‖ ≤ ‖h^6‖ * (‖R 0‖+1) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = (‖R 0‖+1)*‖h^6‖ := mul_comm _ _

theorem log_mgf_fourth_deriv :
    iteratedDeriv 4 (fun h : ℝ => Real.log (mgf h)) 0 = -6/5 := by
  obtain ⟨R,hR,hr⟩ := log_mgf_analytic_jet
  let f : ℝ → ℝ := fun h => Real.log (mgf h)
  let P : ℝ → ℝ := fun h => h^2/2-h^4/20
  have hf : AnalyticAt ℝ f 0 := by
    rw [show f = (fun h => h^2/2-h^4/20+h^6*R h) from funext hr]
    fun_prop
  have hP : AnalyticAt ℝ P 0 := by dsimp [P]; fun_prop
  have hdiff : AnalyticAt ℝ (f-P) 0 := hf.sub hP
  have hord : (6 : ℕ∞) ≤ analyticOrderAt (f-P) 0 := by
    apply (natCast_le_analyticOrderAt hdiff (n := 6)).2
    refine ⟨R,hR,Filter.Eventually.of_forall (fun h => ?_)⟩
    simp only [Pi.sub_apply, smul_eq_mul, f,P,hr]
    ring
  have hz := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hdiff).1 hord 4 (by norm_num)
  rw [iteratedDeriv_sub hf.contDiffAt hP.contDiffAt] at hz
  have hp : iteratedDeriv 4 P 0 = -6/5 := by
    have he : P = (fun h : ℝ => (1/2)*h^2) - (fun h : ℝ => (1/20)*h^4) := by
      funext h
      simp [P]
      ring
    rw [he, iteratedDeriv_sub (by fun_prop) (by fun_prop),
      iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
    norm_num [iteratedDeriv_fun_pow_zero]
  change iteratedDeriv 4 f 0 = -6/5
  linarith

theorem fourth_derivative_eq_moment_cumulant :
    iteratedDeriv 4 (fun h : ℝ => Real.log (mgf h)) 0 =
      moment 4 - 3*(moment 2)^2 := by
  rw [log_mgf_fourth_deriv, fourth_centered_cumulant]

#print axioms EulerianCert.M11StandardizedCumulant.complexMGF_zero
#print axioms EulerianCert.M11StandardizedCumulant.complexMGF_eq_sinh
#print axioms EulerianCert.M11StandardizedCumulant.complexMGF_entire
#print axioms EulerianCert.M11StandardizedCumulant.complexMGF_restrict_real
#print axioms EulerianCert.M11StandardizedCumulant.mgf_analytic_jet
#print axioms EulerianCert.M11StandardizedCumulant.mgf_analyticAt_zero
#print axioms EulerianCert.M11StandardizedCumulant.log_mgf_analytic_jet
#print axioms EulerianCert.M11StandardizedCumulant.log_mgf_bigO
#print axioms EulerianCert.M11StandardizedCumulant.log_mgf_fourth_deriv
#print axioms EulerianCert.M11StandardizedCumulant.fourth_derivative_eq_moment_cumulant

end EulerianCert.M11StandardizedCumulant
