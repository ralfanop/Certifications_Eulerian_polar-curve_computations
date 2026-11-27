import SpecialImaginaryPoint.EulerianLegendreTaylorRemainder
import SpecialImaginaryPoint.EulerianLangevinRange
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

namespace M14.EulerianLegendre
noncomputable section
open Set Filter
open scoped Topology

def rateDomain : Set ℝ := Ioo (-1) 1

theorem rateDomain_zero : (0 : ℝ) ∈ rateDomain := by norm_num [rateDomain]

theorem rateDomain_neg {x : ℝ} (hx : x ∈ rateDomain) : -x ∈ rateDomain := by
  exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

theorem rateDomain_eventually {x : ℝ} (hx : x ∈ rateDomain) :
    ∀ᶠ y in 𝓝 x, y ∈ rateDomain :=
  isOpen_Ioo.mem_nhds hx

theorem inverseLangevin_zero : inverseLangevin 0 = 0 := by
  simpa [langevin] using inverseLangevin_left 0

theorem inverseLangevin_analytic {m : ℝ} (hm : m ∈ rateDomain) :
    AnalyticAt ℝ inverseLangevin m := by
  have h := inverseLangevin_right_on_interval m hm
  have hf : AnalyticAt ℝ langevin (inverseLangevin m) := langevin_analytic _
  have he : inverseLangevin ∘ langevin = id := funext inverseLangevin_left
  have ha : AnalyticAt ℝ (inverseLangevin ∘ langevin) (inverseLangevin m) := by
    rw [he]
    exact analyticAt_id
  have hi := (analyticAt_comp_iff_of_deriv_ne_zero hf
    (ne_of_gt (langevin_deriv_pos (inverseLangevin m)))).mp ha
  rwa [h] at hi

theorem inverseLangevin_odd_on {m : ℝ} (hm : m ∈ rateDomain) :
    inverseLangevin (-m) = -inverseLangevin m := by
  apply langevin_strictMono.injective
  rw [inverseLangevin_right_on_interval (-m) (rateDomain_neg hm), langevin_odd,
    inverseLangevin_right_on_interval m hm]

theorem inverseLangevin_product {m : ℝ} (hm : m ∈ rateDomain) :
    deriv langevin (inverseLangevin m) * deriv inverseLangevin m = 1 := by
  have hd := (inverseLangevin_hasStrictDerivAt (inverseLangevin m)).hasDerivAt
  rw [inverseLangevin_right_on_interval m hm] at hd
  rw [hd.deriv]
  exact mul_inv_cancel₀ (ne_of_gt (langevin_deriv_pos (inverseLangevin m)))

def inverseSlope (m : ℝ) : ℝ := deriv langevin (inverseLangevin m)

theorem inverseSlope_analytic {m : ℝ} (hm : m ∈ rateDomain) :
    AnalyticAt ℝ inverseSlope m :=
  (langevin_analytic (inverseLangevin m)).deriv.comp (inverseLangevin_analytic hm)

theorem inverseSlope_deriv {m : ℝ} (hm : m ∈ rateDomain) :
    deriv inverseSlope m = deriv (deriv langevin) (inverseLangevin m) * deriv inverseLangevin m := by
  have h := ((langevin_analytic (inverseLangevin m)).deriv.differentiableAt.hasDerivAt).comp m
    (inverseLangevin_analytic hm).differentiableAt.hasDerivAt
  exact h.deriv

theorem inverseSlope_zero : inverseSlope 0 = 1 / 3 := by
  rw [inverseSlope, inverseLangevin_zero, langevin_hasDerivAt_zero.deriv]

theorem inverseSlope_deriv_zero : deriv inverseSlope 0 = 0 := by
  rw [inverseSlope_deriv rateDomain_zero, inverseLangevin_zero, langevin_second_deriv_zero, zero_mul]

theorem inverseSlope_second_zero : deriv (deriv inverseSlope) 0 = -(6 / 5) := by
  have he : deriv inverseSlope =ᶠ[𝓝 (0 : ℝ)]
      (fun m => deriv (deriv langevin) (inverseLangevin m) * deriv inverseLangevin m) := by
    filter_upwards [rateDomain_eventually rateDomain_zero] with m hm
    exact inverseSlope_deriv hm
  rw [he.deriv_eq]
  have hb := ((langevin_analytic (inverseLangevin 0)).deriv.deriv.differentiableAt.hasDerivAt).comp 0
      (inverseLangevin_analytic rateDomain_zero).differentiableAt.hasDerivAt
  have hd := hb.mul (inverseLangevin_analytic rateDomain_zero).deriv.differentiableAt.hasDerivAt
  change HasDerivAt
    (fun m => deriv (deriv langevin) (inverseLangevin m) * deriv inverseLangevin m) _ 0 at hd
  rw [hd.deriv, inverseLangevin_zero, langevin_second_deriv_zero, langevin_third_deriv_zero,
    inverseLangevin_hasDerivAt_zero.deriv]
  ring

theorem inverse_product_deriv {m : ℝ} (hm : m ∈ rateDomain) :
    deriv inverseSlope m * deriv inverseLangevin m +
      inverseSlope m * deriv (deriv inverseLangevin) m = 0 := by
  have hd := (inverseSlope_analytic hm).differentiableAt.hasDerivAt.mul
    (inverseLangevin_analytic hm).deriv.differentiableAt.hasDerivAt
  change HasDerivAt (fun y => inverseSlope y * deriv inverseLangevin y) _ m at hd
  have he : (fun y => inverseSlope y * deriv inverseLangevin y) =ᶠ[𝓝 m] (fun _ => (1 : ℝ)) := by
    filter_upwards [rateDomain_eventually hm] with y hy
    exact inverseLangevin_product hy
  exact (hd.congr_of_eventuallyEq he.symm).unique (hasDerivAt_const m (1 : ℝ))

theorem inverseLangevin_second_zero : deriv (deriv inverseLangevin) 0 = 0 := by
  have h := inverse_product_deriv rateDomain_zero
  rw [inverseSlope_deriv_zero, inverseSlope_zero] at h
  linarith

theorem inverseLangevin_third_zero : deriv (deriv (deriv inverseLangevin)) 0 = 54 / 5 := by
  have ha := inverseSlope_analytic rateDomain_zero
  have hi := inverseLangevin_analytic rateDomain_zero
  have hd := (ha.deriv.differentiableAt.hasDerivAt.mul hi.deriv.differentiableAt.hasDerivAt).add
    (ha.differentiableAt.hasDerivAt.mul hi.deriv.deriv.differentiableAt.hasDerivAt)
  change HasDerivAt (fun m => deriv inverseSlope m * deriv inverseLangevin m +
      inverseSlope m * deriv (deriv inverseLangevin) m) _ 0 at hd
  have he : (fun m => deriv inverseSlope m * deriv inverseLangevin m +
      inverseSlope m * deriv (deriv inverseLangevin) m) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := by
    filter_upwards [rateDomain_eventually rateDomain_zero] with m hm
    exact inverse_product_deriv hm
  have hh := (hd.congr_of_eventuallyEq he.symm).unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  rw [inverseSlope_second_zero, inverseLangevin_hasDerivAt_zero.deriv,
    inverseSlope_deriv_zero, inverseLangevin_second_zero, inverseSlope_zero] at hh
  linarith

-- Local parity of derivatives, using the open symmetric domain.
theorem rateDomain_deriv_parity (f : ℝ → ℝ) (a : ℝ)
    (he : ∀ x ∈ rateDomain, f (-x) = a * f x)
    (hf : ∀ x ∈ rateDomain, DifferentiableAt ℝ f x)
    (x : ℝ) (hx : x ∈ rateDomain) :
    deriv f (-x) = -a * deriv f x := by
  have hd := ((hf (-x) (rateDomain_neg hx)).hasDerivAt.comp x (hasDerivAt_id x).neg)
  have h' : HasDerivAt (fun y : ℝ => f (-y)) (deriv f (-x) * -1) x := by
    change HasDerivAt (fun y : ℝ => f (-y)) _ x at hd
    simpa only [smul_eq_mul, mul_neg, mul_one, neg_mul, one_mul] using hd
  have heq : (fun y : ℝ => f (-y)) =ᶠ[𝓝 x] (fun y => a * f y) := by
    filter_upwards [rateDomain_eventually hx] with y hy
    exact he y hy
  have hh := (h'.congr_of_eventuallyEq heq.symm).unique ((hf x hx).hasDerivAt.const_mul a)
  linarith

theorem inverseLangevin_fourth_zero : deriv (deriv (deriv (deriv inverseLangevin))) 0 = 0 := by
  have h1 := rateDomain_deriv_parity inverseLangevin (-1)
    (fun x hx => by rw [inverseLangevin_odd_on hx]; ring)
    (fun x hx => (inverseLangevin_analytic hx).differentiableAt)
  have h2 := rateDomain_deriv_parity (deriv inverseLangevin) 1
    (fun x hx => by simpa using h1 x hx)
    (fun x hx => (inverseLangevin_analytic hx).deriv.differentiableAt)
  have h3 := rateDomain_deriv_parity (deriv (deriv inverseLangevin)) (-1)
    (fun x hx => by simpa using h2 x hx)
    (fun x hx => (inverseLangevin_analytic hx).deriv.deriv.differentiableAt)
  have h4 := rateDomain_deriv_parity (deriv (deriv (deriv inverseLangevin))) 1
    (fun x hx => by simpa using h3 x hx)
    (fun x hx => (inverseLangevin_analytic hx).deriv.deriv.deriv.differentiableAt) 0 rateDomain_zero
  simp only [neg_zero, neg_mul, one_mul] at h4
  linarith

theorem conjugate_analytic {m : ℝ} (hm : m ∈ rateDomain) : AnalyticAt ℝ conjugate m := by
  have h : AnalyticAt ℝ (fun t : ℝ => t * inverseLangevin t - cumulant (inverseLangevin t)) m :=
    (analyticAt_id.mul (inverseLangevin_analytic hm)).sub
      ((cumulant_analytic (inverseLangevin m)).comp (inverseLangevin_analytic hm))
  apply h.congr
  filter_upwards [rateDomain_eventually hm] with t ht
  exact (conjugate_eq_inverse_on_interval t ht).symm

theorem conjugate_hasDerivAt {m : ℝ} (hm : m ∈ rateDomain) :
    HasDerivAt conjugate (inverseLangevin m) m := by
  have hk := cumulant_hasDerivAt (inverseLangevin m)
  rw [inverseLangevin_right_on_interval m hm] at hk
  have h := envelope_derivative cumulant inverseLangevin m (deriv inverseLangevin m)
    (inverseLangevin_analytic hm).differentiableAt.hasDerivAt hk
  apply h.congr_of_eventuallyEq
  filter_upwards [rateDomain_eventually hm] with t ht
  exact conjugate_eq_inverse_on_interval t ht

theorem conjugate_even_on {m : ℝ} (hm : m ∈ rateDomain) : conjugate (-m) = conjugate m := by
  rw [conjugate_eq_inverse_on_interval (-m) (rateDomain_neg hm),
    conjugate_eq_inverse_on_interval m hm, inverseLangevin_odd_on hm, cumulant_even]
  ring

theorem conjugate_zero : conjugate 0 = 0 := by
  rw [conjugate_eq_inverse_on_interval 0 rateDomain_zero, inverseLangevin_zero, cumulant_zero]
  ring

theorem conjugate_iteratedDeriv_succ_zero (n : ℕ) :
    iteratedDeriv (n+1) conjugate 0 = iteratedDeriv n inverseLangevin 0 := by
  rw [iteratedDeriv_succ']
  have he : deriv conjugate =ᶠ[𝓝 (0 : ℝ)] inverseLangevin := by
    filter_upwards [rateDomain_eventually rateDomain_zero] with t ht
    exact (conjugate_hasDerivAt ht).deriv
  have hh : ∀ k : ℕ, iteratedDeriv k (deriv conjugate) =ᶠ[𝓝 (0 : ℝ)] iteratedDeriv k inverseLangevin := by
    intro k
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using he
    | succ k ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      exact ih.deriv
  exact (hh n).eq_of_nhds

theorem rateDomain_half {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1/2)) : x ∈ rateDomain := by
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem local_taylor_deriv_eq (f : ℝ → ℝ)
    (hf : ∀ x ∈ rateDomain, AnalyticAt ℝ f x) (k : ℕ) :
    iteratedDerivWithin k f (Icc (0 : ℝ) (1/2)) 0 = iteratedDeriv k f 0 :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1/2))
    (hf 0 rateDomain_zero).contDiffAt (by norm_num)

theorem inverseLangevin_taylor_four (x : ℝ) :
    taylorWithinEval inverseLangevin 4 (Icc (0 : ℝ) (1/2)) 0 x =
      3*x + 9*x^3/5 := by
  have hd (k : ℕ) := local_taylor_deriv_eq inverseLangevin
    (fun _ hx => inverseLangevin_analytic hx) k
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hd, iteratedDeriv_succ,
    iteratedDeriv_zero, inverseLangevin_zero, inverseLangevin_hasDerivAt_zero.deriv,
    inverseLangevin_second_zero, inverseLangevin_third_zero, inverseLangevin_fourth_zero]
  norm_num [Nat.factorial, smul_eq_mul]
  <;> ring

theorem inverseLangevin_order_five_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℝ, |m| ≤ 1/2 →
      |inverseLangevin m - (3*m + 9*m^3/5)| ≤ C * |m|^5 := by
  have hf : ContDiffOn ℝ 5 inverseLangevin (Icc (0 : ℝ) (1/2)) :=
    fun x hx => (inverseLangevin_analytic (rateDomain_half hx)).contDiffAt.contDiffWithinAt
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (f := inverseLangevin)
    (n := 4) (a := 0) (b := 1/2) (by norm_num) hf
  refine ⟨max C 0, le_max_right _ _, fun m hm => ?_⟩
  have h := hC |m| ⟨abs_nonneg _, hm⟩
  rw [inverseLangevin_taylor_four, Real.norm_eq_abs, sub_zero] at h
  have h' : |inverseLangevin m - (3*m + 9*m^3/5)| ≤ C * |m|^5 := by
    rcases le_or_gt 0 m with hpos | hneg
    · simpa only [abs_of_nonneg hpos] using h
    · have hmem : m ∈ rateDomain := by
        have hh := abs_le.mp hm
        exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
      rw [abs_of_neg hneg, inverseLangevin_odd_on hmem] at h
      have he : -inverseLangevin m - (3 * -m + 9 * (-m)^3 / 5) =
          -(inverseLangevin m - (3*m + 9*m^3/5)) := by ring
      rw [he, abs_neg] at h
      simpa only [abs_of_neg hneg] using h
  exact h'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (abs_nonneg _) _))

theorem conjugate_taylor_five (x : ℝ) :
    taylorWithinEval conjugate 5 (Icc (0 : ℝ) (1/2)) 0 x =
      3*x^2/2 + 9*x^4/20 := by
  have hd (k : ℕ) := local_taylor_deriv_eq conjugate
    (fun _ hx => conjugate_analytic hx) k
  have h1 : iteratedDeriv 1 conjugate 0 = 0 := by
    simpa only [iteratedDeriv_zero, inverseLangevin_zero] using conjugate_iteratedDeriv_succ_zero 0
  have h2 : iteratedDeriv 2 conjugate 0 = 3 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, inverseLangevin_hasDerivAt_zero.deriv] using conjugate_iteratedDeriv_succ_zero 1
  have h3 : iteratedDeriv 3 conjugate 0 = 0 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, inverseLangevin_second_zero] using conjugate_iteratedDeriv_succ_zero 2
  have h4 : iteratedDeriv 4 conjugate 0 = 54/5 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, inverseLangevin_third_zero] using conjugate_iteratedDeriv_succ_zero 3
  have h5 : iteratedDeriv 5 conjugate 0 = 0 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, inverseLangevin_fourth_zero] using conjugate_iteratedDeriv_succ_zero 4
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hd, iteratedDeriv_zero,
    conjugate_zero, h1,h2,h3,h4,h5]
  norm_num [Nat.factorial, smul_eq_mul]
  <;> ring

theorem conjugate_order_six_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℝ, |m| ≤ 1/2 →
      |conjugate m - (3*m^2/2 + 9*m^4/20)| ≤ C * |m|^6 := by
  have hf : ContDiffOn ℝ 6 conjugate (Icc (0 : ℝ) (1/2)) :=
    fun x hx => (conjugate_analytic (rateDomain_half hx)).contDiffAt.contDiffWithinAt
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (f := conjugate)
    (n := 5) (a := 0) (b := 1/2) (by norm_num) hf
  refine ⟨max C 0, le_max_right _ _, fun m hm => ?_⟩
  have h := hC |m| ⟨abs_nonneg _, hm⟩
  rw [conjugate_taylor_five, Real.norm_eq_abs, sub_zero] at h
  have he : conjugate |m| = conjugate m := by
    rcases le_or_gt 0 m with hpos | hneg
    · rw [abs_of_nonneg hpos]
    · have hmem : m ∈ rateDomain := by
        have hh := abs_le.mp hm
        exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
      rw [abs_of_neg hneg, conjugate_even_on hmem]
  have h2 : |m|^2 = m^2 := by rw [← abs_pow]; exact abs_of_nonneg (sq_nonneg m)
  have h4 : |m|^4 = m^4 := by calc
    |m|^4 = (|m|^2)^2 := by ring
    _ = m^4 := by rw [h2]; ring
  rw [he,h2,h4] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (abs_nonneg _) _))

def normalizedRate (s : ℝ) : ℝ := conjugate (s / Real.sqrt 3)

theorem normalizedRate_order_six_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |s| ≤ 1/2 →
      |normalizedRate s - (s^2/2 + s^4/20)| ≤ C * |s|^6 := by
  obtain ⟨C, hC, h⟩ := conjugate_order_six_bound
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsq : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hge : 1 ≤ Real.sqrt 3 := by nlinarith
  refine ⟨C,hC,fun s hsmall => ?_⟩
  have hm : |s / Real.sqrt 3| ≤ |s| := by
    rw [abs_div, abs_of_pos hs]
    apply (div_le_iff₀ hs).2
    nlinarith [mul_nonneg (abs_nonneg s) (sub_nonneg.mpr hge)]
  have hr := h (s / Real.sqrt 3) (hm.trans hsmall)
  have hpoly : 3*(s / Real.sqrt 3)^2/2 + 9*(s / Real.sqrt 3)^4/20 =
      s^2/2 + s^4/20 := by
    field_simp [ne_of_gt hs]
    nlinarith [congrArg (fun t : ℝ => t^2) hsq]
  rw [hpoly] at hr
  exact hr.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hm 6) hC)

end
end M14.EulerianLegendre

#print axioms M14.EulerianLegendre.rateDomain_zero
#print axioms M14.EulerianLegendre.rateDomain_neg
#print axioms M14.EulerianLegendre.rateDomain_eventually
#print axioms M14.EulerianLegendre.inverseLangevin_zero
#print axioms M14.EulerianLegendre.inverseLangevin_analytic
#print axioms M14.EulerianLegendre.inverseLangevin_odd_on
#print axioms M14.EulerianLegendre.inverseLangevin_product
#print axioms M14.EulerianLegendre.inverseSlope_analytic
#print axioms M14.EulerianLegendre.inverseSlope_deriv
#print axioms M14.EulerianLegendre.inverseSlope_zero
#print axioms M14.EulerianLegendre.inverseSlope_deriv_zero
#print axioms M14.EulerianLegendre.inverseSlope_second_zero
#print axioms M14.EulerianLegendre.inverse_product_deriv
#print axioms M14.EulerianLegendre.inverseLangevin_second_zero
#print axioms M14.EulerianLegendre.inverseLangevin_third_zero
#print axioms M14.EulerianLegendre.rateDomain_deriv_parity
#print axioms M14.EulerianLegendre.inverseLangevin_fourth_zero
#print axioms M14.EulerianLegendre.conjugate_analytic
#print axioms M14.EulerianLegendre.conjugate_hasDerivAt
#print axioms M14.EulerianLegendre.conjugate_even_on
#print axioms M14.EulerianLegendre.conjugate_zero
#print axioms M14.EulerianLegendre.conjugate_iteratedDeriv_succ_zero

#print axioms M14.EulerianLegendre.rateDomain_half
#print axioms M14.EulerianLegendre.local_taylor_deriv_eq
#print axioms M14.EulerianLegendre.inverseLangevin_taylor_four
#print axioms M14.EulerianLegendre.inverseLangevin_order_five_bound
#print axioms M14.EulerianLegendre.conjugate_taylor_five
#print axioms M14.EulerianLegendre.conjugate_order_six_bound
#print axioms M14.EulerianLegendre.normalizedRate_order_six_bound
