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
