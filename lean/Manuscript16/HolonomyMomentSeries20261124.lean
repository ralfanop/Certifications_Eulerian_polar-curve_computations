import Mathlib
import Manuscript16.ReactiveHolonomyV166
import Manuscript16.HolonomyEulerProduct20261124

/-!
# M16 v16.6 §14.5 `cor:hol-eulerian`: the evanescent moment series over the circle spectrum

`ReactiveHolonomyV166` (merged) proves, for one positive spectral value `b`, the actual
Lebesgue integral `∫₀^∞ z e^{-2√b z} dz = 1/(4b)` (`evanescent_scalar_moment`), and defines the
closed form `momentClosed a x c = (π/(4a)) sinh(2x)/(cosh(2x) - c)` with scalar identities for it,
without connecting it to a sum over the spectrum. This file makes that connection for the shifted
circle spectrum `b_n = (n - φ)² + a²`, `n ∈ ℤ`, for every `a > 0` and every real `φ`:

* `circle_resolvent_hasSum`: `∑_{n∈ℤ} 1/((n-φ)²+a²) = (π/a) sinh(2πa)/(cosh 2πa - cos 2πφ)`;
* `moment_series_hasSum`: `∑_{n∈ℤ} 1/(4 b_n) = momentClosed a (πa) (cos 2πφ)`;
* `evanescent_moment_hasSum`: `∑_{n∈ℤ} ∫₀^∞ z e^{-2√b_n z} dz = momentClosed a (πa) (cos 2πφ)`;
* `evanescent_trace_integral` (interchange of sum and integral):
  `∫₀^∞ ∑_{n∈ℤ} z e^{-2√b_n z} dz = momentClosed a (πa) (cos 2πφ)`;
* `half_phase_moment_ratio`, `half_phase_moment_ratio_mul_det_limit`: at the half phase the
  moment ratio is `tanh²(πa)`, the reciprocal of the limit of the holonomy product of #596.

Inputs used, not re-proved: the Mittag-Leffler expansion of the cotangent,
`cot_series_rep'` and `summable_cotTerm` (Mathlib); the interchange theorem
`MeasureTheory.integral_tsum_of_summable_integral_norm` (Mathlib). The sums are `HasSum`
statements for the actual real series indexed by `ℤ`. No operator, spectral theorem, trace-class
membership or operator trace is asserted: `b_n` is used as an explicit real sequence.
-/

open Filter Topology MeasureTheory Set

namespace Manuscript16.HolonomyMomentSeries20261124

open Manuscript16.ReactiveHolonomy Manuscript16.HolonomyEulerProduct20261124
open Manuscript16.V166HolonomyPair

/-- The shifted circle spectrum `b_n = (n - φ)² + a²`, `n ∈ ℤ`. -/
noncomputable def circleEig (a φ : ℝ) (n : ℤ) : ℝ := ((n : ℝ) - φ) ^ 2 + a ^ 2

theorem circleEig_pos (a φ : ℝ) (ha : 0 < a) (n : ℤ) : 0 < circleEig a φ n := by
  unfold circleEig
  positivity

/-- The closed form `(π/a) sinh(2πa)/(cosh 2πa - cos 2πφ)`. -/
noncomputable def resolventClosed (a φ : ℝ) : ℝ :=
  Real.pi / a * (Real.sinh (2 * Real.pi * a) /
    (Real.cosh (2 * Real.pi * a) - Real.cos (2 * Real.pi * φ)))

/-- `Im (1/(z - m)) = -a/((m-φ)²+a²)` for `z = φ + i a` and real `m`. -/
theorem im_one_div_zeta_sub (a φ m : ℝ) :
    (1 / (zeta a φ - (m : ℂ))).im = -a / ((m - φ) ^ 2 + a ^ 2) := by
  have h : zeta a φ - (m : ℂ) = ((φ - m : ℝ) : ℂ) + (a : ℂ) * Complex.I := by
    unfold zeta
    push_cast
    ring
  rw [one_div, Complex.inv_im, h, Complex.normSq_add_mul_I]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
  rw [show (φ - m) ^ 2 = (m - φ) ^ 2 by ring, neg_div]

/-- The imaginary part of the Mittag-Leffler term at `z = φ + i a` is the paired spectral term. -/
theorem cotTerm_im (a φ : ℝ) (n : ℕ) :
    (cotTerm (zeta a φ) n).im =
      -a * (1 / circleEig a φ ((n : ℤ) + 1) + 1 / circleEig a φ (-((n : ℤ) + 1))) := by
  have h1 : zeta a φ - ((n : ℂ) + 1) = zeta a φ - (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  have h2 : zeta a φ + ((n : ℂ) + 1) = zeta a φ - ((-((n : ℝ) + 1) : ℝ) : ℂ) := by
    push_cast
    ring
  simp only [cotTerm]
  rw [Complex.add_im, h1, h2, im_one_div_zeta_sub, im_one_div_zeta_sub]
  unfold circleEig
  push_cast
  ring

/-- `Im cot(π(φ + i a)) = -sinh(2πa)/(cosh 2πa - cos 2πφ)` for `a > 0`. -/
theorem im_cot_pi_zeta (a φ : ℝ) (ha : 0 < a) :
    (Complex.cot (Real.pi * zeta a φ)).im =
      -(Real.sinh (2 * Real.pi * a) /
        (Real.cosh (2 * Real.pi * a) - Real.cos (2 * Real.pi * φ))) := by
  have hz : (Real.pi : ℂ) * zeta a φ =
      ((Real.pi * φ : ℝ) : ℂ) + ((Real.pi * a : ℝ) : ℂ) * Complex.I := by
    unfold zeta
    push_cast
    ring
  have hv : 0 < Real.pi * a := by positivity
  have hsv : 0 < Real.sinh (Real.pi * a) := Real.sinh_pos_iff.mpr hv
  rw [Complex.cot_eq_cos_div_sin, hz, Complex.cos_add_mul_I, Complex.sin_add_mul_I,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  rw [Complex.div_im]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  rw [show 2 * Real.pi * a = 2 * (Real.pi * a) by ring,
    show 2 * Real.pi * φ = 2 * (Real.pi * φ) by ring,
    Real.sinh_two_mul, Real.cosh_two_mul, Real.cos_two_mul]
  set u := Real.pi * φ
  set v := Real.pi * a
  have hc : Real.cosh v ^ 2 = Real.sinh v ^ 2 + 1 := Real.cosh_sq v
  have hs : Real.sin u ^ 2 + Real.cos u ^ 2 = 1 := Real.sin_sq_add_cos_sq u
  simp only [mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one, zero_sub]
  have hD : Real.sin u * Real.cosh v * (Real.sin u * Real.cosh v) +
      Real.cos u * Real.sinh v * (Real.cos u * Real.sinh v) =
      Real.sin u ^ 2 + Real.sinh v ^ 2 := by
    linear_combination (Real.sin u ^ 2) * hc + (Real.sinh v ^ 2) * hs
  have hE : Real.cosh v ^ 2 + Real.sinh v ^ 2 - (2 * Real.cos u ^ 2 - 1) =
      2 * (Real.sin u ^ 2 + Real.sinh v ^ 2) := by
    linear_combination hc - 2 * hs
  have hpos : 0 < Real.sin u ^ 2 + Real.sinh v ^ 2 := by positivity
  have hnum : -(Real.sin u * Real.sinh v) * (Real.sin u * Real.cosh v) -
      Real.cos u * Real.cosh v * (Real.cos u * Real.sinh v) = -(Real.sinh v * Real.cosh v) := by
    linear_combination (-(Real.sinh v * Real.cosh v)) * hs
  rw [hD, hE, div_sub_div_same, hnum]
  field_simp

/-- `z = φ + i a` lies off the integers for `a > 0`. -/
theorem zeta_mem_integerComplement (a φ : ℝ) (ha : 0 < a) :
    zeta a φ ∈ Complex.integerComplement := by
  have him : 0 < (zeta a φ).im := by simp [zeta, ha]
  exact UpperHalfPlane.coe_mem_integerComplement ⟨zeta a φ, him⟩

/-- **Spectral resolvent sum over the shifted circle spectrum.** For `a > 0` and real `φ`,
`∑_{n∈ℤ} 1/((n-φ)²+a²) = (π/a) sinh(2πa)/(cosh 2πa - cos 2πφ)`. -/
theorem circle_resolvent_hasSum (a φ : ℝ) (ha : 0 < a) :
    HasSum (fun n : ℤ => 1 / circleEig a φ n) (resolventClosed a φ) := by
  have hmem := zeta_mem_integerComplement a φ ha
  have hc : HasSum (fun n : ℕ => cotTerm (zeta a φ) n)
      ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * zeta a φ) - 1 / zeta a φ) := by
    have h := (summable_cotTerm hmem).hasSum
    rwa [show (∑' n : ℕ, cotTerm (zeta a φ) n) =
      (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * zeta a φ) - 1 / zeta a φ from
        (cot_series_rep' hmem).symm] at h
  have him := Complex.hasSum_im hc
  have hpair : HasSum (fun n : ℕ => 1 / circleEig a φ ((n : ℤ) + 1) +
      1 / circleEig a φ (-((n : ℤ) + 1)))
      (-(((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * zeta a φ) - 1 / zeta a φ).im) / a) := by
    have h := him.div_const (-a)
    refine h.congr_fun ?_ |>.trans_eq ?_
    · intro n
      rw [cotTerm_im]
      field_simp
    · rw [div_neg, neg_div]
  set f : ℤ → ℝ := fun n => 1 / circleEig a φ n with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => (one_div_pos.mpr (circleEig_pos a φ ha n)).le
  have hs1 : Summable (fun n : ℕ => f ((n : ℤ) + 1)) :=
    Summable.of_nonneg_of_le (fun n => hf0 _)
      (fun n => le_add_of_nonneg_right (hf0 (-((n : ℤ) + 1)))) hpair.summable
  have hs2 : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    Summable.of_nonneg_of_le (fun n => hf0 _)
      (fun n => le_add_of_nonneg_left (hf0 ((n : ℤ) + 1))) hpair.summable
  have hZ := HasSum.of_add_one_of_neg_add_one hs1.hasSum hs2.hasSum
  convert hZ using 1
  have hsplit : (∑' n : ℕ, f ((n : ℤ) + 1)) + ∑' n : ℕ, f (-((n : ℤ) + 1)) =
      -(((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * zeta a φ) - 1 / zeta a φ).im) / a := by
    rw [← hs1.tsum_add hs2]
    exact hpair.tsum_eq
  have hval : f 0 = 1 / (φ ^ 2 + a ^ 2) := by
    simp only [hf, circleEig, Int.cast_zero, zero_sub, neg_sq]
  have hinv : (1 / zeta a φ).im = -a / (φ ^ 2 + a ^ 2) := by
    have h := im_one_div_zeta_sub a φ 0
    simp only [Complex.ofReal_zero, sub_zero, zero_sub, neg_sq] at h
    exact h
  rw [show (∑' n : ℕ, f ((n : ℤ) + 1)) + f 0 + ∑' n : ℕ, f (-((n : ℤ) + 1)) =
      ((∑' n : ℕ, f ((n : ℤ) + 1)) + ∑' n : ℕ, f (-((n : ℤ) + 1))) + f 0 by ring,
    hsplit, hval, Complex.sub_im, Complex.im_ofReal_mul, hinv, im_cot_pi_zeta a φ ha]
  unfold resolventClosed
  have hφa : 0 < φ ^ 2 + a ^ 2 := by positivity
  field_simp
  ring

/-- **Spectral moment series.** `∑_{n∈ℤ} 1/(4 b_n) = momentClosed a (πa) (cos 2πφ)`. -/
theorem moment_series_hasSum (a φ : ℝ) (ha : 0 < a) :
    HasSum (fun n : ℤ => 1 / (4 * circleEig a φ n))
      (momentClosed a (Real.pi * a) (Real.cos (2 * Real.pi * φ))) := by
  have h := (circle_resolvent_hasSum a φ ha).div_const 4
  refine h.congr_fun ?_ |>.trans_eq ?_
  · intro n
    rw [div_div, mul_comm]
  · unfold resolventClosed momentClosed
    rw [show 2 * (Real.pi * a) = 2 * Real.pi * a by ring]
    ring_nf

/-- **Evanescent moments summed over the circle spectrum.**
`∑_{n∈ℤ} ∫₀^∞ z e^{-2√b_n z} dz = momentClosed a (πa) (cos 2πφ)`. -/
theorem evanescent_moment_hasSum (a φ : ℝ) (ha : 0 < a) :
    HasSum (fun n : ℤ => ∫ z : ℝ in Ioi 0,
        z * Real.exp (-(2 * Real.sqrt (circleEig a φ n) * z)))
      (momentClosed a (Real.pi * a) (Real.cos (2 * Real.pi * φ))) := by
  refine (moment_series_hasSum a φ ha).congr_fun ?_
  intro n
  rw [evanescent_scalar_moment _ (circleEig_pos a φ ha n)]

/-- **Interchange of sum and integral (trace form).**
`∫₀^∞ ∑_{n∈ℤ} z e^{-2√b_n z} dz = momentClosed a (πa) (cos 2πφ)`. -/
theorem evanescent_trace_integral (a φ : ℝ) (ha : 0 < a) :
    (∫ z : ℝ in Ioi 0, ∑' n : ℤ, z * Real.exp (-(2 * Real.sqrt (circleEig a φ n) * z))) =
      momentClosed a (Real.pi * a) (Real.cos (2 * Real.pi * φ)) := by
  have hint : ∀ n : ℤ, Integrable
      (fun z : ℝ => z * Real.exp (-(2 * Real.sqrt (circleEig a φ n) * z)))
      (volume.restrict (Ioi 0)) := by
    intro n
    apply Integrable.of_integral_ne_zero
    rw [evanescent_scalar_moment _ (circleEig_pos a φ ha n)]
    have := circleEig_pos a φ ha n
    positivity
  have hnorm : ∀ n : ℤ, (∫ z : ℝ in Ioi 0,
      ‖z * Real.exp (-(2 * Real.sqrt (circleEig a φ n) * z))‖) =
      ∫ z : ℝ in Ioi 0, z * Real.exp (-(2 * Real.sqrt (circleEig a φ n) * z)) := by
    intro n
    refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    exact Real.norm_of_nonneg (mul_nonneg (le_of_lt hz) (Real.exp_pos _).le)
  have hsum : Summable (fun n : ℤ => ∫ z : ℝ in Ioi 0,
      ‖z * Real.exp (-(2 * Real.sqrt (circleEig a φ n) * z))‖) := by
    simp only [hnorm]
    exact (evanescent_moment_hasSum a φ ha).summable
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  exact (evanescent_moment_hasSum a φ ha).tsum_eq

/-- **Half phase.** The ratio of the moment series at `φ = 1/2` and `φ = 0` is `tanh²(πa)`. -/
theorem half_phase_moment_ratio (a : ℝ) (ha : 0 < a) :
    (∑' n : ℤ, 1 / (4 * circleEig a (1 / 2) n)) / (∑' n : ℤ, 1 / (4 * circleEig a 0 n)) =
      Real.tanh (Real.pi * a) ^ 2 := by
  rw [(moment_series_hasSum a (1 / 2) ha).tsum_eq, (moment_series_hasSum a 0 ha).tsum_eq,
    half_phase_cos, show 2 * Real.pi * (0 : ℝ) = 0 by ring, Real.cos_zero]
  exact half_moment_ratio a (Real.pi * a) ha (by positivity)

/-- **Half phase, moments and product.** The moment ratio times the limit of the holonomy
product with its `n = 0` factor (#596, `holonomy_det_tendsto`) at `φ = 1/2` equals `1`. -/
theorem half_phase_moment_ratio_mul_det_limit (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ =>
        (∑' n : ℤ, 1 / (4 * circleEig a (1 / 2) n)) / (∑' n : ℤ, 1 / (4 * circleEig a 0 n)) *
          (((1 / 2 : ℝ) ^ 2 + a ^ 2) / a ^ 2 *
            ∏ j ∈ Finset.range N, pairRatio a (1 / 2) ((j : ℝ) + 1))) atTop (𝓝 1) := by
  have hx : 0 < Real.pi * a := by positivity
  have h := (holonomy_det_tendsto a (1 / 2) ha).const_mul (Real.tanh (Real.pi * a) ^ 2)
  rw [half_phase_cos] at h
  have hone : Real.tanh (Real.pi * a) ^ 2 * productClosed (Real.pi * a) (-1) = 1 := by
    have hr := half_product_reciprocal (Real.pi * a) hx
    have hpos : productClosed (Real.pi * a) (-1) ≠ 0 := by
      intro h0
      rw [h0, div_zero] at hr
      have := (half_ratio_strict (Real.pi * a) hx).1
      linarith
    rw [← hr]
    field_simp
  rw [hone] at h
  rw [half_phase_moment_ratio a ha]
  exact h

end Manuscript16.HolonomyMomentSeries20261124

#print axioms Manuscript16.HolonomyMomentSeries20261124.circleEig_pos
#print axioms Manuscript16.HolonomyMomentSeries20261124.im_one_div_zeta_sub
#print axioms Manuscript16.HolonomyMomentSeries20261124.cotTerm_im
#print axioms Manuscript16.HolonomyMomentSeries20261124.im_cot_pi_zeta
#print axioms Manuscript16.HolonomyMomentSeries20261124.zeta_mem_integerComplement
#print axioms Manuscript16.HolonomyMomentSeries20261124.circle_resolvent_hasSum
#print axioms Manuscript16.HolonomyMomentSeries20261124.moment_series_hasSum
#print axioms Manuscript16.HolonomyMomentSeries20261124.evanescent_moment_hasSum
#print axioms Manuscript16.HolonomyMomentSeries20261124.evanescent_trace_integral
#print axioms Manuscript16.HolonomyMomentSeries20261124.half_phase_moment_ratio
#print axioms Manuscript16.HolonomyMomentSeries20261124.half_phase_moment_ratio_mul_det_limit
