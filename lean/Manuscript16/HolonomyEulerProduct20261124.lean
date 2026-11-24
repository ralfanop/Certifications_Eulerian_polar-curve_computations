import Mathlib
import Manuscript16.V166HolonomyPair
import Manuscript16.ReactiveHolonomyV166

/-!
# M16 v16.6 §14.5 `eq:hol-det`: Euler evaluation of the paired holonomy product

`V166HolonomyPair` (merged) defines the paired circle-spectrum factor

  `pairRatio a φ n = ((n-φ)²+a²)((-n-φ)²+a²) / (n²+a²)²`

and proves that `∑ₙ |pairRatio a φ (n+1) - 1| < ∞`. `ReactiveHolonomyV166` (merged) defines
the closed form `productClosed x c = (cosh 2x - c)/(cosh 2x - 1)` and proves scalar identities
for it. The step left open there is the evaluation of the infinite product by Euler's sine
product. This file proves it, for every `a > 0` and every real `φ`:

* `paired_product_tendsto`: the partial products `∏_{n=1}^{N} pairRatio a φ n` converge, as
  `N → ∞`, to `a² (sin²(πφ) + sinh²(πa)) / ((φ²+a²) sinh²(πa))`;
* `holonomy_det_tendsto`: multiplied by the unpaired `n = 0` factor `(φ²+a²)/a²`, they converge
  to `productClosed (π a) (cos (2πφ))`.

Input used, not re-proved: Euler's product for the complex sine,
`Complex.tendsto_euler_sin_prod` (Mathlib). The original step is the factorization
`pairRatio a φ n = |1 - z²/n²|² / (1 + a²/n²)²` with `z = φ + i a` and the evaluation of the
limit. These are statements about real scalar sequences; no operator, trace-class determinant
or uniformity in `(a, φ)` is asserted here.
-/

open Filter Topology

namespace Manuscript16.HolonomyEulerProduct20261124

open Manuscript16.V166HolonomyPair Manuscript16.ReactiveHolonomy

/-- The complex parameter `z = φ + i a` of the shifted circle spectrum. -/
noncomputable def zeta (a φ : ℝ) : ℂ := (φ : ℂ) + (a : ℂ) * Complex.I

theorem normSq_zeta (a φ : ℝ) : Complex.normSq (zeta a φ) = φ ^ 2 + a ^ 2 := by
  unfold zeta
  rw [Complex.normSq_add_mul_I]

theorem zeta_ne_zero (a φ : ℝ) (ha : a ≠ 0) : zeta a φ ≠ 0 := by
  intro h
  have h' := normSq_zeta a φ
  rw [h, map_zero] at h'
  have : 0 < a ^ 2 := by positivity
  nlinarith [sq_nonneg φ]

/-- `|1 - z²/m²|² = ((m-φ)²+a²)((m+φ)²+a²)/m⁴` for real `m ≠ 0`. -/
theorem normSq_factor (a φ m : ℝ) (hm : m ≠ 0) :
    Complex.normSq (1 - zeta a φ ^ 2 / (m : ℂ) ^ 2) =
      ((m - φ) ^ 2 + a ^ 2) * ((m + φ) ^ 2 + a ^ 2) / m ^ 4 := by
  have hmc : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm
  have h1 : (1 : ℂ) - zeta a φ ^ 2 / (m : ℂ) ^ 2 =
      ((m : ℂ) - zeta a φ) * ((m : ℂ) + zeta a φ) / (m : ℂ) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hmc), sub_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hmc)]
    ring
  have h2 : (m : ℂ) - zeta a φ = ((m - φ : ℝ) : ℂ) + ((-a : ℝ) : ℂ) * Complex.I := by
    unfold zeta
    push_cast
    ring
  have h3 : (m : ℂ) + zeta a φ = ((m + φ : ℝ) : ℂ) + ((a : ℝ) : ℂ) * Complex.I := by
    unfold zeta
    push_cast
    ring
  rw [h1, map_div₀, map_mul, h2, h3, Complex.normSq_add_mul_I, Complex.normSq_add_mul_I,
    map_pow, Complex.normSq_ofReal]
  ring

/-- The paired factor is `|1 - z²/m²|² / (1 + a²/m²)²`. -/
theorem pairRatio_eq_normSq (a φ m : ℝ) (hm : m ≠ 0) :
    pairRatio a φ m =
      Complex.normSq (1 - zeta a φ ^ 2 / (m : ℂ) ^ 2) / (1 + a ^ 2 / m ^ 2) ^ 2 := by
  rw [normSq_factor a φ m hm]
  have hm2 : 0 < m ^ 2 := by positivity
  have hd : m ^ 2 + a ^ 2 ≠ 0 := by nlinarith [sq_nonneg a]
  unfold pairRatio
  field_simp
  ring

/-- Finite paired products as a quotient of a squared complex modulus and a real square. -/
theorem pairProduct_eq (a φ : ℝ) (N : ℕ) :
    ∏ j ∈ Finset.range N, pairRatio a φ ((j : ℝ) + 1) =
      Complex.normSq (∏ j ∈ Finset.range N, (1 - zeta a φ ^ 2 / ((j : ℂ) + 1) ^ 2)) /
        (∏ j ∈ Finset.range N, (1 + a ^ 2 / ((j : ℝ) + 1) ^ 2)) ^ 2 := by
  rw [map_prod, ← Finset.prod_pow, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
  rw [pairRatio_eq_normSq a φ _ hj]
  push_cast
  rfl

/-- Euler's product, divided by `π z`. -/
theorem sine_factor_tendsto (z : ℂ) (hz : z ≠ 0) :
    Tendsto (fun N : ℕ => ∏ j ∈ Finset.range N, (1 - z ^ 2 / ((j : ℂ) + 1) ^ 2)) atTop
      (𝓝 (Complex.sin (Real.pi * z) / (Real.pi * z))) := by
  have hpz : (Real.pi : ℂ) * z ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hz
  refine ((Complex.tendsto_euler_sin_prod z).div_const ((Real.pi : ℂ) * z)).congr (fun N => ?_)
  exact mul_div_cancel_left₀ _ hpz

/-- Euler's product at `z = i a`: `∏ (1 + a²/n²) → sinh(πa)/(πa)`. -/
theorem sinh_factor_tendsto (a : ℝ) (ha : a ≠ 0) :
    Tendsto (fun N : ℕ => ∏ j ∈ Finset.range N, (1 + a ^ 2 / ((j : ℝ) + 1) ^ 2)) atTop
      (𝓝 (Real.sinh (Real.pi * a) / (Real.pi * a))) := by
  have hz : (a : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr ha) Complex.I_ne_zero
  have h := (Complex.continuous_re.tendsto _).comp (sine_factor_tendsto _ hz)
  have hprod : ∀ N : ℕ, ∏ j ∈ Finset.range N, (1 - ((a : ℂ) * Complex.I) ^ 2 / ((j : ℂ) + 1) ^ 2) =
      ((∏ j ∈ Finset.range N, (1 + a ^ 2 / ((j : ℝ) + 1) ^ 2) : ℝ) : ℂ) := by
    intro N
    push_cast
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [mul_pow, Complex.I_sq]
    ring
  have hlim : Complex.sin (Real.pi * ((a : ℂ) * Complex.I)) / (Real.pi * ((a : ℂ) * Complex.I)) =
      ((Real.sinh (Real.pi * a) / (Real.pi * a) : ℝ) : ℂ) := by
    rw [show (Real.pi : ℂ) * ((a : ℂ) * Complex.I) = ((Real.pi * a : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.sin_mul_I, ← Complex.ofReal_sinh,
      mul_div_mul_right _ _ Complex.I_ne_zero, ← Complex.ofReal_div]
  rw [hlim, Complex.ofReal_re] at h
  refine h.congr (fun N => ?_)
  simp only [Function.comp_apply]
  rw [hprod N, Complex.ofReal_re]

/-- `|sin(π(φ + i a))|² = sin²(πφ) + sinh²(πa)`. -/
theorem normSq_sin_pi_zeta (a φ : ℝ) :
    Complex.normSq (Complex.sin (Real.pi * zeta a φ)) =
      Real.sin (Real.pi * φ) ^ 2 + Real.sinh (Real.pi * a) ^ 2 := by
  have hz : (Real.pi : ℂ) * zeta a φ =
      ((Real.pi * φ : ℝ) : ℂ) + ((Real.pi * a : ℝ) : ℂ) * Complex.I := by
    unfold zeta
    push_cast
    ring
  rw [hz, Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  rw [show ((Real.sin (Real.pi * φ) : ℝ) : ℂ) * ((Real.cosh (Real.pi * a) : ℝ) : ℂ) +
      ((Real.cos (Real.pi * φ) : ℝ) : ℂ) * ((Real.sinh (Real.pi * a) : ℝ) : ℂ) * Complex.I =
      ((Real.sin (Real.pi * φ) * Real.cosh (Real.pi * a) : ℝ) : ℂ) +
      ((Real.cos (Real.pi * φ) * Real.sinh (Real.pi * a) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.normSq_add_mul_I]
  have hc := Real.cosh_sq (Real.pi * a)
  have hs := Real.cos_sq' (Real.pi * φ)
  calc (Real.sin (Real.pi * φ) * Real.cosh (Real.pi * a)) ^ 2 +
        (Real.cos (Real.pi * φ) * Real.sinh (Real.pi * a)) ^ 2
      = Real.sin (Real.pi * φ) ^ 2 * Real.cosh (Real.pi * a) ^ 2 +
          Real.cos (Real.pi * φ) ^ 2 * Real.sinh (Real.pi * a) ^ 2 := by ring
    _ = Real.sin (Real.pi * φ) ^ 2 + Real.sinh (Real.pi * a) ^ 2 := by rw [hc, hs]; ring

/-- **Euler evaluation of the paired product.** For `a > 0` and real `φ`,
`∏_{n=1}^{N} pairRatio a φ n → a² (sin²(πφ) + sinh²(πa)) / ((φ²+a²) sinh²(πa))`. -/
theorem paired_product_tendsto (a φ : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => ∏ j ∈ Finset.range N, pairRatio a φ ((j : ℝ) + 1)) atTop
      (𝓝 (a ^ 2 * (Real.sin (Real.pi * φ) ^ 2 + Real.sinh (Real.pi * a) ^ 2) /
        ((φ ^ 2 + a ^ 2) * Real.sinh (Real.pi * a) ^ 2))) := by
  have hz := zeta_ne_zero a φ ha.ne'
  have hsinh : 0 < Real.sinh (Real.pi * a) := Real.sinh_pos_iff.mpr (by positivity)
  have hpa : 0 < Real.pi * a := by positivity
  have hn := (Complex.continuous_normSq.tendsto _).comp (sine_factor_tendsto _ hz)
  have hh := (sinh_factor_tendsto a ha.ne').pow 2
  have hq := hn.div hh (by positivity)
  have hval : Complex.normSq (Complex.sin (Real.pi * zeta a φ) / (Real.pi * zeta a φ)) /
      (Real.sinh (Real.pi * a) / (Real.pi * a)) ^ 2 =
      a ^ 2 * (Real.sin (Real.pi * φ) ^ 2 + Real.sinh (Real.pi * a) ^ 2) /
        ((φ ^ 2 + a ^ 2) * Real.sinh (Real.pi * a) ^ 2) := by
    rw [map_div₀, map_mul, normSq_sin_pi_zeta, normSq_zeta, Complex.normSq_ofReal]
    have hφa : 0 < φ ^ 2 + a ^ 2 := by positivity
    field_simp
  rw [hval] at hq
  exact hq.congr (fun N => (pairProduct_eq a φ N).symm)

/-- `productClosed (πa) (cos 2πφ) = (sin²(πφ) + sinh²(πa)) / sinh²(πa)`. -/
theorem productClosed_eq (a φ : ℝ) (ha : 0 < a) :
    productClosed (Real.pi * a) (Real.cos (2 * Real.pi * φ)) =
      (Real.sin (Real.pi * φ) ^ 2 + Real.sinh (Real.pi * a) ^ 2) / Real.sinh (Real.pi * a) ^ 2 := by
  have hsinh : 0 < Real.sinh (Real.pi * a) := Real.sinh_pos_iff.mpr (by positivity)
  unfold productClosed
  rw [show 2 * Real.pi * φ = 2 * (Real.pi * φ) by ring, Real.cosh_two_mul, Real.cos_two_mul,
    Real.cosh_sq, Real.cos_sq']
  have hden : Real.sinh (Real.pi * a) ^ 2 + 1 + Real.sinh (Real.pi * a) ^ 2 - 1 =
      2 * Real.sinh (Real.pi * a) ^ 2 := by ring
  rw [hden]
  field_simp
  ring

/-- **`eq:hol-det`, scalar form.** With the unpaired factor `(φ²+a²)/a²` of `n = 0`, the
symmetric partial products converge to `productClosed (πa) (cos 2πφ)
= (cosh 2πa - cos 2πφ)/(cosh 2πa - 1)`. -/
theorem holonomy_det_tendsto (a φ : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => (φ ^ 2 + a ^ 2) / a ^ 2 *
        ∏ j ∈ Finset.range N, pairRatio a φ ((j : ℝ) + 1)) atTop
      (𝓝 (productClosed (Real.pi * a) (Real.cos (2 * Real.pi * φ)))) := by
  have h := (paired_product_tendsto a φ ha).const_mul ((φ ^ 2 + a ^ 2) / a ^ 2)
  have hsinh : 0 < Real.sinh (Real.pi * a) := Real.sinh_pos_iff.mpr (by positivity)
  have hφa : 0 < φ ^ 2 + a ^ 2 := by positivity
  rw [productClosed_eq a φ ha]
  convert h using 2
  field_simp

/-- The limit is at least `1`, with equality exactly when `sin(πφ) = 0`. -/
theorem holonomy_det_limit_ge_one (a φ : ℝ) (ha : 0 < a) :
    1 ≤ productClosed (Real.pi * a) (Real.cos (2 * Real.pi * φ)) ∧
      (productClosed (Real.pi * a) (Real.cos (2 * Real.pi * φ)) = 1 ↔
        Real.sin (Real.pi * φ) = 0) := by
  have hsinh : 0 < Real.sinh (Real.pi * a) := Real.sinh_pos_iff.mpr (by positivity)
  have hs2 : 0 < Real.sinh (Real.pi * a) ^ 2 := by positivity
  rw [productClosed_eq a φ ha]
  constructor
  · rw [le_div_iff₀ hs2]
    nlinarith [sq_nonneg (Real.sin (Real.pi * φ))]
  · rw [div_eq_one_iff_eq hs2.ne']
    constructor
    · intro h
      have : Real.sin (Real.pi * φ) ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    · intro h
      rw [h]
      ring

end Manuscript16.HolonomyEulerProduct20261124

#print axioms Manuscript16.HolonomyEulerProduct20261124.normSq_zeta
#print axioms Manuscript16.HolonomyEulerProduct20261124.zeta_ne_zero
#print axioms Manuscript16.HolonomyEulerProduct20261124.normSq_factor
#print axioms Manuscript16.HolonomyEulerProduct20261124.pairRatio_eq_normSq
#print axioms Manuscript16.HolonomyEulerProduct20261124.pairProduct_eq
#print axioms Manuscript16.HolonomyEulerProduct20261124.sine_factor_tendsto
#print axioms Manuscript16.HolonomyEulerProduct20261124.sinh_factor_tendsto
#print axioms Manuscript16.HolonomyEulerProduct20261124.normSq_sin_pi_zeta
#print axioms Manuscript16.HolonomyEulerProduct20261124.paired_product_tendsto
#print axioms Manuscript16.HolonomyEulerProduct20261124.productClosed_eq
#print axioms Manuscript16.HolonomyEulerProduct20261124.holonomy_det_tendsto
#print axioms Manuscript16.HolonomyEulerProduct20261124.holonomy_det_limit_ge_one
