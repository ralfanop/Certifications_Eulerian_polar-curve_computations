import Mathlib

/-! # Manuscript 12, proof of Theorem 5.14: the constant-bond identity (162)

For the constant bilateral bond sequence `b`, the Jacobi operator has Fourier multiplier
`2b cos θ`, so `[f(J(b·1))]_{k,k-1} = (1/2π) ∫_{-π}^{π} f(2b cos θ) cos θ dθ` (classical
diagonalisation of the Laurent operator, a published result cited). For an odd continuous
`f`, this integral equals `Φ_f(2b)/b`, where `Φ_f(a) = (1/π) ∫_0^{π/2} a sin θ f(a sin θ) dθ`
(`constant_bond_integral`). With `f = I'` on `[-2b, 2b]`, `Φ_f(2b) = Φ(2b)`, and for
`2b = ξ_{k/M}` the definition `Φ(ξ_α) = α` gives `k/(M b)`, which is (162). -/

namespace UniformLanczos.Rate514Constant

open intervalIntegral Real

/-- `Φ_f(a) = (1/π) ∫_0^{π/2} a sin θ f(a sin θ) dθ`, the functional of (ul-Phi). -/
noncomputable def PhiF (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  (1 / π) * ∫ θ in (0:ℝ)..(π / 2), a * sin θ * f (a * sin θ)

theorem constant_bond_integral (f : ℝ → ℝ) (hf : Continuous f) (hodd : ∀ y, f (-y) = -f y)
    {b : ℝ} (hb : 0 < b) :
    (1 / (2 * π)) * ∫ θ in (-π)..π, f (2 * b * cos θ) * cos θ = PhiF f (2 * b) / b := by
  set g : ℝ → ℝ := fun θ => f (2 * b * cos θ) * cos θ
  have hg : Continuous g := (hf.comp (continuous_const.mul continuous_cos)).mul continuous_cos
  have hii : ∀ x y : ℝ, IntervalIntegrable g MeasureTheory.volume x y :=
    fun x y => hg.intervalIntegrable x y
  -- evenness: `∫_{-π}^0 g = ∫_0^π g`
  have heven : ∫ θ in (-π)..0, g θ = ∫ θ in (0:ℝ)..π, g θ := by
    have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := π) g
    simp only [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [g, cos_neg]
  -- reflection `θ ↦ π - θ`: `∫_{π/2}^π g = ∫_0^{π/2} g`, since `f` is odd
  have hrefl : ∫ θ in (π / 2)..π, g θ = ∫ θ in (0:ℝ)..(π / 2), g θ := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := π / 2) g π
    rw [show π - π / 2 = π / 2 by ring, sub_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [g, cos_pi_sub, mul_neg, hodd]
    ring
  -- `θ ↦ π/2 - θ` on `[0, π/2]` turns `cos` into `sin`
  have hsin : ∫ θ in (0:ℝ)..(π / 2), g θ = ∫ θ in (0:ℝ)..(π / 2), f (2 * b * sin θ) * sin θ := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := π / 2) g (π / 2)
    rw [sub_self, sub_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [g, cos_pi_div_two_sub]
  have hfull : ∫ θ in (-π)..π, g θ = 4 * ∫ θ in (0:ℝ)..(π / 2), g θ := by
    have h1 : ∫ θ in (-π)..π, g θ = (∫ θ in (-π)..0, g θ) + ∫ θ in (0:ℝ)..π, g θ :=
      (intervalIntegral.integral_add_adjacent_intervals (hii (-π) 0) (hii 0 π)).symm
    have h2 : ∫ θ in (0:ℝ)..π, g θ = (∫ θ in (0:ℝ)..(π / 2), g θ) + ∫ θ in (π / 2)..π, g θ :=
      (intervalIntegral.integral_add_adjacent_intervals (hii 0 (π / 2)) (hii (π / 2) π)).symm
    rw [h1, heven, h2, hrefl]
    ring
  have hPhi : PhiF f (2 * b) = (2 * b) / π * ∫ θ in (0:ℝ)..(π / 2), f (2 * b * sin θ) * sin θ := by
    unfold PhiF
    have hI : ∫ θ in (0:ℝ)..(π / 2), 2 * b * sin θ * f (2 * b * sin θ) =
        2 * b * ∫ θ in (0:ℝ)..(π / 2), f (2 * b * sin θ) * sin θ := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext θ; ring
    rw [hI]; ring
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hb0 : b ≠ 0 := hb.ne'
  show (1 / (2 * π)) * ∫ θ in (-π)..π, g θ = PhiF f (2 * b) / b
  rw [hfull, hsin, hPhi]
  field_simp
  ring

/-- **(162).** If moreover `Φ_f(2b) = k/M` (for `f = I'` near `[-2b, 2b]` and `2b = ξ_{k/M}`,
this is the definition of `ξ`), the constant-bond entry equals `k/(M b)`. -/
theorem constant_bond_entry (f : ℝ → ℝ) (hf : Continuous f) (hodd : ∀ y, f (-y) = -f y)
    {b k M : ℝ} (hb : 0 < b) (hPhi : PhiF f (2 * b) = k / M) :
    (1 / (2 * π)) * ∫ θ in (-π)..π, f (2 * b * cos θ) * cos θ = k / (M * b) := by
  rw [constant_bond_integral f hf hodd hb, hPhi, div_div]

end UniformLanczos.Rate514Constant

#print axioms UniformLanczos.Rate514Constant.constant_bond_integral
#print axioms UniformLanczos.Rate514Constant.constant_bond_entry
