/-
Uniform Lanczos note, Corollary (small-α expansion of the limit profile), formalised
conditionally on the expansion of `I'` at the origin.

With `Hint` from `Endpoint.lean` and `H(a) = Hint (x ↦ x I'(x)) a`:
* `integral_sin_four_half_pi` : `∫₀^{π/2} sin⁴ = 3π/16`;
* `Hint_expansion` : if `|I'(x) - 12x - (144/5)x³| ≤ C x⁵` on `[0,b]` then
  `|H(a) - 3a² - (27/5)a⁴| ≤ C a⁶/2` on `[0,b]`;
* `inversion` : if `α = 3A + (27/5)A² + r`, `|r| ≤ C A³`, `0 ≤ A ≤ 1`, then
  `|A/4 - (α/12 - α²/20)| ≤ K A³` with explicit `K`; with `A = a²`, `F(α) = a²/4`, this is
  `F(α) = α/12 - α²/20 + O(α³)` (and `A ≤ α/2` for small `A`, see `A_le_half_alpha`).
The expansion `I'(x) = 12x + (144/5)x³ + O(x⁵)` itself (inversion of
`Λ'(s) = s/12 - s³/720 + O(s⁵)`) is a hypothesis here.
-/
import UniformLanczos.Endpoint

open Set Real intervalIntegral

namespace UniformLanczos

lemma integral_sin_four_half_pi : ∫ θ in (0 : ℝ)..(π / 2), sin θ ^ 4 = 3 * π / 16 := by
  have h := integral_sin_pow (a := 0) (b := π / 2) 2
  norm_num [sin_pi_div_two, cos_pi_div_two] at h
  rw [h]; ring

theorem Hint_expansion {I1 : ℝ → ℝ} {b C : ℝ} (hC : 0 ≤ C)
    (hIc : ContinuousOn I1 (Icc 0 b))
    (hexp : ∀ x ∈ Icc 0 b, |I1 x - (12 * x + 144 / 5 * x ^ 3)| ≤ C * x ^ 5) :
    ∀ a ∈ Icc 0 b, |Hint (fun y => y * I1 y) a - (3 * a ^ 2 + 27 / 5 * a ^ 4)| ≤ C * a ^ 6 / 2 := by
  intro a ha
  have hpoly : Hint (fun y => y * (12 * y + 144 / 5 * y ^ 3)) a = 3 * a ^ 2 + 27 / 5 * a ^ 4 := by
    unfold Hint
    have e : (fun θ => a * sin θ * (12 * (a * sin θ) + 144 / 5 * (a * sin θ) ^ 3)) =
        fun θ => (12 * a ^ 2) * sin θ ^ 2 + (144 / 5 * a ^ 4) * sin θ ^ 4 := by
      funext θ; ring
    rw [e, integral_add, integral_const_mul, integral_const_mul, integral_sin_sq_half_pi,
      integral_sin_four_half_pi]
    · field_simp; ring
    · exact (continuous_const.mul ((continuous_sin).pow 2)).intervalIntegrable _ _
    · exact (continuous_const.mul ((continuous_sin).pow 4)).intervalIntegrable _ _
  rw [← hpoly]
  have ha0 : a ∈ Icc 0 a := ⟨ha.1, le_rfl⟩
  have hab : Icc 0 a ⊆ Icc 0 b := Icc_subset_Icc le_rfl ha.2
  have hpc : ContinuousOn (fun y : ℝ => y * (12 * y + 144 / 5 * y ^ 3)) (Icc 0 a) := by
    fun_prop
  have hIc' : ContinuousOn (fun y => y * I1 y) (Icc 0 a) := continuousOn_id.mul (hIc.mono hab)
  have hclose : ∀ y ∈ Icc 0 a,
      |y * I1 y - y * (12 * y + 144 / 5 * y ^ 3)| ≤ C * a ^ 6 := by
    intro y hy
    rw [← mul_sub, abs_mul, abs_of_nonneg hy.1]
    have h1 := hexp y (hab hy)
    have hy5 : y ^ 5 ≤ a ^ 5 := pow_le_pow_left₀ hy.1 hy.2 5
    calc y * |I1 y - (12 * y + 144 / 5 * y ^ 3)| ≤ a * (C * a ^ 5) :=
          mul_le_mul hy.2 (h1.trans (mul_le_mul_of_nonneg_left hy5 hC)) (abs_nonneg _) ha.1
      _ = C * a ^ 6 := by ring
  have := Hint_close ha.1 hIc' hpc hclose a ha0
  linarith [this]

theorem A_le_half_alpha {A α r C : ℝ} (hA0 : 0 ≤ A) (hα : α = 3 * A + 27 / 5 * A ^ 2 + r)
    (hr : |r| ≤ C * A ^ 3) (hsmall : C * A ^ 2 ≤ 1) : 2 * A ≤ α := by
  have h1 : -(C * A ^ 3) ≤ r := (abs_le.mp hr).1
  have h2 : C * A ^ 3 ≤ A := by nlinarith
  nlinarith [sq_nonneg A]

theorem inversion {A α r C : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hC : 0 ≤ C)
    (hα : α = 3 * A + 27 / 5 * A ^ 2 + r) (hr : |r| ≤ C * A ^ 3) :
    |A / 4 - (α / 12 - α ^ 2 / 20)| ≤
      (C / 12 + (162 / 5 + 729 / 25 + 6 * C + 54 / 5 * C + C ^ 2) / 20) * A ^ 3 := by
  have hid : A / 4 - (α / 12 - α ^ 2 / 20) =
      -r / 12 + (162 / 5 * A ^ 3 + 729 / 25 * A ^ 4 + 6 * A * r + 54 / 5 * A ^ 2 * r + r ^ 2) / 20 := by
    rw [hα]; ring
  rw [hid]
  have hA3 : 0 ≤ A ^ 3 := pow_nonneg hA0 3
  have hA4 : A ^ 4 ≤ A ^ 3 := by nlinarith [pow_nonneg hA0 3]
  have hrA : |A * r| ≤ C * A ^ 3 := by
    rw [abs_mul, abs_of_nonneg hA0]
    calc A * |r| ≤ A * (C * A ^ 3) := mul_le_mul_of_nonneg_left hr hA0
      _ = C * A ^ 4 := by ring
      _ ≤ C * A ^ 3 := mul_le_mul_of_nonneg_left hA4 hC
  have hA2r : |A ^ 2 * r| ≤ C * A ^ 3 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg A)]
    have hA5 : A ^ 5 ≤ A ^ 3 := by nlinarith [pow_nonneg hA0 3, sq_nonneg A]
    calc A ^ 2 * |r| ≤ A ^ 2 * (C * A ^ 3) := mul_le_mul_of_nonneg_left hr (sq_nonneg A)
      _ = C * A ^ 5 := by ring
      _ ≤ C * A ^ 3 := mul_le_mul_of_nonneg_left hA5 hC
  have hr2 : r ^ 2 ≤ C ^ 2 * A ^ 3 := by
    have : r ^ 2 = |r| ^ 2 := (sq_abs r).symm
    rw [this]
    have hA6 : A ^ 6 ≤ A ^ 3 := by nlinarith [pow_nonneg hA0 3, pow_le_one₀ hA0 hA1 (n := 3)]
    calc |r| ^ 2 ≤ (C * A ^ 3) ^ 2 := pow_le_pow_left₀ (abs_nonneg r) hr 2
      _ = C ^ 2 * A ^ 6 := by ring
      _ ≤ C ^ 2 * A ^ 3 := mul_le_mul_of_nonneg_left hA6 (sq_nonneg C)
  have hr' := abs_le.mp hr
  have hrA' := abs_le.mp hrA
  have hA2r' := abs_le.mp hA2r
  have hr2' : 0 ≤ r ^ 2 := sq_nonneg r
  rw [abs_le]
  constructor <;> nlinarith

end UniformLanczos
