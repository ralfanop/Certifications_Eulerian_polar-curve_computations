import UniformLanczos.Lemma511
import UniformLanczos.Lemma512
import UniformLanczos.Lemma513

/-! M12 5.8: the finite weighted energy estimate and the transfer from
recurrence coefficients to their squares. No claim of the full rate is made
until the concrete estimates and the window argument are connected. -/

namespace UniformLanczos.Theorem514

open Finset UniformLanczos.Theorem59

/-- A coercivity estimate converts a weighted residual bound into a weighted
squared-error bound. The proof uses the square of μ d - r. -/
theorem weighted_energy {ι : Type*} [Fintype ι]
    (w d r : ι → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hw : ∀ i, 0 ≤ w i)
    (hcoercive : μ * (∑ i, w i * (d i)^2) ≤ ∑ i, w i * d i * r i) :
    μ^2 * (∑ i, w i * (d i)^2) ≤ ∑ i, w i * (r i)^2 := by
  have hs : 0 ≤ ∑ i, w i * (μ * d i - r i)^2 := by
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  have he : (∑ i, w i * (μ * d i - r i)^2) =
      μ^2 * (∑ i, w i * (d i)^2) -
        2 * μ * (∑ i, w i * d i * r i) + ∑ i, w i * (r i)^2 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hs
  have hc := mul_le_mul_of_nonneg_left hcoercive hμ.le
  nlinarith

theorem square_rate_transfer {a b E : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)
    (hE : |a - b| ≤ E) : |a^2 - b^2| ≤ E := by
  rw [show a^2 - b^2 = (a-b)*(a+b) by ring, abs_mul,
    abs_of_nonneg (add_nonneg ha hb)]
  exact (mul_le_of_le_one_right (abs_nonneg _) hab).trans hE

/-- The two conclusions must use the same normalized coefficient. This is
the exact square-transfer step for the existing definitions of betaM and F. -/
theorem beta_rate_of_sqrt_rate {j M : ℕ} (hM : 0 < M)
    (hβ : 0 ≤ betaM M j) (ht : 0 < (j : ℝ) / M)
    (hbound : Real.sqrt (betaM M j) / (M : ℝ) ≤ 1 / 2)
    {C : ℝ}
    (hrate : |Real.sqrt (betaM M j) / (M : ℝ) -
      Profile.ξ ((j : ℝ) / M) / 2| ≤ C / M) :
    |betaM M j / (M : ℝ)^2 - Profile.F ((j : ℝ) / M)| ≤ C / M := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hξ := (Profile.ξ_spec ht).1
  have ha : 0 ≤ Real.sqrt (betaM M j) / (M : ℝ) :=
    div_nonneg (Real.sqrt_nonneg _) hMr.le
  have hb : 0 ≤ Profile.ξ ((j : ℝ) / M) / 2 :=
    div_nonneg hξ.1.le (by norm_num)
  have hab : Real.sqrt (betaM M j) / (M : ℝ) +
      Profile.ξ ((j : ℝ) / M) / 2 ≤ 1 := by
    linarith [hξ.2]
  have h := square_rate_transfer ha hb hab hrate
  rw [div_pow, Real.sq_sqrt hβ, div_pow] at h
  simpa [Profile.F, show (2 : ℝ)^2 = 4 by norm_num] using h

end UniformLanczos.Theorem514

#print axioms UniformLanczos.Theorem514.weighted_energy
#print axioms UniformLanczos.Theorem514.square_rate_transfer
#print axioms UniformLanczos.Theorem514.beta_rate_of_sqrt_rate
