import EulerianGrothendieck.SummationRemainder

noncomputable section
open scoped BigOperators
open Finset Polynomial
namespace EulerianGrothendieck

theorem shifted_power_geometric_summable (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (d : ℕ) :
    Summable (fun k : ℕ => (k+1:ℝ)^d*s^k) := by
  have hs : ‖s‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hs0]
  have h := (summable_nat_add_iff 1).2 (summable_pow_mul_geometric_of_norm_lt_one d hs)
  have h' : Summable (fun k : ℕ => ((k+1:ℝ)^d*s^k)*s) := by
    simpa only [Nat.cast_add, Nat.cast_one, pow_succ, mul_assoc] using h
  exact (summable_mul_right_iff (ne_of_gt hs0)).1 h'

theorem weighted_polynomial_power_summable (w : ℕ → ℝ) (s C : ℝ) (d r : ℕ)
    (hs0 : 0 < s) (hs1 : s < 1) (hw : ∀ k, 0 ≤ w k)
    (hws : ∀ k, w k ≤ s^k) (hC : 0 ≤ C) :
    Summable (fun k : ℕ => w k*(C*(k+1:ℝ)^d)^r) := by
  have h := (shifted_power_geometric_summable s hs0 hs1 (d*r)).mul_left (C^r)
  apply h.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw k) (by positivity))]
  calc
    w k*(C*(k+1:ℝ)^d)^r ≤ s^k*(C*(k+1:ℝ)^d)^r :=
      mul_le_mul_of_nonneg_right (hws k) (by positivity)
    _ = C^r*((k+1:ℝ)^(d*r)*s^k) := by rw [mul_pow, pow_mul]; ring

theorem weighted_coefficients_summable (P : ℕ → ℝ[X]) (w : ℕ → ℝ)
    (A C s : ℝ) (d r : ℕ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hs0 : 0 < s) (hs1 : s < 1) (hw : ∀ k, 0 ≤ w k)
    (hws : ∀ k, w k ≤ s^k)
    (hcoeff : ∀ k, |(P k).coeff r| ≤ A*(r+1)*(C*(k+1:ℝ)^d)^r) :
    Summable (fun k => w k*(P k).coeff r) := by
  have h := (weighted_polynomial_power_summable w s C d r hs0 hs1 hw hws hC).mul_left (A*(r+1))
  apply h.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw k)]
  simpa only [mul_assoc, mul_left_comm] using
    mul_le_mul_of_nonneg_left (hcoeff k) (hw k)

theorem weighted_remainderMajorant_summable (w : ℕ → ℝ) (A C s : ℝ) (d R : ℕ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hs0 : 0 < s) (hs1 : s < 1)
    (hw : ∀ k, 0 ≤ w k) (hws : ∀ k, w k ≤ s^k) :
    Summable (fun k => w k*remainderMajorant A (C*(k+1:ℝ)^d) R) := by
  have hp := fun r => weighted_polynomial_power_summable w s C d r hs0 hs1 hw hws hC
  have h1 := (hp (R+1)).mul_left (A*(2*R+6))
  have h2 := (hp (R+1)).mul_left ((2:ℝ)^(R+1))
  have h3 : Summable (fun k => ∑ r ∈ range (R+1),
      ((2:ℝ)^(R+1)*A*(r+1))*(w k*(C*(k+1:ℝ)^d)^(R+1+r))) := by
    apply summable_sum
    intro r hr
    exact (hp (R+1+r)).mul_left _
  apply (h1.add (h2.add h3)).congr
  intro k
  unfold remainderMajorant
  have heq : (∑ r ∈ range (R+1),
      ((2:ℝ)^(R+1)*A*(r+1))*(w k*(C*(k+1:ℝ)^d)^(R+1+r))) =
      w k*(2*(C*(k+1:ℝ)^d))^(R+1)*
        (∑ r ∈ range (R+1), A*(r+1)*(C*(k+1:ℝ)^d)^r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [mul_pow, pow_add]
    ring
  rw [heq, mul_pow]
  ring

/-- An arbitrary finite-order expansion with a single constant independent of
M, for every family satisfying the displayed polynomial coefficient bounds. -/
theorem geometric_weighted_all_order_remainder (P : ℕ → ℝ[X]) (w : ℕ → ℝ)
    (A C s : ℝ) (d R : ℕ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hs0 : 0 < s) (hs1 : s < 1) (hw : ∀ k, 0 ≤ w k)
    (hws : ∀ k, w k ≤ s^k)
    (hvalues : ∀ M : ℕ, M ≠ 0 → ∀ k, |(P k).eval (1/(M:ℝ))| ≤ 1)
    (hcoeff : ∀ k r, |(P k).coeff r| ≤ A*(r+1)*(C*(k+1:ℝ)^d)^r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, M ≠ 0 →
      |(∑' k, w k*(P k).eval (1/(M:ℝ))) -
        ∑ r ∈ range (R+1), (∑' k, w k*(P k).coeff r)/(M:ℝ)^r| ≤
        K/(M:ℝ)^(R+1) := by
  let K := ∑' k, w k*remainderMajorant A (C*(k+1:ℝ)^d) R
  refine ⟨K, tsum_nonneg (fun k => mul_nonneg (hw k)
    (remainderMajorant_nonneg _ _ _ hA (by positivity))), ?_⟩
  intro M hM
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM
  have hwsum : Summable w := (hasSum_geometric_of_lt_one (le_of_lt hs0) hs1).summable.of_norm_bounded
    (fun k => by rw [Real.norm_eq_abs, abs_of_nonneg (hw k)]; exact hws k)
  have h := weighted_polynomial_remainder P w (fun k => C*(k+1:ℝ)^d) A (1/(M:ℝ)) R
    hA (by positivity) (by exact (div_le_one (by positivity)).2 hM1) hw (fun k => by positivity)
    (hvalues M hM) hcoeff hwsum
    (fun r => weighted_coefficients_summable P w A C s d r hA hC hs0 hs1 hw hws (fun k => hcoeff k r))
    (weighted_remainderMajorant_summable w A C s d R hA hC hs0 hs1 hw hws)
  simpa only [one_div_pow, mul_one_div] using h

end EulerianGrothendieck
