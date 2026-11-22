import EulerianCert.CentralSlope
import PrivateApex.GlobalApex

/-!
PRIVATE: Manuscript 15, Section 7 -- asymptotic expansion of the even central slopes.

Let `n = 2m ≥ 4`, `N = n + 1`, `σ(x) = √(216/(π x))`.  The exact identity
`t_n = 2 N² / ((N+1)(N+3)) · s_{n+1}` (`slopeQ_even_cast`) transfers every expansion of the
odd slopes `s_{n+1}` in powers of `1/(N+1)` to an expansion of `t_n` in powers of `1/N`.

* `transfer_core`: the exact splitting behind the transfer, for an arbitrary real `s`.
* `ratio_bound_one`, `ratio_bound_two`: for arbitrary real `d₁`, `d₂`,
    `N²/((N+1)(N+3)) · (1 + d₁/(N+1)) · √(N/(N+1)) = 1 + e₁/N + O(N⁻²)`,
    `N²/((N+1)(N+3)) · (1 + d₁/(N+1) + d₂/(N+1)²) · √(N/(N+1)) = 1 + e₁/N + e₂/N² + O(N⁻³)`,
  with `e₁ = d₁ - 9/2`, `e₂ = d₂ - (11/2) d₁ + 123/8` and explicit constants.
* `even_slope_asymp` (unconditional): from the first-order odd expansion proved in
  `EulerianCert.CentralSlope.slope_asymp`,
    `|t_n - 2 σ(N) (1 - 33/(4N))| ≤ K N^(-5/2)`   for all even `n ≥ 4`.
* `even_slope_second_order_of_odd` (transfer, proved implication): if the odd slopes satisfy
    `|s_n - σ(D)(1 + d₁/D + d₂/D²)| ≤ K D^(-7/2)`, `D = n + 1`,
  then  `|t_n - 2 σ(N)(1 + e₁/N + e₂/N²)| ≤ K' N^(-7/2)`.
* `even_slope_second_order_coefficients`: the same with the coefficients of Manuscript 15,
  Theorem 7.4, `d₁ = -15/4`, `d₂ = 1829/160`, giving `e₁ = -33/4`, `e₂ = 7589/160`.
  The hypothesis of this implication is proved for the actual Eulerian numbers in
  `OddSecondOrder.odd_slope_second_order`; the resulting unconditional statement is
  `OddSecondOrder.even_slope_second_order`.
-/
noncomputable section
namespace PrivateApex
open Real

/-- `σ(x) = √(216/(π x))`. -/
def sig (x : ℝ) : ℝ := √(216 / (π * x))

theorem sig_nonneg (x : ℝ) : 0 ≤ sig x := sqrt_nonneg _

theorem sig_eq {N : ℝ} (hN : 0 < N) : sig N = √(216 / π) / √N := by
  unfold sig
  rw [← sqrt_div (by positivity)]
  congr 1
  field_simp

theorem sig_succ {N : ℝ} (hN : 0 < N) : sig (N + 1) = sig N * √(N / (N + 1)) := by
  unfold sig
  rw [← sqrt_mul (by positivity)]
  congr 1
  field_simp

/-- Polynomial enclosures of `√(N/(N+1)) = (1 + 1/N)^(-1/2)`. -/
theorem rho_bounds {N : ℝ} (hN : 1 ≤ N) :
    1 - 1 / (2 * N) ≤ √(N / (N + 1)) ∧
    √(N / (N + 1)) ≤ 1 - 1 / (2 * N) + 3 / (8 * N ^ 2) ∧
    1 - 1 / (2 * N) + 3 / (8 * N ^ 2) - 5 / (16 * N ^ 3) ≤ √(N / (N + 1)) := by
  have hN0 : 0 < N := by linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 1 / N := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hN0]; exact hN
  have hNx : N * x = 1 := by rw [hx]; exact mul_one_div_cancel hN0.ne'
  have h1x : 0 < 1 + x := by linarith
  have e : N / (N + 1) = 1 / (1 + x) := by
    rw [div_eq_div_iff (by positivity) h1x.ne']
    nlinarith
  have e1 : 1 / (2 * N) = x / 2 := by rw [hx]; ring
  have e2 : 3 / (8 * N ^ 2) = 3 * x ^ 2 / 8 := by rw [hx]; ring
  have e3 : 5 / (16 * N ^ 3) = 5 * x ^ 3 / 16 := by rw [hx]; ring
  rw [e, e1, e2, e3]
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hx3 : x ^ 3 ≤ 1 := pow_le_one₀ hx0.le hx1
  have hx3' : 0 ≤ x ^ 3 := pow_nonneg hx0.le 3
  refine ⟨?_, ?_, ?_⟩
  · have h0 : 0 ≤ 1 - x / 2 := by linarith
    rw [← sqrt_sq h0]
    apply sqrt_le_sqrt
    rw [le_div_iff₀ h1x]
    nlinarith [mul_nonneg hx2 (by linarith : (0 : ℝ) ≤ 3 - x)]
  · have h0 : 0 ≤ 1 - x / 2 + 3 * x ^ 2 / 8 := by linarith
    rw [← sqrt_sq h0]
    apply sqrt_le_sqrt
    rw [div_le_iff₀ h1x]
    nlinarith [mul_nonneg hx3' (by nlinarith : (0 : ℝ) ≤ 5 / 8 - 15 * x / 64 + 9 * x ^ 2 / 64)]
  · have h0 : 0 ≤ 1 - x / 2 + 3 * x ^ 2 / 8 - 5 * x ^ 3 / 16 := by linarith
    rw [← sqrt_sq h0]
    apply sqrt_le_sqrt
    rw [le_div_iff₀ h1x]
    nlinarith [mul_nonneg (pow_nonneg hx0.le 4)
      (by linarith : (0 : ℝ) ≤ 35 / 64 - 7 * x / 32 + 35 * x ^ 2 / 256 - 25 * x ^ 3 / 256)]

/-- The exact splitting behind the transfer from odd to even slopes. -/
theorem transfer_core {N : ℝ} (hN : 1 ≤ N) (s P T : ℝ) :
    |2 * N ^ 2 / ((N + 1) * (N + 3)) * s - 2 * sig N * T| ≤
      2 * |s - sig (N + 1) * P| +
      2 * sig N * |N ^ 2 / ((N + 1) * (N + 3)) * P * √(N / (N + 1)) - T| := by
  have hN0 : 0 < N := by linarith
  have hc0 : 0 ≤ 2 * N ^ 2 / ((N + 1) * (N + 3)) := by positivity
  have hc2 : 2 * N ^ 2 / ((N + 1) * (N + 3)) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hσ : 0 ≤ 2 * sig N := mul_nonneg (by norm_num) (sig_nonneg N)
  have hid : 2 * N ^ 2 / ((N + 1) * (N + 3)) * s - 2 * sig N * T =
      2 * N ^ 2 / ((N + 1) * (N + 3)) * (s - sig (N + 1) * P) +
      2 * sig N * (N ^ 2 / ((N + 1) * (N + 3)) * P * √(N / (N + 1)) - T) := by
    rw [sig_succ hN0]; ring
  rw [hid]
  calc |2 * N ^ 2 / ((N + 1) * (N + 3)) * (s - sig (N + 1) * P) +
        2 * sig N * (N ^ 2 / ((N + 1) * (N + 3)) * P * √(N / (N + 1)) - T)|
      ≤ |2 * N ^ 2 / ((N + 1) * (N + 3)) * (s - sig (N + 1) * P)| +
        |2 * sig N * (N ^ 2 / ((N + 1) * (N + 3)) * P * √(N / (N + 1)) - T)| := abs_add_le _ _
    _ = 2 * N ^ 2 / ((N + 1) * (N + 3)) * |s - sig (N + 1) * P| +
        2 * sig N * |N ^ 2 / ((N + 1) * (N + 3)) * P * √(N / (N + 1)) - T| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hc0, abs_of_nonneg hσ]
    _ ≤ 2 * |s - sig (N + 1) * P| +
        2 * sig N * |N ^ 2 / ((N + 1) * (N + 3)) * P * √(N / (N + 1)) - T| :=
        add_le_add (mul_le_mul_of_nonneg_right hc2 (abs_nonneg _)) le_rfl

/-- First-order transfer of the coefficients: `e₁ = d₁ - 9/2`. -/
theorem ratio_bound_one {N : ℝ} (hN : 1 ≤ N) (d₁ : ℝ) :
    |N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1)) * √(N / (N + 1)) -
        (1 + (d₁ - 9 / 2) / N)| ≤ (58 + 16 * |d₁|) / N ^ 2 := by
  have hN0 : 0 < N := by linarith
  obtain ⟨hL, hU, -⟩ := rho_bounds hN
  have hA0 : 0 ≤ |d₁| := abs_nonneg _
  have hdA : d₁ ≤ |d₁| := le_abs_self _
  have hdA' : -|d₁| ≤ d₁ := neg_abs_le _
  have hq0 : 0 ≤ N ^ 2 / ((N + 1) * (N + 3)) := by positivity
  have hq1 : N ^ 2 / ((N + 1) * (N + 3)) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hR : |N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1))| ≤ 1 + |d₁| := by
    have h1 : |d₁ / (N + 1)| ≤ |d₁| := by
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < N + 1)]
      exact div_le_self hA0 (by linarith)
    have hP : |1 + d₁ / (N + 1)| ≤ 1 + |d₁| :=
      (abs_add_le _ _).trans (by rw [abs_one]; linarith)
    rw [abs_mul, abs_of_nonneg hq0]
    calc N ^ 2 / ((N + 1) * (N + 3)) * |1 + d₁ / (N + 1)| ≤ 1 * (1 + |d₁|) :=
          mul_le_mul hq1 hP (abs_nonneg _) (by norm_num)
      _ = 1 + |d₁| := one_mul _
  have hρ : |√(N / (N + 1)) - (1 - 1 / (2 * N))| ≤ 3 / (8 * N ^ 2) := by
    have h3 : (0 : ℝ) ≤ 3 / (8 * N ^ 2) := by positivity
    rw [abs_le]
    constructor <;> linarith
  have hkey : N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1)) * (1 - 1 / (2 * N)) -
      (1 + (d₁ - 9 / 2) / N) =
      ((30 - 11 * d₁) * N ^ 2 + (57 - 14 * d₁) * N + (27 - 6 * d₁)) /
        (2 * N * (N + 1) ^ 2 * (N + 3)) := by
    field_simp
    ring
  have hden : 0 < 2 * N * (N + 1) ^ 2 * (N + 3) := by positivity
  have hnum : |(30 - 11 * d₁) * N ^ 2 + (57 - 14 * d₁) * N + (27 - 6 * d₁)| ≤
      (114 + 31 * |d₁|) * N ^ 2 := by
    have hNN : 0 ≤ N ^ 2 := sq_nonneg N
    have hN2 : N ≤ N ^ 2 := by nlinarith
    have h1N2 : (1 : ℝ) ≤ N ^ 2 := by nlinarith
    have u2 : d₁ * N ^ 2 ≤ |d₁| * N ^ 2 := mul_le_mul_of_nonneg_right hdA hNN
    have l2 : -(|d₁| * N ^ 2) ≤ d₁ * N ^ 2 := by
      linarith [mul_le_mul_of_nonneg_right hdA' hNN]
    have u1 : d₁ * N ≤ |d₁| * N := mul_le_mul_of_nonneg_right hdA hN0.le
    have l1 : -(|d₁| * N) ≤ d₁ * N := by
      linarith [mul_le_mul_of_nonneg_right hdA' hN0.le]
    have a1 : |d₁| * N ≤ |d₁| * N ^ 2 := mul_le_mul_of_nonneg_left hN2 hA0
    have a0 : |d₁| ≤ |d₁| * N ^ 2 := by
      linarith [mul_le_mul_of_nonneg_left h1N2 hA0]
    rw [abs_le]
    constructor <;> nlinarith
  have hRU : |N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1)) * (1 - 1 / (2 * N)) -
      (1 + (d₁ - 9 / 2) / N)| ≤ (114 + 31 * |d₁|) / (2 * N ^ 2) := by
    rw [hkey, abs_div, abs_of_pos hden]
    calc |(30 - 11 * d₁) * N ^ 2 + (57 - 14 * d₁) * N + (27 - 6 * d₁)| /
          (2 * N * (N + 1) ^ 2 * (N + 3))
        ≤ (114 + 31 * |d₁|) * N ^ 2 / (2 * N * (N + 1) ^ 2 * (N + 3)) :=
          div_le_div_of_nonneg_right hnum hden.le
      _ ≤ (114 + 31 * |d₁|) / (2 * N ^ 2) := by
          rw [div_le_div_iff₀ hden (by positivity)]
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 114 + 31 * |d₁|)
            (by positivity : (0 : ℝ) ≤ 2 * N * (5 * N ^ 2 + 7 * N + 3))]
  have hsplit : N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1)) * √(N / (N + 1)) -
      (1 + (d₁ - 9 / 2) / N) =
      N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1)) *
        (√(N / (N + 1)) - (1 - 1 / (2 * N))) +
      (N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1)) * (1 - 1 / (2 * N)) -
        (1 + (d₁ - 9 / 2) / N)) := by ring
  rw [hsplit]
  calc |N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1)) *
          (√(N / (N + 1)) - (1 - 1 / (2 * N))) +
        (N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1)) * (1 - 1 / (2 * N)) -
          (1 + (d₁ - 9 / 2) / N))|
      ≤ |N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1)) *
          (√(N / (N + 1)) - (1 - 1 / (2 * N)))| +
        |N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1)) * (1 - 1 / (2 * N)) -
          (1 + (d₁ - 9 / 2) / N)| := abs_add_le _ _
    _ ≤ (1 + |d₁|) * (3 / (8 * N ^ 2)) + (114 + 31 * |d₁|) / (2 * N ^ 2) := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul hR hρ (abs_nonneg _) (by positivity)) hRU
    _ = ((1 + |d₁|) * 3 / 8 + (114 + 31 * |d₁|) / 2) / N ^ 2 := by ring
    _ ≤ (58 + 16 * |d₁|) / N ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith

/-- Second-order transfer of the coefficients: `e₁ = d₁ - 9/2`, `e₂ = d₂ - (11/2) d₁ + 123/8`. -/
theorem ratio_bound_two {N : ℝ} (hN : 1 ≤ N) (d₁ d₂ : ℝ) :
    |N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2) * √(N / (N + 1)) -
        (1 + (d₁ - 9 / 2) / N + (d₂ - 11 / 2 * d₁ + 123 / 8) / N ^ 2)| ≤
      (377 + 147 * |d₁| + 32 * |d₂|) / N ^ 3 := by
  have hN0 : 0 < N := by linarith
  obtain ⟨-, hU, hL⟩ := rho_bounds hN
  have hA0 : 0 ≤ |d₁| := abs_nonneg _
  have hB0 : 0 ≤ |d₂| := abs_nonneg _
  have hdA : d₁ ≤ |d₁| := le_abs_self _
  have hdA' : -|d₁| ≤ d₁ := neg_abs_le _
  have hdB : d₂ ≤ |d₂| := le_abs_self _
  have hdB' : -|d₂| ≤ d₂ := neg_abs_le _
  have hq0 : 0 ≤ N ^ 2 / ((N + 1) * (N + 3)) := by positivity
  have hq1 : N ^ 2 / ((N + 1) * (N + 3)) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hR : |N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2)| ≤
      1 + |d₁| + |d₂| := by
    have hN1 : (1 : ℝ) ≤ N + 1 := by linarith
    have h1 : |d₁ / (N + 1)| ≤ |d₁| := by
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < N + 1)]
      exact div_le_self hA0 hN1
    have h2 : |d₂ / (N + 1) ^ 2| ≤ |d₂| := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N + 1) ^ 2)]
      exact div_le_self hB0 (by nlinarith)
    have hP : |1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2| ≤ 1 + |d₁| + |d₂| := by
      calc |1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2|
          ≤ |1 + d₁ / (N + 1)| + |d₂ / (N + 1) ^ 2| := abs_add_le _ _
        _ ≤ (|(1 : ℝ)| + |d₁ / (N + 1)|) + |d₂ / (N + 1) ^ 2| :=
            add_le_add (abs_add_le _ _) le_rfl
        _ ≤ 1 + |d₁| + |d₂| := by rw [abs_one]; linarith
    rw [abs_mul, abs_of_nonneg hq0]
    calc N ^ 2 / ((N + 1) * (N + 3)) * |1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2|
        ≤ 1 * (1 + |d₁| + |d₂|) := mul_le_mul hq1 hP (abs_nonneg _) (by norm_num)
      _ = 1 + |d₁| + |d₂| := one_mul _
  have hρ : |√(N / (N + 1)) - (1 - 1 / (2 * N) + 3 / (8 * N ^ 2))| ≤ 5 / (16 * N ^ 3) := by
    have h5 : (0 : ℝ) ≤ 5 / (16 * N ^ 3) := by positivity
    rw [abs_le]
    constructor <;> linarith
  have hkey : N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2) *
        (1 - 1 / (2 * N) + 3 / (8 * N ^ 2)) -
      (1 + (d₁ - 9 / 2) / N + (d₂ - 11 / 2 * d₁ + 123 / 8) / N ^ 2) =
      ((167 * d₁ - 52 * d₂ - 384) * N ^ 3 + (451 * d₁ - 93 * d₂ - 1137) * N ^ 2 +
        (416 * d₁ - 80 * d₂ - 1122) * N + (132 * d₁ - 24 * d₂ - 369)) /
        (8 * N ^ 2 * (N + 1) ^ 3 * (N + 3)) := by
    field_simp
    ring
  have hden : 0 < 8 * N ^ 2 * (N + 1) ^ 3 * (N + 3) := by positivity
  have hnum : |(167 * d₁ - 52 * d₂ - 384) * N ^ 3 + (451 * d₁ - 93 * d₂ - 1137) * N ^ 2 +
        (416 * d₁ - 80 * d₂ - 1122) * N + (132 * d₁ - 24 * d₂ - 369)| ≤
      (3012 + 1166 * |d₁| + 249 * |d₂|) * N ^ 3 := by
    have hN3 : 0 ≤ N ^ 3 := pow_nonneg hN0.le 3
    have hNN : 0 ≤ N ^ 2 := sq_nonneg N
    have n2 : N ^ 2 ≤ N ^ 3 := by nlinarith
    have n1 : N ≤ N ^ 3 := by nlinarith
    have n0 : (1 : ℝ) ≤ N ^ 3 := by nlinarith
    have u3 : d₁ * N ^ 3 ≤ |d₁| * N ^ 3 := mul_le_mul_of_nonneg_right hdA hN3
    have l3 : -(|d₁| * N ^ 3) ≤ d₁ * N ^ 3 := by
      linarith [mul_le_mul_of_nonneg_right hdA' hN3]
    have u2 : d₁ * N ^ 2 ≤ |d₁| * N ^ 2 := mul_le_mul_of_nonneg_right hdA hNN
    have l2 : -(|d₁| * N ^ 2) ≤ d₁ * N ^ 2 := by
      linarith [mul_le_mul_of_nonneg_right hdA' hNN]
    have u1 : d₁ * N ≤ |d₁| * N := mul_le_mul_of_nonneg_right hdA hN0.le
    have l1 : -(|d₁| * N) ≤ d₁ * N := by
      linarith [mul_le_mul_of_nonneg_right hdA' hN0.le]
    have v3 : d₂ * N ^ 3 ≤ |d₂| * N ^ 3 := mul_le_mul_of_nonneg_right hdB hN3
    have w3 : -(|d₂| * N ^ 3) ≤ d₂ * N ^ 3 := by
      linarith [mul_le_mul_of_nonneg_right hdB' hN3]
    have v2 : d₂ * N ^ 2 ≤ |d₂| * N ^ 2 := mul_le_mul_of_nonneg_right hdB hNN
    have w2 : -(|d₂| * N ^ 2) ≤ d₂ * N ^ 2 := by
      linarith [mul_le_mul_of_nonneg_right hdB' hNN]
    have v1 : d₂ * N ≤ |d₂| * N := mul_le_mul_of_nonneg_right hdB hN0.le
    have w1 : -(|d₂| * N) ≤ d₂ * N := by
      linarith [mul_le_mul_of_nonneg_right hdB' hN0.le]
    have a2 : |d₁| * N ^ 2 ≤ |d₁| * N ^ 3 := mul_le_mul_of_nonneg_left n2 hA0
    have a1 : |d₁| * N ≤ |d₁| * N ^ 3 := mul_le_mul_of_nonneg_left n1 hA0
    have a0 : |d₁| ≤ |d₁| * N ^ 3 := by linarith [mul_le_mul_of_nonneg_left n0 hA0]
    have b2 : |d₂| * N ^ 2 ≤ |d₂| * N ^ 3 := mul_le_mul_of_nonneg_left n2 hB0
    have b1 : |d₂| * N ≤ |d₂| * N ^ 3 := mul_le_mul_of_nonneg_left n1 hB0
    have b0 : |d₂| ≤ |d₂| * N ^ 3 := by linarith [mul_le_mul_of_nonneg_left n0 hB0]
    rw [abs_le]
    constructor <;> nlinarith
  have hRU : |N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2) *
        (1 - 1 / (2 * N) + 3 / (8 * N ^ 2)) -
      (1 + (d₁ - 9 / 2) / N + (d₂ - 11 / 2 * d₁ + 123 / 8) / N ^ 2)| ≤
      (3012 + 1166 * |d₁| + 249 * |d₂|) / (8 * N ^ 3) := by
    rw [hkey, abs_div, abs_of_pos hden]
    calc |(167 * d₁ - 52 * d₂ - 384) * N ^ 3 + (451 * d₁ - 93 * d₂ - 1137) * N ^ 2 +
          (416 * d₁ - 80 * d₂ - 1122) * N + (132 * d₁ - 24 * d₂ - 369)| /
          (8 * N ^ 2 * (N + 1) ^ 3 * (N + 3))
        ≤ (3012 + 1166 * |d₁| + 249 * |d₂|) * N ^ 3 / (8 * N ^ 2 * (N + 1) ^ 3 * (N + 3)) :=
          div_le_div_of_nonneg_right hnum hden.le
      _ ≤ (3012 + 1166 * |d₁| + 249 * |d₂|) / (8 * N ^ 3) := by
          rw [div_le_div_iff₀ hden (by positivity)]
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 3012 + 1166 * |d₁| + 249 * |d₂|)
            (by positivity : (0 : ℝ) ≤ 8 * N ^ 2 * (6 * N ^ 3 + 12 * N ^ 2 + 10 * N + 3))]
  have hsplit : N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2) *
        √(N / (N + 1)) -
      (1 + (d₁ - 9 / 2) / N + (d₂ - 11 / 2 * d₁ + 123 / 8) / N ^ 2) =
      N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2) *
        (√(N / (N + 1)) - (1 - 1 / (2 * N) + 3 / (8 * N ^ 2))) +
      (N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2) *
        (1 - 1 / (2 * N) + 3 / (8 * N ^ 2)) -
        (1 + (d₁ - 9 / 2) / N + (d₂ - 11 / 2 * d₁ + 123 / 8) / N ^ 2)) := by ring
  rw [hsplit]
  calc |N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2) *
          (√(N / (N + 1)) - (1 - 1 / (2 * N) + 3 / (8 * N ^ 2))) +
        (N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2) *
          (1 - 1 / (2 * N) + 3 / (8 * N ^ 2)) -
          (1 + (d₁ - 9 / 2) / N + (d₂ - 11 / 2 * d₁ + 123 / 8) / N ^ 2))|
      ≤ |N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2) *
          (√(N / (N + 1)) - (1 - 1 / (2 * N) + 3 / (8 * N ^ 2)))| +
        |N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2) *
          (1 - 1 / (2 * N) + 3 / (8 * N ^ 2)) -
          (1 + (d₁ - 9 / 2) / N + (d₂ - 11 / 2 * d₁ + 123 / 8) / N ^ 2)| := abs_add_le _ _
    _ ≤ (1 + |d₁| + |d₂|) * (5 / (16 * N ^ 3)) +
        (3012 + 1166 * |d₁| + 249 * |d₂|) / (8 * N ^ 3) := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul hR hρ (abs_nonneg _) (by positivity)) hRU
    _ = ((1 + |d₁| + |d₂|) * 5 / 16 + (3012 + 1166 * |d₁| + 249 * |d₂|) / 8) / N ^ 3 := by ring
    _ ≤ (377 + 147 * |d₁| + 32 * |d₂|) / N ^ 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith

/-- `(N+1)^k √(N+1) ≥ N^k √N`: the remainders in `1/(N+1)` are remainders in `1/N`. -/
theorem remainder_mono {N : ℝ} (hN : 1 ≤ N) (k : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    K / ((N + 1) ^ k * √(N + 1)) ≤ K / (N ^ k * √N) := by
  have hN0 : 0 < N := by linarith
  apply div_le_div_of_nonneg_left hK (by positivity)
  exact mul_le_mul (pow_le_pow_left₀ hN0.le (by linarith) k) (sqrt_le_sqrt (by linarith))
    (sqrt_nonneg _) (by positivity)

/-- **Even-order central slopes, first-order asymptotics** (unconditional).  For even
`n = 2m ≥ 4` and `N = n + 1`:  `|t_n - 2 √(216/(πN)) (1 - 33/(4N))| ≤ K N^(-5/2)`. -/
theorem even_slope_asymp : ∃ K, ∀ m : ℕ, 2 ≤ m →
    |((slopeQ (2 * m) : ℚ) : ℝ) - 2 * √(216 / (π * ((2 * m + 1 : ℕ) : ℝ))) *
        (1 - 33 / (4 * ((2 * m + 1 : ℕ) : ℝ)))| ≤
      K / (((2 * m + 1 : ℕ) : ℝ) ^ 2 * √((2 * m + 1 : ℕ) : ℝ)) := by
  obtain ⟨K, hK⟩ := EulerianCert.CentralSlope.slope_asymp
  refine ⟨2 * |K| + 2 * √(216 / π) * 118, fun m hm => ?_⟩
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = ((2 * m + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hN : (1 : ℝ) ≤ N := by
    rw [hNdef]; exact_mod_cast (show 1 ≤ 2 * m + 1 by omega)
  have hN0 : 0 < N := by linarith
  have hD : ((2 * m + 2 : ℕ) : ℝ) = N + 1 := by rw [hNdef]; push_cast; ring
  have hodd := hK m (by omega)
  have hslope : EulerianCert.CentralSlope.slope m = ((slopeQ (2 * m + 1) : ℚ) : ℝ) :=
    (slopeQ_odd_cast m).symm
  rw [hslope, hD] at hodd
  have hodd' : |((slopeQ (2 * m + 1) : ℚ) : ℝ) - sig (N + 1) * (1 + (-15 / 4) / (N + 1))| ≤
      |K| / (N ^ 2 * √N) := by
    have e : sig (N + 1) * (1 + (-15 / 4) / (N + 1)) =
        √(216 / (π * (N + 1))) * (1 - 15 / (4 * (N + 1))) := by
      have h4 : (15 : ℝ) / (4 * (N + 1)) = 15 / 4 / (N + 1) := by rw [div_div]
      unfold sig
      rw [h4]
      ring
    rw [e]
    exact (hodd.trans (div_le_div_of_nonneg_right (le_abs_self K) (by positivity))).trans
      (remainder_mono hN 2 (abs_nonneg K))
  have hcore := transfer_core hN ((slopeQ (2 * m + 1) : ℚ) : ℝ) (1 + (-15 / 4) / (N + 1))
    (1 + (-15 / 4 - 9 / 2) / N)
  have hratio := ratio_bound_one hN (-15 / 4)
  rw [show |(-15 / 4 : ℝ)| = 15 / 4 by rw [abs_of_neg (by norm_num)]; norm_num] at hratio
  have hσ := sig_nonneg N
  have hsN : 0 < √N := sqrt_pos.mpr hN0
  rw [slopeQ_even_cast hm, ← hNdef]
  have e2 : 2 * √(216 / (π * N)) * (1 - 33 / (4 * N)) =
      2 * sig N * (1 + (-15 / 4 - 9 / 2) / N) := by
    unfold sig; ring
  rw [e2]
  calc |2 * N ^ 2 / ((N + 1) * (N + 3)) * ((slopeQ (2 * m + 1) : ℚ) : ℝ) -
        2 * sig N * (1 + (-15 / 4 - 9 / 2) / N)|
      ≤ 2 * |((slopeQ (2 * m + 1) : ℚ) : ℝ) - sig (N + 1) * (1 + (-15 / 4) / (N + 1))| +
        2 * sig N * |N ^ 2 / ((N + 1) * (N + 3)) * (1 + (-15 / 4) / (N + 1)) * √(N / (N + 1)) -
          (1 + (-15 / 4 - 9 / 2) / N)| := hcore
    _ ≤ 2 * (|K| / (N ^ 2 * √N)) + 2 * sig N * ((58 + 16 * (15 / 4)) / N ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hodd' (by norm_num))
          (mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num) hσ))
    _ = (2 * |K| + 2 * √(216 / π) * 118) / (N ^ 2 * √N) := by
        rw [sig_eq hN0]
        field_simp
        ring

/-- **Transfer of the second-order expansion** from odd to even central slopes (a proved
implication, valid for arbitrary real coefficients `d₁`, `d₂`).  If, for all `j ≥ j₀`,
`|s_{2j+1} - σ(D)(1 + d₁/D + d₂/D²)| ≤ K D^(-7/2)` with `D = 2j + 2`, then for all
`m ≥ max 2 j₀`, with `N = 2m + 1`,
`|t_{2m} - 2 σ(N)(1 + e₁/N + e₂/N²)| ≤ K' N^(-7/2)`,
`e₁ = d₁ - 9/2`, `e₂ = d₂ - (11/2) d₁ + 123/8`,
`K' = 2|K| + 2 √(216/π) (377 + 147|d₁| + 32|d₂|)`. -/
theorem even_slope_second_order_of_odd (d₁ d₂ K : ℝ) (j₀ : ℕ)
    (hodd : ∀ j : ℕ, j₀ ≤ j →
      |((slopeQ (2 * j + 1) : ℚ) : ℝ) - √(216 / (π * ((2 * j + 2 : ℕ) : ℝ))) *
          (1 + d₁ / ((2 * j + 2 : ℕ) : ℝ) + d₂ / ((2 * j + 2 : ℕ) : ℝ) ^ 2)| ≤
        K / (((2 * j + 2 : ℕ) : ℝ) ^ 3 * √((2 * j + 2 : ℕ) : ℝ))) :
    ∀ m : ℕ, 2 ≤ m → j₀ ≤ m →
      |((slopeQ (2 * m) : ℚ) : ℝ) - 2 * √(216 / (π * ((2 * m + 1 : ℕ) : ℝ))) *
          (1 + (d₁ - 9 / 2) / ((2 * m + 1 : ℕ) : ℝ) +
            (d₂ - 11 / 2 * d₁ + 123 / 8) / ((2 * m + 1 : ℕ) : ℝ) ^ 2)| ≤
        (2 * |K| + 2 * √(216 / π) * (377 + 147 * |d₁| + 32 * |d₂|)) /
          (((2 * m + 1 : ℕ) : ℝ) ^ 3 * √((2 * m + 1 : ℕ) : ℝ)) := by
  intro m hm hmj
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = ((2 * m + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hN : (1 : ℝ) ≤ N := by
    rw [hNdef]; exact_mod_cast (show 1 ≤ 2 * m + 1 by omega)
  have hN0 : 0 < N := by linarith
  have hD : ((2 * m + 2 : ℕ) : ℝ) = N + 1 := by rw [hNdef]; push_cast; ring
  have h1 := hodd m hmj
  rw [hD] at h1
  have hodd' : |((slopeQ (2 * m + 1) : ℚ) : ℝ) -
      sig (N + 1) * (1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2)| ≤ |K| / (N ^ 3 * √N) :=
    (h1.trans (div_le_div_of_nonneg_right (le_abs_self K) (by positivity))).trans
      (remainder_mono hN 3 (abs_nonneg K))
  have hcore := transfer_core hN ((slopeQ (2 * m + 1) : ℚ) : ℝ)
    (1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2)
    (1 + (d₁ - 9 / 2) / N + (d₂ - 11 / 2 * d₁ + 123 / 8) / N ^ 2)
  have hratio := ratio_bound_two hN d₁ d₂
  have hσ := sig_nonneg N
  have hsN : 0 < √N := sqrt_pos.mpr hN0
  rw [slopeQ_even_cast hm, ← hNdef]
  calc |2 * N ^ 2 / ((N + 1) * (N + 3)) * ((slopeQ (2 * m + 1) : ℚ) : ℝ) -
        2 * sig N * (1 + (d₁ - 9 / 2) / N + (d₂ - 11 / 2 * d₁ + 123 / 8) / N ^ 2)|
      ≤ 2 * |((slopeQ (2 * m + 1) : ℚ) : ℝ) -
          sig (N + 1) * (1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2)| +
        2 * sig N * |N ^ 2 / ((N + 1) * (N + 3)) * (1 + d₁ / (N + 1) + d₂ / (N + 1) ^ 2) *
          √(N / (N + 1)) -
          (1 + (d₁ - 9 / 2) / N + (d₂ - 11 / 2 * d₁ + 123 / 8) / N ^ 2)| := hcore
    _ ≤ 2 * (|K| / (N ^ 3 * √N)) +
        2 * sig N * ((377 + 147 * |d₁| + 32 * |d₂|) / N ^ 3) :=
        add_le_add (mul_le_mul_of_nonneg_left hodd' (by norm_num))
          (mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num) hσ))
    _ = (2 * |K| + 2 * √(216 / π) * (377 + 147 * |d₁| + 32 * |d₂|)) / (N ^ 3 * √N) := by
        rw [sig_eq hN0]
        field_simp

/-- Exact rational arithmetic of the coefficients (Manuscript 15, Theorem 7.4 and the new
corollary).  With `λ₂ = 1/5`, `λ₃ = 8/105` and the normalised Gaussian moments
`𝒢(y⁴) = 15/4`, `𝒢(y⁶) = 105/8`, `𝒢(y⁸) = 945/16`:
`c₁ = -3/4`, `c₂ = 29/160`; `d₁ = -15/4`, `d₂ = 1829/160`; `e₁ = -33/4`, `e₂ = 7589/160`,
and the two transfer formulas (from the `d_j` and directly from the `c_j`) agree. -/
theorem coefficient_arithmetic :
    let c₁ : ℚ := -(1 / 5) * (15 / 4)
    let c₂ : ℚ := -(8 / 105) * (105 / 8) + (1 / 5) ^ 2 / 2 * (945 / 16)
    let d₁ : ℚ := -3 + c₁
    let d₂ : ℚ := 15 / 2 - 5 * c₁ + c₂
    c₁ = -3 / 4 ∧ c₂ = 29 / 160 ∧ d₁ = -15 / 4 ∧ d₂ = 1829 / 160 ∧
    d₁ - 9 / 2 = -33 / 4 ∧ d₂ - 11 / 2 * d₁ + 123 / 8 = 7589 / 160 ∧
    -15 / 2 + c₁ = -33 / 4 ∧ 315 / 8 - 21 / 2 * c₁ + c₂ = 7589 / 160 := by
  norm_num

/-- **Even-order central slopes, second-order coefficients.**  If the odd slopes satisfy the
second-order expansion of Manuscript 15, Theorem 7.4 (`d₁ = -15/4`, `d₂ = 1829/160`), then
`|t_n - 2 √(216/(πN)) (1 - 33/(4N) + 7589/(160 N²))| ≤ K' N^(-7/2)`, `N = n + 1`. -/
theorem even_slope_second_order_coefficients (K : ℝ) (j₀ : ℕ)
    (hodd : ∀ j : ℕ, j₀ ≤ j →
      |((slopeQ (2 * j + 1) : ℚ) : ℝ) - √(216 / (π * ((2 * j + 2 : ℕ) : ℝ))) *
          (1 + (-15 / 4) / ((2 * j + 2 : ℕ) : ℝ) +
            (1829 / 160) / ((2 * j + 2 : ℕ) : ℝ) ^ 2)| ≤
        K / (((2 * j + 2 : ℕ) : ℝ) ^ 3 * √((2 * j + 2 : ℕ) : ℝ))) :
    ∀ m : ℕ, 2 ≤ m → j₀ ≤ m →
      |((slopeQ (2 * m) : ℚ) : ℝ) - 2 * √(216 / (π * ((2 * m + 1 : ℕ) : ℝ))) *
          (1 - 33 / (4 * ((2 * m + 1 : ℕ) : ℝ)) +
            7589 / (160 * ((2 * m + 1 : ℕ) : ℝ) ^ 2))| ≤
        (2 * |K| + 2 * √(216 / π) * 1295) /
          (((2 * m + 1 : ℕ) : ℝ) ^ 3 * √((2 * m + 1 : ℕ) : ℝ)) := by
  intro m hm hmj
  have h := even_slope_second_order_of_odd (-15 / 4) (1829 / 160) K j₀ hodd m hm hmj
  have hN0 : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have e : (1 : ℝ) + (-15 / 4 - 9 / 2) / ((2 * m + 1 : ℕ) : ℝ) +
      (1829 / 160 - 11 / 2 * (-15 / 4) + 123 / 8) / ((2 * m + 1 : ℕ) : ℝ) ^ 2 =
      1 - 33 / (4 * ((2 * m + 1 : ℕ) : ℝ)) + 7589 / (160 * ((2 * m + 1 : ℕ) : ℝ) ^ 2) := by
    field_simp
    ring
  rw [e] at h
  refine h.trans (div_le_div_of_nonneg_right ?_ (by positivity))
  have h1 : |(-15 / 4 : ℝ)| = 15 / 4 := by rw [abs_of_neg (by norm_num)]; norm_num
  have h2 : |(1829 / 160 : ℝ)| = 1829 / 160 := abs_of_pos (by norm_num)
  rw [h1, h2]
  have hs : 0 ≤ √(216 / π) := sqrt_nonneg _
  nlinarith

#print axioms rho_bounds
#print axioms transfer_core
#print axioms ratio_bound_one
#print axioms ratio_bound_two
#print axioms even_slope_asymp
#print axioms even_slope_second_order_of_odd
#print axioms coefficient_arithmetic
#print axioms even_slope_second_order_coefficients
end PrivateApex
