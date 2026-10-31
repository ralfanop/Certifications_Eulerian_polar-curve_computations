import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Section 8: an Eulerian entire function in the Rabotnov family

Manuscript V173, Proposition 8.1 (printed (170)–(173)).

`F_E(z) = z r_E(i√z) = 2√z sinh(√z/2) = z + ∑_{n≥2} z^n/(4^{n-1}(2n-1)!)` is defined by its power
series. We prove
* the closed form `F_E(w²) = 2w sinh(w/2)` for every complex `w` (so the square root is only apparent);
* `F_E` is the member `κ = 1`, `β = 1/4` of the normalised Rabotnov family
  `𝕽_{κ,β}(z) = ∑_{k≥0} β^k Γ(1+κ)/Γ((k+1)(1+κ)) z^{k+1}` (Eker–Ece; Altınkaya);
* convexity on the unit disk *from* the published criterion of Eker and Ece
  [Hacet. J. Math. Stat. 51 (2022), Theorem 2.8], which enters as an explicit hypothesis;
* the values `F_E(π²) = 2π sinh(π/2)`, `F_E(-π²) = -2π`, and their ratio `sinh(π/2) = r_E(iπ)/r_E(π)`.
-/

open Complex

namespace EulerianBridge.Rabotnov

/-- Coefficients of `F_E`: `c n = 1/(4^{n-1}(2n-1)!)` for `n ≥ 1`, `c 0 = 0`. -/
noncomputable def c (n : ℕ) : ℂ := if n = 0 then 0 else 1 / (4 ^ (n - 1) * ((2 * n - 1).factorial : ℂ))

/-- `F_E(z) = ∑ c_n z^n`. -/
noncomputable def FE (z : ℂ) : ℂ := ∑' n : ℕ, c n * z ^ n

theorem c_zero : c 0 = 0 := by simp [c]

/-- The normalised Rabotnov coefficients (Eker–Ece): `a_{k+1} = β^k Γ(1+κ)/Γ((k+1)(1+κ))`. -/
noncomputable def rabotnovCoeff (κ β : ℝ) (k : ℕ) : ℝ :=
  β ^ k * Real.Gamma (1 + κ) / Real.Gamma ((k + 1) * (1 + κ))

/-- `F_E` is the normalised Rabotnov function with `κ = 1`, `β = 1/4`: its coefficients agree. -/
theorem c_eq_rabotnov (k : ℕ) : c (k + 1) = (rabotnovCoeff 1 (1 / 4) k : ℂ) := by
  unfold c rabotnovCoeff
  rw [if_neg (Nat.succ_ne_zero k)]
  have h1 : Real.Gamma (1 + 1) = 1 := by
    rw [show (1:ℝ) + 1 = ((1:ℕ):ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; simp
  have h2 : Real.Gamma (((k:ℝ) + 1) * (1 + 1)) = ((2 * k + 1).factorial : ℝ) := by
    rw [show ((k:ℝ) + 1) * (1 + 1) = ((2 * k + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  rw [h1, h2, show 2 * (k + 1) - 1 = 2 * k + 1 by omega, show k + 1 - 1 = k by omega]
  push_cast
  rw [div_pow, one_pow]
  field_simp

/-- The series `∑ (w/2)^{2n+1}/(2n+1)! = sinh(w/2)`. -/
theorem hasSum_sinh_half (w : ℂ) :
    HasSum (fun n : ℕ => (w / 2) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℂ)) (Complex.sinh (w / 2)) :=
  Complex.hasSum_sinh (w / 2)

/-- Closed form: `F_E(w²) = 2w sinh(w/2)` (eq. (170)). -/
theorem FE_sq (w : ℂ) : HasSum (fun n => c n * (w ^ 2) ^ n) (2 * w * Complex.sinh (w / 2)) := by
  have h := (hasSum_sinh_half w).mul_left (2 * w)
  -- reindex n ↦ n+1; the n = 0 term of the c-series vanishes
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, c_zero, zero_mul, sub_zero]
  convert h using 1
  funext n
  unfold c
  rw [if_neg (Nat.succ_ne_zero n), show 2 * (n + 1) - 1 = 2 * n + 1 by omega,
    show n + 1 - 1 = n by omega]
  rw [div_pow, ← pow_mul, show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
  have h4 : (2:ℂ) ^ (2 * n + 1) = 2 * 4 ^ n := by
    rw [pow_succ, pow_mul]; norm_num; ring
  rw [h4]
  have hf : ((2 * n + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h4' : (4:ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

theorem FE_eq_sq (w : ℂ) : FE (w ^ 2) = 2 * w * Complex.sinh (w / 2) := (FE_sq w).tsum_eq

/-- Eq. (171): `F_E(π²) = 2π sinh(π/2)`. -/
theorem FE_pi_sq : FE ((Real.pi : ℂ) ^ 2) = 2 * Real.pi * Complex.sinh (Real.pi / 2) := by
  rw [FE_eq_sq]

/-- Eq. (172): `F_E(-π²) = -2π`. -/
theorem FE_neg_pi_sq : FE (-((Real.pi : ℂ) ^ 2)) = -2 * Real.pi := by
  have : -((Real.pi : ℂ) ^ 2) = ((Real.pi : ℂ) * I) ^ 2 := by rw [mul_pow, I_sq]; ring
  rw [this, FE_eq_sq, show (Real.pi : ℂ) * I / 2 = (Real.pi / 2 : ℂ) * I by ring, Complex.sinh_mul_I,
    show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sin,
    Real.sin_pi_div_two]
  push_cast
  ring_nf
  rw [I_sq]; ring

/-- Eq. (173): `F_E(π²)/(-F_E(-π²)) = sinh(π/2)`, and `r_E(iπ)/r_E(π) = sinh(π/2)` with
`r_E(π) = 2/π`, `r_E(iπ) = sinh(π/2)/(π/2)`. -/
theorem FE_ratio :
    FE ((Real.pi : ℂ) ^ 2) / (-FE (-((Real.pi : ℂ) ^ 2))) = Complex.sinh (Real.pi / 2) ∧
      (Real.sinh (Real.pi / 2) / (Real.pi / 2)) / (2 / Real.pi) = Real.sinh (Real.pi / 2) := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine ⟨?_, ?_⟩
  · rw [FE_pi_sq, FE_neg_pi_sq]; field_simp
  · have := Real.pi_ne_zero; field_simp

/-! ## Convexity from the published Eker–Ece criterion -/

/-- Convexity of a normalised analytic function on the unit disk: `Re(1 + z f''(z)/f'(z)) > 0`. -/
def ConvexOnUnitDisk (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ < 1 → 0 < (1 + z * deriv (deriv f) z / deriv f z).re

/-- The power series with coefficients `rabotnovCoeff κ β`. -/
noncomputable def rabotnovFun (κ β : ℝ) (z : ℂ) : ℂ := ∑' k : ℕ, (rabotnovCoeff κ β k : ℂ) * z ^ (k + 1)

/-- Eker–Ece, Theorem 2.8 (cited input, not re-proved): the normalised Rabotnov function with
`κ ≥ 0`, `β > 0` and `β/(1+κ) < 0.199496` is convex on the unit disk. -/
def EkerEceCriterion : Prop :=
  ∀ κ β : ℝ, 0 ≤ κ → 0 < β → β / (1 + κ) < 0.199496 → ConvexOnUnitDisk (rabotnovFun κ β)

theorem FE_eq_rabotnovFun : FE = rabotnovFun 1 (1 / 4) := by
  funext z
  unfold FE rabotnovFun
  rw [tsum_eq_zero_add']
  · simp only [c_zero, zero_mul, zero_add]
    congr 1; funext k; rw [c_eq_rabotnov]
  · -- summability: `z = w²` with `w = z^{1/2}`, and the series of `F_E(w²)` converges
    have hz : (z ^ ((2:ℕ)⁻¹ : ℂ)) ^ 2 = z := Complex.cpow_nat_inv_pow z (by norm_num)
    have hs := (FE_sq (z ^ ((2:ℕ)⁻¹ : ℂ))).summable
    rw [hz] at hs
    exact (summable_nat_add_iff (f := fun n : ℕ => c n * z ^ n) 1).mpr hs

/-- Proposition 8.1, convexity: `F_E` is convex on the unit disk, given the Eker–Ece criterion. -/
theorem FE_convex (h : EkerEceCriterion) : ConvexOnUnitDisk FE := by
  rw [FE_eq_rabotnovFun]
  exact h 1 (1 / 4) (by norm_num) (by norm_num) (by norm_num)

end EulerianBridge.Rabotnov
