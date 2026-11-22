import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
PRIVATE.  Manuscript 15: Eulerian Fourier reconstruction of the Mandelbrot cardioid.
Algebraic and analytic identities.

With `u = exp (θ * I)` the boundary of the main cardioid of the Mandelbrot set is
`cardioid θ = u / 2 - u ^ 2 / 4`.  This file proves

* `cardioid_sub_quarter`, `cardioid_eulerian`: `cardioid θ - 1/4 = -(u - 1)^2 / 4
  = (θ^2 / 4) * rE θ ^ 2 * exp (θ * I)`, where `rE θ = sinc (θ / 2)` is the Eulerian Fourier kernel;
* `eulerianB_exp`, `cardioid_eulerianB`, `rhoE_sq_mul`, `rhoE_sq_mul_neg_pi`, `rhoPole_sq_mul`:
  the same identity in terms of the Eulerian factor `B(u) = (u - 1) / log u` and of the poles
  `ρ_j(u) = (log u + 2 π i j) / (u - 1)`, with the principal branch of the logarithm;
* `one_sub_four_cardioid`, `re_one_sub_exp_nonneg`, `one_sub_exp_eq_eulerianB`: the relation
  `√(1 - 4 c(θ)) = 1 - e^{iθ} = -iθ B(e^{iθ})` with the Catalan square root;
* `cardioid_special_point`, `special_point_unique`: the normalisation by `z0 = I / √2`;
* `cardioid_zero`, `cardioid_pi`, `rE_pi`, `fixed_point`, `multiplier`, `period_two_factor`,
  `period_doubling`, `hasDerivAt_cardioid`, `cardioid_polar`, `norm_cardioid_sub`,
  `cusp_quotient`, `cusp_quotient_tendsto`: the special values at `θ = 0` and `θ = π`.
-/

namespace PrivateApex
namespace Cardioid
open Complex
open scoped Real Topology

/-- Boundary of the main cardioid, parametrised by the multiplier `u = exp (θ * I)`. -/
noncomputable def cardioid (θ : ℝ) : ℂ := exp (θ * I) / 2 - exp (θ * I) ^ 2 / 4

/-- The Eulerian Fourier kernel `r_E(θ) = sin (θ / 2) / (θ / 2)`, with value `1` at `θ = 0`. -/
noncomputable def rE (θ : ℝ) : ℝ := Real.sinc (θ / 2)

theorem rE_zero : rE 0 = 1 := by simp [rE]

theorem half_mul_rE (θ : ℝ) : θ / 2 * rE θ = Real.sin (θ / 2) := by
  unfold rE
  by_cases h : θ / 2 = 0
  · simp [h]
  · have hθ : θ ≠ 0 := fun h' => h (by simp [h'])
    rw [Real.sinc_of_ne_zero h]; field_simp

/-- `r_E` is nonnegative on `[-2π, 2π]`. -/
theorem rE_nonneg {θ : ℝ} (h1 : -(2 * π) ≤ θ) (h2 : θ ≤ 2 * π) : 0 ≤ rE θ := by
  unfold rE
  by_cases h : θ / 2 = 0
  · simp [h]
  · rw [Real.sinc_of_ne_zero h]
    rcases lt_or_gt_of_ne h with hneg | hpos
    · exact div_nonneg_of_nonpos
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le hneg.le (by linarith)) hneg.le
    · exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hpos.le (by linarith)) hpos.le

theorem exp_half_sq (θ : ℝ) :
    exp ((θ : ℂ) * I) = exp (((θ / 2 : ℝ) : ℂ) * I) * exp (((θ / 2 : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem exp_half_sq' (θ : ℝ) :
    exp ((θ : ℂ) * I) = exp (((θ / 2 : ℝ) : ℂ) * I) ^ 2 := by
  rw [sq]; exact exp_half_sq θ

/-- `e^{iθ} - 1 = 2 i sin (θ/2) e^{iθ/2}`. -/
theorem exp_sub_one (θ : ℝ) :
    exp ((θ : ℂ) * I) - 1 =
      2 * I * (Real.sin (θ / 2) : ℂ) * exp (((θ / 2 : ℝ) : ℂ) * I) := by
  have hinv : exp (-(((θ / 2 : ℝ) : ℂ)) * I) * exp (((θ / 2 : ℝ) : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]; simp
  have hI : I * I = -1 := Complex.I_mul_I
  rw [Complex.ofReal_sin, Complex.sin, exp_half_sq]
  linear_combination
    (-(exp (-(((θ / 2 : ℝ) : ℂ)) * I) * exp (((θ / 2 : ℝ) : ℂ) * I)) +
      exp (((θ / 2 : ℝ) : ℂ) * I) * exp (((θ / 2 : ℝ) : ℂ) * I)) * hI + hinv

theorem sin_half_cast (θ : ℝ) : (Real.sin (θ / 2) : ℂ) = (θ : ℂ) / 2 * (rE θ : ℂ) := by
  rw [← half_mul_rE]; push_cast; ring

/-- `(e^{iθ} - 1)^2 = -θ^2 r_E(θ)^2 e^{iθ}`. -/
theorem exp_sub_one_sq (θ : ℝ) :
    (exp ((θ : ℂ) * I) - 1) ^ 2 = -((θ : ℂ) ^ 2 * (rE θ : ℂ) ^ 2 * exp ((θ : ℂ) * I)) := by
  have hI : I * I = -1 := Complex.I_mul_I
  rw [exp_sub_one, sin_half_cast, exp_half_sq θ]
  linear_combination
    ((θ : ℂ) ^ 2 * (rE θ : ℂ) ^ 2 * exp (((θ / 2 : ℝ) : ℂ) * I) *
      exp (((θ / 2 : ℝ) : ℂ) * I)) * hI

/-- First fundamental identity: `c(θ) - 1/4 = -(u - 1)^2 / 4`. -/
theorem cardioid_sub_quarter (θ : ℝ) :
    cardioid θ - 1 / 4 = -(exp ((θ : ℂ) * I) - 1) ^ 2 / 4 := by
  unfold cardioid; ring

/-- Second fundamental identity: `c(θ) - 1/4 = (θ^2 / 4) r_E(θ)^2 e^{iθ}`. -/
theorem cardioid_eulerian (θ : ℝ) :
    cardioid θ - 1 / 4 = (θ : ℂ) ^ 2 / 4 * (rE θ : ℂ) ^ 2 * exp ((θ : ℂ) * I) := by
  rw [cardioid_sub_quarter, exp_sub_one_sq]; ring

/-! ### The Eulerian factor and the dominant singularity -/

/-- The Eulerian factor `B(u) = (u - 1) / log u` (principal branch), with `B(1) = 1`. -/
noncomputable def eulerianB (u : ℂ) : ℂ := if u = 1 then 1 else (u - 1) / log u

/-- The dominant singularity `ρ(u) = log u / (u - 1)` (principal branch), with `ρ(1) = 1`. -/
noncomputable def rhoE (u : ℂ) : ℂ := if u = 1 then 1 else log u / (u - 1)

/-- The full family of poles `ρ_j(u) = (log u + 2 π i j) / (u - 1)`. -/
noncomputable def rhoPole (j : ℤ) (u : ℂ) : ℂ := (log u + 2 * π * I * j) / (u - 1)

theorem eulerianB_of_ne {u : ℂ} (hu : u ≠ 1) : eulerianB u = (u - 1) / log u := by
  simp [eulerianB, hu]

theorem rhoE_of_ne {u : ℂ} (hu : u ≠ 1) : rhoE u = log u / (u - 1) := by
  simp [rhoE, hu]

theorem rhoPole_zero {u : ℂ} (hu : u ≠ 1) : rhoPole 0 u = rhoE u := by
  simp [rhoPole, rhoE, hu]

theorem log_exp_theta {θ : ℝ} (h1 : -π < θ) (h2 : θ ≤ π) :
    log (exp ((θ : ℂ) * I)) = (θ : ℂ) * I := by
  apply Complex.log_exp <;> simpa using by assumption

theorem exp_ne_one {θ : ℝ} (h1 : -π < θ) (h2 : θ ≤ π) (h0 : θ ≠ 0) :
    exp ((θ : ℂ) * I) ≠ 1 := by
  intro h
  have hlog := log_exp_theta h1 h2
  rw [h, Complex.log_one] at hlog
  have : (θ : ℂ) = 0 := by
    rcases mul_eq_zero.mp hlog.symm with h' | h'
    · exact h'
    · exact absurd h' Complex.I_ne_zero
  exact h0 (by exact_mod_cast this)

private theorem key_quotient (a b : ℂ) (hb : b ≠ 0) :
    (a / b) ^ 2 * (-b ^ 2 / 4) = -a ^ 2 / 4 := by
  field_simp

/-- Third fundamental identity, principal branch: for `-π < θ ≤ π`,
`ρ(e^{iθ})^2 (c(θ) - 1/4) = θ^2 / 4`; at `θ = 0` the value `ρ(1) = 1` is the removable one. -/
theorem rhoE_sq_mul {θ : ℝ} (h1 : -π < θ) (h2 : θ ≤ π) :
    rhoE (exp ((θ : ℂ) * I)) ^ 2 * (cardioid θ - 1 / 4) = (θ : ℂ) ^ 2 / 4 := by
  by_cases h0 : θ = 0
  · subst h0; simp [rhoE, cardioid]; norm_num
  · have hne := exp_ne_one h1 h2 h0
    rw [rhoE_of_ne hne, log_exp_theta h1 h2, cardioid_sub_quarter,
      key_quotient _ _ (sub_ne_zero.mpr hne), mul_pow, I_sq]
    ring

/-- The same identity at the other endpoint `θ = -π`, where `e^{-iπ} = -1` and the principal
value of the logarithm is `iπ`: the squared identity holds on the closed interval `[-π, π]`. -/
theorem rhoE_sq_mul_neg_pi :
    rhoE (exp (((-π : ℝ) : ℂ) * I)) ^ 2 * (cardioid (-π) - 1 / 4) = ((-π : ℝ) : ℂ) ^ 2 / 4 := by
  have h : exp (((-π : ℝ) : ℂ) * I) = -1 := by
    push_cast
    rw [neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  have hne : (-1 : ℂ) ≠ 1 := by norm_num
  unfold cardioid
  rw [h, rhoE_of_ne hne, Complex.log_neg_one]
  push_cast
  have hI : I ^ 2 = -1 := I_sq
  field_simp
  linear_combination (-8 : ℂ) * hI

/-- For `θ` in the `j`-th window `(2j-1)π < θ ≤ (2j+1)π`, the pole `ρ_j` plays the role of the
dominant singularity: `ρ_j(e^{iθ})^2 (c(θ) - 1/4) = θ^2 / 4` whenever `e^{iθ} ≠ 1`. -/
theorem rhoPole_sq_mul (j : ℤ) {θ : ℝ} (h1 : -π < θ - 2 * π * j) (h2 : θ - 2 * π * j ≤ π)
    (hne : exp ((θ : ℂ) * I) ≠ 1) :
    rhoPole j (exp ((θ : ℂ) * I)) ^ 2 * (cardioid θ - 1 / 4) = (θ : ℂ) ^ 2 / 4 := by
  have hper : exp ((θ : ℂ) * I) = exp (((θ - 2 * π * j : ℝ) : ℂ) * I) := by
    have : (θ : ℂ) * I = ((θ - 2 * π * j : ℝ) : ℂ) * I + (j : ℂ) * (2 * π * I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hlog : log (exp ((θ : ℂ) * I)) + 2 * π * I * j = (θ : ℂ) * I := by
    rw [hper, log_exp_theta h1 h2]; push_cast; ring
  rw [rhoPole, hlog, cardioid_sub_quarter, key_quotient _ _ (sub_ne_zero.mpr hne), mul_pow, I_sq]
  ring

/-- On the unit circle, principal range, `B(e^{iθ}) = e^{iθ/2} r_E(θ)`. -/
theorem eulerianB_exp {θ : ℝ} (h1 : -π < θ) (h2 : θ ≤ π) :
    eulerianB (exp ((θ : ℂ) * I)) = exp (((θ / 2 : ℝ) : ℂ) * I) * (rE θ : ℂ) := by
  by_cases h0 : θ = 0
  · subst h0; simp [eulerianB, rE]
  · have hne := exp_ne_one h1 h2 h0
    have hθ : (θ : ℂ) ≠ 0 := by exact_mod_cast h0
    rw [eulerianB_of_ne hne, log_exp_theta h1 h2, exp_sub_one, sin_half_cast]
    field_simp

/-- `|B(e^{iθ})| = r_E(θ)` on the principal range: the polar profile of Flajolet and Sedgewick. -/
theorem norm_eulerianB_exp {θ : ℝ} (h1 : -π < θ) (h2 : θ ≤ π) :
    ‖eulerianB (exp ((θ : ℂ) * I))‖ = rE θ := by
  rw [eulerianB_exp h1 h2, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (rE_nonneg (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))]

/-- The cardioid from the squared Eulerian factor: `c(θ) - 1/4 = (θ^2 / 4) B(e^{iθ})^2`. -/
theorem cardioid_eulerianB {θ : ℝ} (h1 : -π < θ) (h2 : θ ≤ π) :
    cardioid θ - 1 / 4 = (θ : ℂ) ^ 2 / 4 * eulerianB (exp ((θ : ℂ) * I)) ^ 2 := by
  rw [cardioid_eulerian, eulerianB_exp h1 h2, mul_pow, exp_half_sq θ]; ring

/-- `1 - 4 c(θ) = (1 - e^{iθ})^2`: the cardioid is the boundary of the region
`|1 - √(1 - 4 z)| ≤ 1` of Flajolet and Sedgewick. -/
theorem one_sub_four_cardioid (θ : ℝ) :
    1 - 4 * cardioid θ = (1 - exp ((θ : ℂ) * I)) ^ 2 := by
  unfold cardioid; ring

/-- `Re (1 - e^{iθ}) ≥ 0`, so that `1 - e^{iθ}` is the principal square root of
`1 - 4 c(θ)`. -/
theorem re_one_sub_exp_nonneg (θ : ℝ) : 0 ≤ (1 - exp ((θ : ℂ) * I)).re := by
  rw [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re]
  linarith [Real.cos_le_one θ]

/-- `√(1 - 4 c(θ)) = 1 - e^{iθ} = -iθ B(e^{iθ})` on the principal range. -/
theorem one_sub_exp_eq_eulerianB {θ : ℝ} (h1 : -π < θ) (h2 : θ ≤ π) :
    1 - exp ((θ : ℂ) * I) = -((θ : ℂ) * I) * eulerianB (exp ((θ : ℂ) * I)) := by
  by_cases h0 : θ = 0
  · subst h0; simp
  · have hne := exp_ne_one h1 h2 h0
    have hθ : (θ : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast h0) I_ne_zero
    have hB : (θ : ℂ) * I * ((exp ((θ : ℂ) * I) - 1) / ((θ : ℂ) * I)) =
        exp ((θ : ℂ) * I) - 1 := by
      have hθ' : (θ : ℂ) ≠ 0 := by exact_mod_cast h0
      field_simp
    rw [eulerianB_of_ne hne, log_exp_theta h1 h2]
    linear_combination hB

/-! ### The special point `z0 = i / √2` -/

/-- The special point `z0 = i / √2`. -/
noncomputable def z0 : ℂ := I / (Real.sqrt 2 : ℂ)

theorem z0_sq : z0 ^ 2 = -1 / 2 := by
  unfold z0
  rw [div_pow, I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- `c(θ) - 1/4 = (z0^2 / 2) (e^{iθ} - 1)^2`. -/
theorem cardioid_special_point (θ : ℝ) :
    cardioid θ - 1 / 4 = z0 ^ 2 / 2 * (exp ((θ : ℂ) * I) - 1) ^ 2 := by
  rw [cardioid_sub_quarter, z0_sq]; ring

/-- The normalisation only sees `z0^2`: a complex number `ζ` gives the same identity at one
point with `e^{iθ} ≠ 1` exactly when `ζ = ± z0`. -/
theorem special_point_unique (ζ : ℂ) {θ : ℝ} (hne : exp ((θ : ℂ) * I) ≠ 1)
    (h : cardioid θ - 1 / 4 = ζ ^ 2 / 2 * (exp ((θ : ℂ) * I) - 1) ^ 2) : ζ = z0 ∨ ζ = -z0 := by
  have hb : (exp ((θ : ℂ) * I) - 1) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hne)
  rw [cardioid_special_point] at h
  have h2 : ζ ^ 2 = z0 ^ 2 := by
    have := mul_right_cancel₀ hb h
    linear_combination (-2 : ℂ) * this
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h2

/-! ### Special values -/

theorem cardioid_zero : cardioid 0 = 1 / 4 := by
  simp [cardioid]; norm_num

theorem cardioid_pi : cardioid π = -3 / 4 := by
  simp [cardioid, Complex.exp_pi_mul_I]; norm_num

theorem rE_pi : rE π = 2 / π := by
  unfold rE
  rw [Real.sinc_of_ne_zero (by positivity), Real.sin_pi_div_two]
  field_simp

/-- The point `e^{iθ} / 2` is a fixed point of `w ↦ w^2 + c(θ)`. -/
theorem fixed_point (θ : ℝ) :
    (exp ((θ : ℂ) * I) / 2) ^ 2 + cardioid θ = exp ((θ : ℂ) * I) / 2 := by
  unfold cardioid; ring

/-- Its multiplier is `e^{iθ}`: `1` at the cusp (parabolic), `-1` at `θ = π`. -/
theorem multiplier (θ : ℝ) :
    HasDerivAt (fun w : ℂ => w ^ 2 + cardioid θ) (exp ((θ : ℂ) * I))
      (exp ((θ : ℂ) * I) / 2) := by
  have h := (hasDerivAt_pow 2 (exp ((θ : ℂ) * I) / 2)).add_const (cardioid θ)
  convert h using 1
  norm_num; ring

theorem multiplier_zero : exp (((0 : ℝ) : ℂ) * I) = 1 := by simp

theorem multiplier_pi : exp (((π : ℝ) : ℂ) * I) = -1 := Complex.exp_pi_mul_I

/-- Points of period dividing two of `w ↦ w^2 + c`: the fixed-point factor and the 2-cycle
factor. -/
theorem period_two_factor (w c : ℂ) :
    (w ^ 2 + c) ^ 2 + c - w = (w ^ 2 - w + c) * (w ^ 2 + w + c + 1) := by ring

/-- At `c(π) = -3/4` the 2-cycle factor is a perfect square: the 2-cycle collapses onto the fixed
point `-1/2` (period-doubling bifurcation). -/
theorem period_doubling (w : ℂ) : w ^ 2 + w + cardioid π + 1 = (w + 1 / 2) ^ 2 := by
  rw [cardioid_pi]; ring

/-- Derivative of the parametrisation: it vanishes exactly when `e^{iθ} = 1`. -/
theorem hasDerivAt_cardioid (θ : ℝ) :
    HasDerivAt cardioid (I / 2 * exp ((θ : ℂ) * I) * (1 - exp ((θ : ℂ) * I))) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I θ := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const I
  have h2 : HasDerivAt (fun t : ℝ => exp ((t : ℂ) * I)) (exp ((θ : ℂ) * I) * I) θ := h1.cexp
  have h3 := (h2.div_const 2).sub ((h2.pow 2).div_const 4)
  unfold cardioid
  convert h3 using 1
  simp; ring

theorem deriv_cardioid_eq_zero_iff (θ : ℝ) :
    I / 2 * exp ((θ : ℂ) * I) * (1 - exp ((θ : ℂ) * I)) = 0 ↔ exp ((θ : ℂ) * I) = 1 := by
  have hI : (I / 2 : ℂ) ≠ 0 := by simp
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' hI
      · exact absurd h'' (Complex.exp_ne_zero _)
    · exact (sub_eq_zero.mp h').symm
  · intro h; rw [h]; ring

/-- Polar form about the cusp: `c(θ) - 1/4 = sin^2(θ/2) e^{iθ}`. -/
theorem cardioid_polar (θ : ℝ) :
    cardioid θ - 1 / 4 = ((Real.sin (θ / 2) ^ 2 : ℝ) : ℂ) * exp ((θ : ℂ) * I) := by
  rw [cardioid_eulerian, Complex.ofReal_pow, sin_half_cast]; ring

theorem cardioid_re (θ : ℝ) : (cardioid θ - 1 / 4).re = Real.sin (θ / 2) ^ 2 * Real.cos θ := by
  rw [cardioid_polar, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem cardioid_im (θ : ℝ) : (cardioid θ - 1 / 4).im = Real.sin (θ / 2) ^ 2 * Real.sin θ := by
  rw [cardioid_polar, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- The cusp-centred radius is the normalised cycloid ordinate `(1 - cos θ) / 2`. -/
theorem norm_cardioid_sub (θ : ℝ) : ‖cardioid θ - 1 / 4‖ = (1 - Real.cos θ) / 2 := by
  rw [cardioid_polar, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg _), Real.sin_sq_eq_half_sub]
  ring_nf

/-- The distance from the cusp `1/4` to the period-doubling point `-3/4` is
`1 = ((π / 2) r_E(π))^2`. -/
theorem cusp_distance : ‖cardioid π - 1 / 4‖ = 1 := by
  rw [norm_cardioid_sub, Real.cos_pi]; norm_num

theorem cusp_distance_rE : ‖cardioid π - 1 / 4‖ = (π / 2 * rE π) ^ 2 := by
  rw [cusp_distance, rE_pi]
  have : π / 2 * (2 / π) = 1 := by field_simp
  rw [this]; norm_num

/-- Exact cusp quotient: `Im^2 cos^3 θ = 4 cos^2(θ/2) Re^3`. -/
theorem cusp_quotient (θ : ℝ) :
    (cardioid θ - 1 / 4).im ^ 2 * Real.cos θ ^ 3 =
      4 * Real.cos (θ / 2) ^ 2 * (cardioid θ - 1 / 4).re ^ 3 := by
  rw [cardioid_re, cardioid_im]
  have h : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; congr 1; ring
  rw [h]; ring

/-- The cusp at `θ = 0` is semicubical: `Im^2 / Re^3 → 4`. -/
theorem cusp_quotient_tendsto :
    Filter.Tendsto (fun θ : ℝ => (cardioid θ - 1 / 4).im ^ 2 / (cardioid θ - 1 / 4).re ^ 3)
      (𝓝[≠] 0) (𝓝 4) := by
  have hcont : Filter.Tendsto (fun θ : ℝ => 4 * Real.cos (θ / 2) ^ 2 / Real.cos θ ^ 3)
      (𝓝[≠] 0) (𝓝 4) := by
    have hc : ContinuousAt (fun θ : ℝ => 4 * Real.cos (θ / 2) ^ 2 / Real.cos θ ^ 3) 0 := by
      have h0 : Real.cos (0 : ℝ) ^ 3 ≠ 0 := by simp
      fun_prop (disch := exact h0)
    have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    have h4 : 4 * Real.cos ((0 : ℝ) / 2) ^ 2 / Real.cos 0 ^ 3 = 4 := by simp
    rw [h4] at ht
    exact ht
  refine hcont.congr' ?_
  have hpos : ∀ᶠ θ : ℝ in 𝓝[≠] 0, θ ∈ Set.Ioo (-1 : ℝ) 1 ∧ θ ≠ 0 := by
    refine Filter.Eventually.and ?_ (eventually_mem_nhdsWithin)
    exact nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hpos] with θ ⟨⟨h1, h2⟩, h0⟩
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.two_le_pi], by linarith [Real.two_le_pi]⟩
  have hsin : Real.sin (θ / 2) ≠ 0 := by
    rcases lt_or_gt_of_ne h0 with hneg | hp
    · exact (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith [Real.two_le_pi])).ne
    · exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.two_le_pi])).ne'
  have hre : (cardioid θ - 1 / 4).re ^ 3 ≠ 0 := by
    rw [cardioid_re]; exact pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hsin) hcos.ne')
  have hq := cusp_quotient θ
  rw [div_eq_div_iff (pow_ne_zero _ hcos.ne') hre]
  linarith

end Cardioid
end PrivateApex
