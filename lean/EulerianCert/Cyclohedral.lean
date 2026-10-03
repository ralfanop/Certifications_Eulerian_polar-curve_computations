/-
# Cyclohedral manuscript (V500): exact algebraic facts

Companion to R. Alfano, *Cyclohedral zeta targets, Cassini spectral bridges, and Chebyshev
strong-cycle realisations* (manuscript V500). Numbers refer to the V500 PDF.

Certified here:
* Corollary 3.1, proof: the factorisation `2 - 3ω + ω³ = (ω-1)²(ω+2)`, the closed form
  `Ẑ = 8(ω+2)/(ω(ω+1)²)` (Eqs. (28)-(32)), the value `Ẑ(0) = 6` (Eq. (33)), the branch condition
  `Re(1-4q) > 0` on `|q| < 1/4` (Eq. (24)), and the zero-free property (Eqs. (34)-(35)).
* Eq. (76): `T₂(ω) = 1 - 8q` whenever `ω² = 1 - 4q` (the cyclohedral branch is the principal
  order-two Chebyshev branch).
* Proposition 4.1: the characteristic polynomial of `A_c(θ)` (Eq. (56)) and the chain (55).
* Eq. (58): `M₂(e^{iθ}) = A_{1/2}(θ)ᵀ`.
* Corollary 4.5: Chebyshev composition `T_{ab} = T_a ∘ T_b = T_b ∘ T_a` and, for `a = 2`,
  `T_{2m} - 1 = 2(T_m - 1)(T_m + 1)`, `T_{2m} + 1 = 2T_m²` (the factorisations behind (82)-(83)).
* Proposition 4.6: the Riemann–Hurwitz count and the node count give the same genus
  `⌊(n-1)²/2⌋` (Eqs. (93) and (95) and the node-count check).

The spectral, covering and analytic statements themselves (Voronin universality, Brualdi sets,
monodromy, Jordan structure) are not formalised; see `numerics/v500_certificates.py`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.Norm

namespace EulerianCert.Cyclohedral

open Polynomial Complex

/-! ## Corollary 3.1 -/

/-- Eq. (29): `2 - 3ω + ω³ = (ω - 1)²(ω + 2)`. -/
theorem tail_numerator_factor (ω : ℂ) : 2 - 3 * ω + ω ^ 3 = (ω - 1) ^ 2 * (ω + 2) := by ring

/-- Eqs. (28)-(32): with `q = (1 - ω²)/4`, the normalised tail `(1/ω - 1 - 2q)/q²` equals
`8(ω+2)/(ω(ω+1)²)`, for `ω ∉ {0, ±1}`. -/
theorem zhat_closed_form (ω : ℂ) (h0 : ω ≠ 0) (h1 : ω - 1 ≠ 0) (h2 : ω + 1 ≠ 0) :
    (1 / ω - 1 - 2 * ((1 - ω ^ 2) / 4)) / ((1 - ω ^ 2) / 4) ^ 2
      = 8 * (ω + 2) / (ω * (ω + 1) ^ 2) := by
  have hq : (1 - ω ^ 2) ≠ 0 := by
    have : 1 - ω ^ 2 = -((ω - 1) * (ω + 1)) := by ring
    rw [this, neg_ne_zero]; exact mul_ne_zero h1 h2
  field_simp
  ring

/-- Eq. (33): the closed form takes the removable value `6` at `ω = 1` (`q = 0`). -/
theorem zhat_at_origin : (8 : ℂ) * (1 + 2) / (1 * (1 + 1) ^ 2) = 6 := by norm_num

/-- Eq. (24): on `|q| < 1/4`, `1 - 4q` lies in the open right half-plane. -/
theorem branch_right_half_plane (q : ℂ) (hq : ‖q‖ < 1 / 4) : 0 < (1 - 4 * q).re := by
  have h := Complex.re_le_norm q
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re]
  norm_num
  linarith

/-- Eqs. (34)-(35): if `Re ω > 0` then `ω ≠ 0, -1, -2` and the closed form does not vanish. -/
theorem zhat_zero_free (ω : ℂ) (h : 0 < ω.re) :
    ω ≠ 0 ∧ ω + 1 ≠ 0 ∧ ω + 2 ≠ 0 ∧ 8 * (ω + 2) / (ω * (ω + 1) ^ 2) ≠ 0 := by
  have h0 : ω ≠ 0 := fun e => by simp [e] at h
  have h1 : ω + 1 ≠ 0 := fun e => by
    have := congrArg Complex.re e; simp at this; linarith
  have h2 : ω + 2 ≠ 0 := fun e => by
    have := congrArg Complex.re e; simp at this; linarith
  refine ⟨h0, h1, h2, ?_⟩
  exact div_ne_zero (mul_ne_zero (by norm_num) h2) (mul_ne_zero h0 (pow_ne_zero 2 h1))

/-! ## Eq. (76): the cyclohedral branch is the order-two Chebyshev branch -/

/-- Eq. (76): if `ω² = 1 - 4q` then `T₂(ω) = 1 - 8q`. -/
theorem cyclohedral_spectral_link (q ω : ℂ) (h : ω ^ 2 = 1 - 4 * q) :
    (Chebyshev.T ℂ 2).eval ω = 1 - 8 * q := by
  simp only [Chebyshev.T_two, eval_sub, eval_mul, eval_pow, eval_X, eval_one, eval_ofNat]
  rw [h]; ring

/-! ## Proposition 4.1 and Eq. (58) -/

lemma inv_sqrt_two_sq : ((1 / Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 1 / 2 := by
  have : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  rw [← Complex.ofReal_pow, this]; norm_num

/-- The matrix `A_c(θ)` of Eq. (53). -/
noncomputable def A (c θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((1 / Real.sqrt 2 : ℝ) : ℂ), (Real.sqrt c : ℂ) * Complex.exp (θ * Complex.I);
     (Real.sqrt c : ℂ), -((1 / Real.sqrt 2 : ℝ) : ℂ)]

/-- Eq. (56): `det[ξI - A_c(θ)] = ξ² - 1/2 - c e^{iθ}` for `c ≥ 0`. -/
theorem charpoly_A (c θ : ℝ) (hc : 0 ≤ c) (ξ : ℂ) :
    Matrix.det (ξ • (1 : Matrix (Fin 2) (Fin 2) ℂ) - A c θ)
      = ξ ^ 2 - 1 / 2 - c * Complex.exp (θ * Complex.I) := by
  have hs : ((Real.sqrt c : ℝ) : ℂ) * (Real.sqrt c : ℂ) = c := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  rw [Matrix.det_fin_two]
  simp [A, Matrix.sub_apply, Matrix.smul_apply]
  have h2 := inv_sqrt_two_sq
  simp only [one_div, Complex.ofReal_inv] at h2
  linear_combination -h2 - Complex.exp (θ * Complex.I) * hs

/-- Eq. (55): `det = 0 ⇔ T₂(ξ) = 2c e^{iθ} ⇔ ξ²/2 = (1/2)(1/2 + c e^{iθ})`. -/
theorem cassini_chain (c θ : ℝ) (hc : 0 ≤ c) (ξ : ℂ) :
    (Matrix.det (ξ • (1 : Matrix (Fin 2) (Fin 2) ℂ) - A c θ) = 0 ↔
      (Chebyshev.T ℂ 2).eval ξ = 2 * c * Complex.exp (θ * Complex.I)) ∧
    ((Chebyshev.T ℂ 2).eval ξ = 2 * c * Complex.exp (θ * Complex.I) ↔
      ξ ^ 2 / 2 = 1 / 2 * (1 / 2 + c * Complex.exp (θ * Complex.I))) := by
  rw [charpoly_A c θ hc]
  simp only [Chebyshev.T_two, eval_sub, eval_mul, eval_pow, eval_X, eval_one, eval_ofNat]
  constructor
  · constructor
    · intro h; linear_combination (2 : ℂ) * h
    · intro h; linear_combination (1 / 2 : ℂ) * h
  · constructor
    · intro h; linear_combination (1 / 4 : ℂ) * h
    · intro h; linear_combination (4 : ℂ) * h

/-- The order-two strong-cycle matrix `M₂(w)` of Eq. (64), with `α₁ = cos(π/4)`,
`α₂ = cos(3π/4)`, `r₂ = 2^{-1/2}`. -/
noncomputable def M2 (w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (Real.pi / 4) : ℂ), ((2 : ℝ) ^ (-(1 : ℝ) / 2) : ℝ);
     (((2 : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * w, (Real.cos (3 * Real.pi / 4) : ℂ)]

/-- Eq. (58): `M₂(e^{iθ}) = A_{1/2}(θ)ᵀ`. -/
theorem M2_eq_A_half_transpose (θ : ℝ) :
    M2 (Complex.exp (θ * Complex.I)) = (A (1 / 2) θ).transpose := by
  have hcos : Real.cos (Real.pi / 4) = 1 / Real.sqrt 2 := by
    rw [Real.cos_pi_div_four]
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hcos3 : Real.cos (3 * Real.pi / 4) = -(1 / Real.sqrt 2) := by
    have : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
    rw [this, Real.cos_pi_sub, hcos]
  have hr : (2 : ℝ) ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt 2 := by
    have e : (-(1 : ℝ) / 2) = -(1 / 2) := by ring
    rw [e, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow]
    exact (one_div _).symm
  unfold M2
  rw [hcos, hcos3, hr]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, Matrix.transpose_apply, mul_comm]

/-! ## Corollary 4.5: Chebyshev composition and the a = 2 factorisations -/

/-- Composition law used in Corollary 4.5: `T_{ab} = T_a ∘ T_b = T_b ∘ T_a`. -/
theorem cheb_composition (R : Type*) [CommRing R] (a b : ℤ) :
    Chebyshev.T R (a * b) = (Chebyshev.T R a).comp (Chebyshev.T R b) ∧
    Chebyshev.T R (a * b) = (Chebyshev.T R b).comp (Chebyshev.T R a) := by
  refine ⟨Chebyshev.T_mul R a b, ?_⟩
  rw [mul_comm]; exact Chebyshev.T_mul R b a

/-- The `a = 2` case of Corollary 4.5 (Eqs. (82)-(83)): `T_{2m} - 1 = 2(T_m - 1)(T_m + 1)` and
`T_{2m} + 1 = 2 T_m²`. -/
theorem cheb_even_factorisations (R : Type*) [CommRing R] (m : ℤ) :
    Chebyshev.T R (2 * m) - 1 = 2 * (Chebyshev.T R m - 1) * (Chebyshev.T R m + 1) ∧
    Chebyshev.T R (2 * m) + 1 = 2 * Chebyshev.T R m ^ 2 := by
  have h : Chebyshev.T R (2 * m) = 2 * Chebyshev.T R m ^ 2 - 1 := by
    rw [Chebyshev.T_mul, Chebyshev.T_two]; simp [sub_comp, mul_comp, pow_comp]
  constructor <;> rw [h] <;> ring

/-! ## Proposition 4.6: genus by Riemann–Hurwitz and by node count -/

/-- Total ramification `R_n` of Eq. (95). -/
def ramification (n : ℕ) : ℕ := n * (n - 1) + (if n % 2 = 1 then n - 1 else n - 2)

/-- Riemann–Hurwitz, Eq. (95): `2g - 2 = -2n + R_n` with `g = ⌊(n-1)²/2⌋`, for `n ≥ 2`. -/
theorem riemann_hurwitz_genus (n : ℕ) (hn : 2 ≤ n) :
    ramification n + 2 = 2 * n + 2 * ((n - 1) ^ 2 / 2) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · -- n = 2k, k ≥ 1
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have e1 : (2 * (j + 1)) % 2 = 0 := by omega
    have e2 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
    have e3 : 2 * (j + 1) - 2 = 2 * j := by omega
    simp only [ramification, e1, e2, e3, Nat.zero_ne_one, ↓reduceIte]
    have : (2 * j + 1) ^ 2 / 2 = 2 * j * j + 2 * j := by
      have : (2 * j + 1) ^ 2 = 2 * (2 * j * j + 2 * j) + 1 := by ring
      omega
    rw [this]; ring
  · -- n = 2k + 1, k ≥ 1
    have e1 : (2 * k + 1) % 2 = 1 := by omega
    have e2 : 2 * k + 1 - 1 = 2 * k := by omega
    simp only [ramification, e1, e2, ↓reduceIte]
    have : (2 * k) ^ 2 / 2 = 2 * k * k := by
      have : (2 * k) ^ 2 = 2 * (2 * k * k) := by ring
      omega
    rw [this]; ring

/-- Node count: `N = r₊² + r₋²` with `r₊ = ⌊(n-1)/2⌋`, `r₋ = ⌈(n-1)/2⌉`, and
`(n-1)² - N = ⌊(n-1)²/2⌋`, for every `n`. -/
theorem node_count_genus (n : ℕ) :
    let rp := (n - 1) / 2
    let rm := (n - 1 + 1) / 2
    rp ^ 2 + rm ^ 2 + (n - 1) ^ 2 / 2 = (n - 1) ^ 2 := by
  intro rp rm
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (n - 1)
  · have h1 : rp = k := by simp only [rp]; omega
    have h2 : rm = k := by simp only [rm]; omega
    rw [h1, h2, hk]
    have : (2 * k) ^ 2 / 2 = 2 * k * k := by
      have : (2 * k) ^ 2 = 2 * (2 * k * k) := by ring
      omega
    rw [this]; ring
  · have h1 : rp = k := by simp only [rp]; omega
    have h2 : rm = k + 1 := by simp only [rm]; omega
    rw [h1, h2, hk]
    have : (2 * k + 1) ^ 2 / 2 = 2 * k * k + 2 * k := by
      have : (2 * k + 1) ^ 2 = 2 * (2 * k * k + 2 * k) + 1 := by ring
      omega
    rw [this]; ring

end EulerianCert.Cyclohedral
