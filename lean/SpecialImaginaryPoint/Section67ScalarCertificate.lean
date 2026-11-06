import Mathlib

/-!
# Manuscript 14, Sections 6 and 7: the scalar certificate

This module kernel-checks the scalar content of Sections 6 and 7 of manuscript 14
("Eulerian Fourier profiles at the special point i/√2").

* Lemma 7.1: `z₀ = i/√2` is the unique point of the upper half-plane with `-1/τ = 2τ`;
  `2 z₀² + 1 = 0`, `S z₀ = z₁ = 2 z₀`, `S z₁ = z₀`, and `r_E(z₁) - r_E(z₀) > 0`.
* Theorem 7.2: the modular duplication (91) `r_E(S z₀) = r_E(z₁) = cosh(1/√8) r_E(z₀)`,
  the factorisation (92) of the Euler product over the spectrum `{π²n²/4}` of `A₂`
  into the products over the spectra `{π²n²}` of `A` and `{π²(n-1/2)²}` of `A_DN`,
  the companion form (93), the duplications (94)–(96) of the Langevin function, of the
  Langevin variance and of the resolvent traces, and the explicit companion values.
* Proposition 6.2, scalar form: the Euler products (13)–(14), `sinh x / x = ∏ (1 + x²/(π²n²))`
  and `cosh x = ∏ (1 + x²/(π²(n-1/2)²))`, as the products (71)–(72) over the spectra
  (68) and (70), hence (73).
* Proposition 6.3 and Corollary 6.4, scalar form: (74)–(76) and (81)–(82) as identities of
  the spectral sums over `{π²n²}` and `{π²(n-1/2)²}`, the special values (77) and (79),
  and the Hilbert–Schmidt identity (83)–(84).

The operators of Definition 6.1 enter only through their spectra (68) and (70), which are
classical inputs; the identification of a Fredholm determinant of a positive trace-class
operator with the product over its spectrum, and of a trace with the sum over its
spectrum, is likewise an input and is not formalised here.  The zeta-regularised
determinants are not formalised.

Conventions: `rE z = 2 sin(z/2)/z` with `rE 0 = 1`; `a = 1/√8`, `b = 1/√2 = 2a`;
`Lval x = coth x - 1/x` is the Langevin function and `Vval x = 1/x² - 1/sinh² x` its
derivative, the Langevin variance; `TD x = ∑ₙ (π²(n+1)² + x²)⁻¹`,
`TDN x = ∑ₙ (π²(n+1/2)² + x²)⁻¹`, `QD x = ∑ₙ (π²(n+1)² + x²)⁻²` (indices from 0).
-/

open Filter Topology
open scoped Real

noncomputable section

namespace Manuscript14Section67

/-! ## Definitions -/

/-- The Eulerian profile `r_E(z) = 2 sin(z/2)/z`, `r_E(0) = 1`. -/
def rE (z : ℂ) : ℂ := if z = 0 then 1 else 2 * Complex.sin (z / 2) / z

/-- The coupling `a = 1/√8`. -/
def a : ℝ := 1 / Real.sqrt 8

/-- The companion coupling `b = 1/√2`. -/
def b : ℝ := 1 / Real.sqrt 2

/-- The special point `z₀ = i/√2`. -/
def z0 : ℂ := Complex.I / ((Real.sqrt 2 : ℝ) : ℂ)

/-- The companion point `z₁ = i√2`. -/
def z1 : ℂ := Complex.I * ((Real.sqrt 2 : ℝ) : ℂ)

/-- The modular inversion `S(τ) = -1/τ`. -/
def S (τ : ℂ) : ℂ := -1 / τ

/-- The Langevin function `coth x - 1/x`. -/
def Lval (x : ℝ) : ℝ := Real.cosh x / Real.sinh x - x⁻¹

/-- The Langevin variance `1/x² - 1/sinh² x`, the derivative of `Lval`. -/
def Vval (x : ℝ) : ℝ := (x ^ 2)⁻¹ - (Real.sinh x ^ 2)⁻¹

/-- The `n`-th resolvent eigenvalue `(π²(n+1)² + x²)⁻¹` of the Dirichlet Laplacian. -/
def tdTerm (x : ℝ) (n : ℕ) : ℝ := (π ^ 2 * ((n : ℝ) + 1) ^ 2 + x ^ 2)⁻¹

/-- The `n`-th resolvent eigenvalue `(π²(n+1/2)² + x²)⁻¹` of the Dirichlet–Neumann Laplacian. -/
def tdnTerm (x : ℝ) (n : ℕ) : ℝ := (π ^ 2 * ((n : ℝ) + 1 / 2) ^ 2 + x ^ 2)⁻¹

/-- The square `(π²(n+1)² + x²)⁻²` of the Dirichlet resolvent eigenvalue. -/
def qdTerm (x : ℝ) (n : ℕ) : ℝ := ((π ^ 2 * ((n : ℝ) + 1) ^ 2 + x ^ 2) ^ 2)⁻¹

/-- `Tr (A + x²)⁻¹` as the sum over the spectrum `{π²n²}`. -/
def TD (x : ℝ) : ℝ := ∑' n : ℕ, tdTerm x n

/-- `Tr (A_DN + x²)⁻¹` as the sum over the spectrum `{π²(n-1/2)²}`. -/
def TDN (x : ℝ) : ℝ := ∑' n : ℕ, tdnTerm x n

/-- `Tr (A + x²)⁻²` as the sum over the spectrum `{π²n²}`. -/
def QD (x : ℝ) : ℝ := ∑' n : ℕ, qdTerm x n

/-- The Euler factor `1 + x²/(π²(n+1)²)` over the Dirichlet spectrum. -/
def sinhFac (x : ℝ) (n : ℕ) : ℝ := 1 + x ^ 2 / (π ^ 2 * ((n : ℝ) + 1) ^ 2)

/-- The Euler factor `1 + x²/(π²(n+1/2)²)` over the Dirichlet–Neumann spectrum. -/
def coshFac (x : ℝ) (n : ℕ) : ℝ := 1 + x ^ 2 / (π ^ 2 * ((n : ℝ) + 1 / 2) ^ 2)

/-! ## The constants `a` and `b` -/

theorem sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem sqrt_eight : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num) 2,
    Real.sqrt_sq (by norm_num)]

theorem a_eq : a = 1 / (2 * Real.sqrt 2) := by
  show 1 / Real.sqrt 8 = _
  rw [sqrt_eight]

theorem a_pos : 0 < a := by
  rw [a_eq]
  have := sqrt_two_pos
  positivity

theorem a_ne_zero : a ≠ 0 := a_pos.ne'

theorem a_sq : a ^ 2 = 1 / 8 := by
  rw [a_eq, div_pow, mul_pow, sqrt_two_sq]
  norm_num

theorem b_eq_two_mul_a : b = 2 * a := by
  have hs : Real.sqrt 2 ≠ 0 := sqrt_two_pos.ne'
  rw [a_eq]
  show 1 / Real.sqrt 2 = _
  first
    | (rw [mul_one_div, div_mul_cancel_left₀ (two_ne_zero : (2 : ℝ) ≠ 0), one_div]; done)
    | (field_simp; done)
    | (field_simp; ring)

theorem b_pos : 0 < b := by
  rw [b_eq_two_mul_a]
  linarith [a_pos]

theorem b_ne_zero : b ≠ 0 := b_pos.ne'

theorem b_sq : b ^ 2 = 1 / 2 := by
  rw [b_eq_two_mul_a, mul_pow, a_sq]
  norm_num

theorem one_div_a : 1 / a = Real.sqrt 8 := by
  show 1 / (1 / Real.sqrt 8) = _
  rw [one_div_one_div]

theorem one_div_b : 1 / b = Real.sqrt 2 := by
  show 1 / (1 / Real.sqrt 2) = _
  rw [one_div_one_div]

theorem two_a_sqrt_two : 2 * a * Real.sqrt 2 = 1 := by
  have hs : Real.sqrt 2 ≠ 0 := sqrt_two_pos.ne'
  rw [a_eq]
  first
    | (field_simp; done)
    | (field_simp; ring)
    | (rw [mul_one_div, div_mul_cancel_left₀ (two_ne_zero : (2 : ℝ) ≠ 0), inv_mul_cancel₀ hs])

theorem two_b : 2 * b = Real.sqrt 2 := by
  have hs : Real.sqrt 2 ≠ 0 := sqrt_two_pos.ne'
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  show 2 * (1 / Real.sqrt 2) = Real.sqrt 2
  rw [mul_one_div, div_eq_iff hs, h2]

/-! ## The points `z₀`, `z₁` and Lemma 7.1 -/

theorem sqrt_two_ne_zero_c : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr sqrt_two_pos.ne'

theorem sqrt_two_sq_c : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  have h := sqrt_two_sq
  exact_mod_cast h

theorem z0_eq : z0 = 2 * ((a : ℂ) * Complex.I) := by
  have hs := sqrt_two_ne_zero_c
  rw [a_eq]
  push_cast
  show Complex.I / ((Real.sqrt 2 : ℝ) : ℂ) = _
  first
    | ring
    | (field_simp; done)
    | (field_simp; ring)

theorem z1_eq_two_mul_z0 : z1 = 2 * z0 := by
  have hs := sqrt_two_ne_zero_c
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← sq]
    exact sqrt_two_sq_c
  show Complex.I * ((Real.sqrt 2 : ℝ) : ℂ) = 2 * (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ))
  calc Complex.I * ((Real.sqrt 2 : ℝ) : ℂ)
      = ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) *
          (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ)) := by
        rw [mul_assoc, mul_div_cancel₀ _ hs]
        ring
    _ = 2 * (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ)) := by rw [h2]

theorem z1_eq : z1 = 2 * ((b : ℂ) * Complex.I) := by
  rw [z1_eq_two_mul_z0, z0_eq, b_eq_two_mul_a]
  push_cast
  ring

theorem z0_ne_zero : z0 ≠ 0 := by
  rw [z0_eq]
  exact mul_ne_zero two_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr a_ne_zero) Complex.I_ne_zero)

theorem z1_ne_zero : z1 ≠ 0 := by
  rw [z1_eq_two_mul_z0]
  exact mul_ne_zero two_ne_zero z0_ne_zero

theorem z0_im : z0.im = 2 * a := by
  rw [z0_eq]
  first
    | (simp; done)
    | (simp; ring)

theorem z0_im_pos : 0 < z0.im := by
  rw [z0_im]
  linarith [a_pos]

/-- `z₀` satisfies the primitive quadratic equation `2τ² + 1 = 0` of discriminant `-8`. -/
theorem quadratic_z0 : 2 * z0 ^ 2 + 1 = 0 := by
  show 2 * (Complex.I / ((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 + 1 = 0
  rw [div_pow, Complex.I_sq, sqrt_two_sq_c]
  norm_num

/-- **Lemma 7.1** (uniqueness): `z₀` is the unique `τ` with `Im τ > 0` and `-1/τ = 2τ`. -/
theorem S_eq_two_mul_iff (τ : ℂ) (hτ : 0 < τ.im) : S τ = 2 * τ ↔ τ = z0 := by
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_im] at hτ
    exact lt_irrefl 0 hτ
  constructor
  · intro h
    have h0 : -1 / τ = 2 * τ := h
    have h1 : 2 * τ ^ 2 + 1 = 0 := by
      have h' : -1 = 2 * τ * τ := (div_eq_iff hτ0).mp h0
      linear_combination -h'
    have h2 : (τ - z0) * (τ + z0) = 0 := by
      linear_combination (1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * quadratic_z0
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exfalso
      have h4 : τ = -z0 := by linear_combination h3
      have h5 : τ.im = -z0.im := by rw [h4, Complex.neg_im]
      linarith [z0_im_pos]
  · rintro rfl
    show -1 / z0 = 2 * z0
    rw [div_eq_iff z0_ne_zero]
    linear_combination -quadratic_z0

/-- **Lemma 7.1**, (89): `S z₀ = z₁ = 2 z₀`. -/
theorem S_z0 : S z0 = z1 := by
  rw [(S_eq_two_mul_iff z0 z0_im_pos).mpr rfl, z1_eq_two_mul_z0]

/-- **Lemma 7.1**, (89): `S z₁ = z₀`. -/
theorem S_z1 : S z1 = z0 := by
  show -1 / (Complex.I * ((Real.sqrt 2 : ℝ) : ℂ)) = Complex.I / ((Real.sqrt 2 : ℝ) : ℂ)
  rw [div_eq_div_iff (mul_ne_zero Complex.I_ne_zero sqrt_two_ne_zero_c) sqrt_two_ne_zero_c,
    ← mul_assoc, Complex.I_mul_I]

/-! ## The Eulerian profile on the imaginary axis and the modular duplication -/

/-- The duplication identity of the profile, `r_E(2z) = cos(z/2) r_E(z)`. -/
theorem rE_two_mul (z : ℂ) : rE (2 * z) = Complex.cos (z / 2) * rE z := by
  by_cases hz : z = 0
  · subst hz
    simp [rE]
  · have h2z : (2 : ℂ) * z ≠ 0 := mul_ne_zero two_ne_zero hz
    have hs : Complex.sin (2 * z / 2) = 2 * Complex.sin (z / 2) * Complex.cos (z / 2) := by
      rw [← Complex.sin_two_mul]
      congr 1
      ring
    simp only [rE, if_neg h2z, if_neg hz]
    rw [hs, mul_div_mul_left _ _ (two_ne_zero : (2 : ℂ) ≠ 0)]
    ring

/-- On the imaginary axis, `r_E(2ix) = sinh x / x`. -/
theorem rE_two_mul_I (x : ℝ) (hx : x ≠ 0) :
    rE (2 * ((x : ℂ) * Complex.I)) = ((Real.sinh x / x : ℝ) : ℂ) := by
  have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have hz : (2 : ℂ) * ((x : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero two_ne_zero (mul_ne_zero hx' Complex.I_ne_zero)
  simp only [rE, if_neg hz]
  rw [mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℂ) ≠ 0), Complex.sin_mul_I,
    mul_div_mul_left _ _ (two_ne_zero : (2 : ℂ) ≠ 0),
    mul_div_mul_right _ _ Complex.I_ne_zero, Complex.ofReal_div, Complex.ofReal_sinh]

/-- `r_E(z₀) = sinh(a)/a`. -/
theorem rE_z0 : rE z0 = ((Real.sinh a / a : ℝ) : ℂ) := by
  rw [z0_eq]
  exact rE_two_mul_I a a_ne_zero

/-- `r_E(z₁) = sinh(b)/b`. -/
theorem rE_z1 : rE z1 = ((Real.sinh b / b : ℝ) : ℂ) := by
  rw [z1_eq]
  exact rE_two_mul_I b b_ne_zero

/-- **Theorem 7.2**, (91), with the coupling `a`. -/
theorem modular_duplication :
    rE (S z0) = rE z1 ∧ rE z1 = ((Real.cosh a : ℝ) : ℂ) * rE z0 := by
  refine ⟨by rw [S_z0], ?_⟩
  rw [z1_eq_two_mul_z0, rE_two_mul, z0_eq,
    mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℂ) ≠ 0), Complex.cos_mul_I, Complex.ofReal_cosh]

/-- **Theorem 7.2**, (91), as displayed: `r_E(S z₀) = r_E(z₁) = cosh(1/√8) r_E(z₀)`. -/
theorem eq91 :
    rE (S z0) = rE z1 ∧ rE z1 = ((Real.cosh (1 / Real.sqrt 8) : ℝ) : ℂ) * rE z0 :=
  modular_duplication

/-- **Lemma 7.1**, (90): the Eulerian difference `r_E(z₁) - r_E(z₀) = (cosh a - 1) sinh(a)/a`
is real and strictly positive. -/
theorem pair_difference :
    rE z1 - rE z0 = (((Real.cosh a - 1) * (Real.sinh a / a) : ℝ) : ℂ) ∧
      0 < (Real.cosh a - 1) * (Real.sinh a / a) := by
  refine ⟨?_, ?_⟩
  · rw [modular_duplication.2, rE_z0]
    push_cast
    ring
  · apply mul_pos
    · have := Real.one_lt_cosh.mpr a_ne_zero
      linarith
    · exact div_pos (Real.sinh_pos_iff.mpr a_pos) a_pos

/-! ## The Langevin function, its derivative and their duplications -/

/-- The duplication of the Langevin function, `2 L(2x) = L(x) + tanh x`. -/
theorem langevin_dup (x : ℝ) (hx : x ≠ 0) : 2 * Lval (2 * x) = Lval x + Real.tanh x := by
  have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  simp only [Lval, Real.cosh_two_mul, Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
  first
    | (field_simp; ring)
    | (field_simp; done)

/-- The Langevin variance is the derivative of the Langevin function. -/
theorem hasDerivAt_Lval (x : ℝ) (hx : x ≠ 0) : HasDerivAt Lval (Vval x) x := by
  have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
  have h := ((Real.hasDerivAt_cosh x).fun_div (Real.hasDerivAt_sinh x) hs).fun_sub
    (hasDerivAt_inv hx)
  refine h.congr_deriv ?_
  have hcs := Real.cosh_sq_sub_sinh_sq x
  simp only [Vval]
  linear_combination (-(Real.sinh x ^ 2)⁻¹) * hcs

/-- The duplication of the Langevin variance, `4 L'(2x) = L'(x) + sech² x`. -/
theorem var_dup (x : ℝ) (hx : x ≠ 0) : 4 * Vval (2 * x) = Vval x + (Real.cosh x ^ 2)⁻¹ := by
  have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
  have e1 : 4 * Vval (2 * x) = (x ^ 2)⁻¹ - (Real.sinh x ^ 2)⁻¹ * (Real.cosh x ^ 2)⁻¹ := by
    simp only [Vval, Real.sinh_two_mul]
    ring
  have h1 : Real.sinh x ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have h2 : Real.sinh x ^ 2 + 1 ≠ 0 := by positivity
  have e2 : (Real.sinh x ^ 2)⁻¹ - (Real.cosh x ^ 2)⁻¹ =
      (Real.sinh x ^ 2)⁻¹ * (Real.cosh x ^ 2)⁻¹ := by
    rw [Real.cosh_sq x]
    first
      | (rw [inv_sub_inv h1 h2, add_sub_cancel_left, one_div, mul_inv]; done)
      | (field_simp; done)
      | (field_simp; ring)
  rw [e1]
  simp only [Vval]
  linear_combination e2

/-! ## The spectral sums: positivity and summability -/

theorem pos_base (n : ℕ) : 0 < π ^ 2 * ((n : ℝ) + 1) ^ 2 := by positivity

theorem pos_TD (x : ℝ) (n : ℕ) : 0 < π ^ 2 * ((n : ℝ) + 1) ^ 2 + x ^ 2 := by positivity

theorem pos_TDN (x : ℝ) (n : ℕ) : 0 < π ^ 2 * ((n : ℝ) + 1 / 2) ^ 2 + x ^ 2 := by positivity

theorem one_le_D (y : ℝ) (n : ℕ) : 1 ≤ π ^ 2 * ((n : ℝ) + 1) ^ 2 + y ^ 2 := by
  have hπ : 3 < π := Real.pi_gt_three
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hπ2 : 9 ≤ π ^ 2 := by nlinarith
  have hn2 : 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  nlinarith [mul_le_mul hπ2 hn2 (by norm_num) (by positivity), sq_nonneg y]

theorem quarter_le (n : ℕ) :
    π ^ 2 * ((n : ℝ) + 1) ^ 2 / 4 ≤ π ^ 2 * ((n : ℝ) + 1 / 2) ^ 2 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_nonneg (sq_nonneg π) (by positivity : (0 : ℝ) ≤ 3 * (n : ℝ) ^ 2 + 2 * n)]

theorem summable_base : Summable (fun n : ℕ => (π ^ 2 * ((n : ℝ) + 1) ^ 2)⁻¹) := by
  have h : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have h0 : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
      Real.summable_nat_pow_inv.mpr (by norm_num)
    have h1 := (summable_nat_add_iff 1).mpr h0
    simpa [Nat.cast_add, Nat.cast_one] using h1
  exact (h.mul_left ((π ^ 2)⁻¹)).congr (fun n => (mul_inv _ _).symm)

theorem summable_tdTerm (x : ℝ) : Summable (tdTerm x) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) summable_base
  · unfold tdTerm
    exact (inv_pos.mpr (pos_TD x n)).le
  · unfold tdTerm
    exact inv_anti₀ (pos_base n) (le_add_of_nonneg_right (sq_nonneg x))

theorem summable_tdnTerm (x : ℝ) : Summable (tdnTerm x) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_base.mul_left 4)
  · unfold tdnTerm
    exact (inv_pos.mpr (pos_TDN x n)).le
  · unfold tdnTerm
    have h0 : 0 < π ^ 2 * ((n : ℝ) + 1) ^ 2 / 4 := by positivity
    have hle : π ^ 2 * ((n : ℝ) + 1) ^ 2 / 4 ≤ π ^ 2 * ((n : ℝ) + 1 / 2) ^ 2 + x ^ 2 :=
      (quarter_le n).trans (le_add_of_nonneg_right (sq_nonneg x))
    calc (π ^ 2 * ((n : ℝ) + 1 / 2) ^ 2 + x ^ 2)⁻¹
        ≤ (π ^ 2 * ((n : ℝ) + 1) ^ 2 / 4)⁻¹ := inv_anti₀ h0 hle
      _ = 4 * (π ^ 2 * ((n : ℝ) + 1) ^ 2)⁻¹ := by rw [inv_div, div_eq_mul_inv]

theorem summable_qdTerm (x : ℝ) : Summable (qdTerm x) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_tdTerm x)
  · unfold qdTerm
    exact (inv_pos.mpr (pow_pos (pos_TD x n) 2)).le
  · unfold qdTerm tdTerm
    have hD := pos_TD x n
    have h1 := one_le_D x n
    exact inv_anti₀ hD (by nlinarith [mul_nonneg hD.le (sub_nonneg.mpr h1)])

/-! ## Proposition 6.3: the traces as sums over the spectra -/

theorem div_mul_I (p q : ℂ) : p / (q * Complex.I) = -(p / q * Complex.I) := by
  rw [div_mul_eq_div_div, Complex.div_I]

theorem pair_term (z m : ℂ) (h1 : z - m ≠ 0) (h2 : z + m ≠ 0) :
    1 / (z - m) + 1 / (z + m) = 2 * z / (z ^ 2 - m ^ 2) := by
  rw [div_add_div _ _ h1 h2]
  ring

theorem imag_term (u : ℝ) (n : ℕ) :
    2 * ((u : ℂ) * Complex.I) / (((u : ℂ) * Complex.I) ^ 2 - ((n : ℂ) + 1) ^ 2) =
      -(((2 * u / (u ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) * Complex.I) := by
  rw [mul_pow, Complex.I_sq,
    show (u : ℂ) ^ 2 * -1 - ((n : ℂ) + 1) ^ 2 = -((u : ℂ) ^ 2 + ((n : ℂ) + 1) ^ 2) by ring,
    div_neg]
  push_cast
  ring

theorem real_term (x : ℝ) (n : ℕ) :
    2 * (x / π) / ((x / π) ^ 2 + ((n : ℝ) + 1) ^ 2) = 2 * π * x * tdTerm x n := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hD : π ^ 2 * ((n : ℝ) + 1) ^ 2 + x ^ 2 ≠ 0 := (pos_TD x n).ne'
  have hE : (x / π) ^ 2 + ((n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
  unfold tdTerm
  first
    | (field_simp; ring)
    | (field_simp; done)

/-- **Proposition 6.3**, (74) and (81): `L(x) = 2x ∑ₙ 1/(π²n² + x²)` for `x > 0`, from the
Mittag-Leffler expansion of the cotangent at the imaginary point `ix/π`. -/
theorem trace_master (x : ℝ) (hx : 0 < x) : Lval x = 2 * x * TD x := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = x / π := ⟨_, rfl⟩
  have hu_pos : 0 < u := by
    rw [hu]
    exact div_pos hx Real.pi_pos
  have hmem : ((u : ℂ) * Complex.I) ∈ Complex.integerComplement := by
    have him : 0 < ((u : ℂ) * Complex.I).im := by simpa using hu_pos
    exact UpperHalfPlane.coe_mem_integerComplement ⟨_, him⟩
  have h := cot_series_rep' hmem
  have hπu : (π : ℂ) * ((u : ℂ) * Complex.I) = (x : ℂ) * Complex.I := by
    rw [← mul_assoc, ← Complex.ofReal_mul, hu, mul_div_cancel₀ _ hπ]
  have hL : (π : ℂ) * Complex.cot ((π : ℂ) * ((u : ℂ) * Complex.I)) - 1 / ((u : ℂ) * Complex.I) =
      -(((π * Lval x : ℝ) : ℂ) * Complex.I) := by
    rw [hπu, Complex.cot_eq_cos_div_sin, Complex.cos_mul_I, Complex.sin_mul_I, div_mul_I,
      div_mul_I, hu]
    simp only [Lval]
    push_cast
    first
      | ring
      | (field_simp; ring)
  have hR : ∀ n : ℕ, 1 / ((u : ℂ) * Complex.I - ((n : ℂ) + 1)) +
      1 / ((u : ℂ) * Complex.I + ((n : ℂ) + 1)) =
      -(((2 * π * x * tdTerm x n : ℝ) : ℂ) * Complex.I) := by
    intro n
    have h1 : (u : ℂ) * Complex.I - ((n : ℂ) + 1) ≠ 0 := by
      intro h0
      have h0' := congrArg Complex.im h0
      simp at h0'
      linarith
    have h2 : (u : ℂ) * Complex.I + ((n : ℂ) + 1) ≠ 0 := by
      intro h0
      have h0' := congrArg Complex.im h0
      simp at h0'
      linarith
    rw [pair_term _ _ h1 h2, imag_term u n, hu, real_term x n]
  have hT : (∑' n : ℕ, 2 * π * x * tdTerm x n) = 2 * π * x * TD x := by
    unfold TD
    exact tsum_mul_left
  have hsum : (∑' n : ℕ, (1 / ((u : ℂ) * Complex.I - ((n : ℂ) + 1)) +
      1 / ((u : ℂ) * Complex.I + ((n : ℂ) + 1)))) =
      -(((2 * π * x * TD x : ℝ) : ℂ) * Complex.I) := by
    rw [tsum_congr hR, tsum_neg, tsum_mul_right, ← Complex.ofReal_tsum, hT]
  rw [hL, hsum] at h
  have h' : ((π * Lval x : ℝ) : ℂ) = ((2 * π * x * TD x : ℝ) : ℂ) :=
    mul_right_cancel₀ Complex.I_ne_zero (neg_injective h)
  have h'' : π * Lval x = 2 * π * x * TD x := Complex.ofReal_injective h'
  have h3 : π * Lval x = π * (2 * x * TD x) := by
    rw [h'']
    ring
  exact mul_left_cancel₀ hπ h3

/-- The reflection splitting of the spectral sum: `4 T(2x) = T(x) + T_DN(x)`. -/
theorem trace_split (x : ℝ) : 4 * TD (2 * x) = TD x + TDN x := by
  have hfs : Summable (tdTerm (2 * x)) := summable_tdTerm (2 * x)
  have he : Summable (fun k : ℕ => tdTerm (2 * x) (2 * k)) :=
    hfs.comp_injective (mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0))
  have ho : Summable (fun k : ℕ => tdTerm (2 * x) (2 * k + 1)) :=
    hfs.comp_injective ((add_left_injective 1).comp
      (mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0)))
  have hsplit := tsum_even_add_odd he ho
  have hev : ∀ k : ℕ, 4 * tdTerm (2 * x) (2 * k) = tdnTerm x k := by
    intro k
    simp only [tdTerm, tdnTerm]
    rw [show π ^ 2 * (((2 * k : ℕ) : ℝ) + 1) ^ 2 + (2 * x) ^ 2 =
        4 * (π ^ 2 * ((k : ℝ) + 1 / 2) ^ 2 + x ^ 2) by push_cast; ring,
      mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), one_mul]
  have hod : ∀ k : ℕ, 4 * tdTerm (2 * x) (2 * k + 1) = tdTerm x k := by
    intro k
    simp only [tdTerm]
    rw [show π ^ 2 * (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2 + (2 * x) ^ 2 =
        4 * (π ^ 2 * ((k : ℝ) + 1) ^ 2 + x ^ 2) by push_cast; ring,
      mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), one_mul]
  calc 4 * TD (2 * x) = 4 * ∑' k, tdTerm (2 * x) k := rfl
    _ = 4 * ((∑' k, tdTerm (2 * x) (2 * k)) + ∑' k, tdTerm (2 * x) (2 * k + 1)) := by
        rw [hsplit]
    _ = (∑' k, 4 * tdTerm (2 * x) (2 * k)) + ∑' k, 4 * tdTerm (2 * x) (2 * k + 1) := by
        rw [mul_add, tsum_mul_left, tsum_mul_left]
    _ = TDN x + TD x := by simp only [hev, hod, TDN, TD]
    _ = TD x + TDN x := add_comm _ _

/-- **Proposition 6.3**, (75) and (82): `tanh x = 2x ∑ₙ 1/(π²(n-1/2)² + x²)` for `x > 0`. -/
theorem trace_tanh (x : ℝ) (hx : 0 < x) : Real.tanh x = 2 * x * TDN x := by
  have h1 := langevin_dup x hx.ne'
  have h2 := trace_master x hx
  have h3 := trace_master (2 * x) (by linarith)
  have h4 := trace_split x
  linear_combination -h1 + 2 * h3 - h2 + 2 * x * h4

/-- The sum `T_DN` in the indexing of (82), `∑ₙ 4/(π²(2n-1)² + 4x²)`. -/
theorem TDN_eq (x : ℝ) : TDN x = ∑' n : ℕ, 4 / (π ^ 2 * (2 * (n : ℝ) + 1) ^ 2 + 4 * x ^ 2) := by
  unfold TDN
  refine tsum_congr (fun n => ?_)
  unfold tdnTerm
  rw [show π ^ 2 * ((n : ℝ) + 1 / 2) ^ 2 + x ^ 2 =
      (π ^ 2 * (2 * (n : ℝ) + 1) ^ 2 + 4 * x ^ 2) / 4 by ring, inv_div]

theorem hasDerivAt_tdTerm (n : ℕ) (y : ℝ) :
    HasDerivAt (fun y => tdTerm y n) (-(2 * y) * qdTerm y n) y := by
  have hd : HasDerivAt (fun y : ℝ => π ^ 2 * ((n : ℝ) + 1) ^ 2 + y ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add (π ^ 2 * ((n : ℝ) + 1) ^ 2)
  have h := hd.fun_inv (pos_TD y n).ne'
  refine h.congr_deriv ?_
  unfold qdTerm
  rw [div_eq_mul_inv]

/-- Termwise differentiation of the Dirichlet spectral sum. -/
theorem hasDerivAt_TD (x : ℝ) (hx : 0 < x) : HasDerivAt TD (-(2 * x) * QD x) x := by
  have hu : Summable (fun n : ℕ => 4 * x * (π ^ 2 * ((n : ℝ) + 1) ^ 2)⁻¹) :=
    summable_base.mul_left (4 * x)
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (0 : ℝ) (2 * x) →
      ‖-(2 * y) * qdTerm y n‖ ≤ 4 * x * (π ^ 2 * ((n : ℝ) + 1) ^ 2)⁻¹ := by
    intro n y hy
    obtain ⟨hy0, hy1⟩ := hy
    have hD := pos_TD y n
    have hB := pos_base n
    have hDB : π ^ 2 * ((n : ℝ) + 1) ^ 2 ≤ π ^ 2 * ((n : ℝ) + 1) ^ 2 + y ^ 2 :=
      le_add_of_nonneg_right (sq_nonneg y)
    have hD1 := one_le_D y n
    unfold qdTerm
    have h2y : (0 : ℝ) < 2 * y := by linarith
    have hq : (0 : ℝ) < ((π ^ 2 * ((n : ℝ) + 1) ^ 2 + y ^ 2) ^ 2)⁻¹ := by positivity
    rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h2y, abs_of_pos hq]
    have e1 : ((π ^ 2 * ((n : ℝ) + 1) ^ 2 + y ^ 2) ^ 2)⁻¹ ≤ (π ^ 2 * ((n : ℝ) + 1) ^ 2)⁻¹ := by
      apply inv_anti₀ hB
      nlinarith [mul_nonneg hD.le (sub_nonneg.mpr hD1)]
    calc 2 * y * ((π ^ 2 * ((n : ℝ) + 1) ^ 2 + y ^ 2) ^ 2)⁻¹
        ≤ 2 * y * (π ^ 2 * ((n : ℝ) + 1) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left e1 h2y.le
      _ ≤ 4 * x * (π ^ 2 * ((n : ℝ) + 1) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (by linarith) (inv_pos.mpr hB).le
  have hx_mem : x ∈ Set.Ioo (0 : ℝ) (2 * x) := ⟨hx, by linarith⟩
  have key : HasDerivAt (fun z => ∑' n : ℕ, tdTerm z n) (∑' n : ℕ, -(2 * x) * qdTerm x n) x :=
    hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
      (fun n y _ => hasDerivAt_tdTerm n y) hbound hx_mem (summable_tdTerm x) hx_mem
  have hsum : (∑' n : ℕ, -(2 * x) * qdTerm x n) = -(2 * x) * QD x := by
    unfold QD
    exact tsum_mul_left
  rw [hsum] at key
  exact key

/-- **Proposition 6.3**, (76): `L'(x) = 2 ∑ₙ 1/(π²n² + x²) - 4x² ∑ₙ 1/(π²n² + x²)²`. -/
theorem trace_square (x : ℝ) (hx : 0 < x) : Vval x = 2 * TD x - 4 * x ^ 2 * QD x := by
  have h1 : HasDerivAt (fun y => 2 * y * TD y) (2 * 1 * TD x + 2 * x * (-(2 * x) * QD x)) x :=
    ((hasDerivAt_id' (x := x)).const_mul 2).fun_mul (hasDerivAt_TD x hx)
  have heq : Lval =ᶠ[𝓝 x] (fun y => 2 * y * TD y) :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx) (fun y hy => trace_master y hy)
  have h2 : HasDerivAt Lval (2 * 1 * TD x + 2 * x * (-(2 * x) * QD x)) x :=
    h1.congr_of_eventuallyEq heq
  have h3 := (hasDerivAt_Lval x hx.ne').unique h2
  rw [h3]
  ring

/-! ## The special values of Proposition 6.3 and Corollary 6.4 -/

/-- (77) as a spectral sum: `Tr (8/(8A+I)) = ∑ₙ 8/(8π²n² + 1)`. -/
theorem TD_a_series : TD a = ∑' n : ℕ, 8 / (8 * π ^ 2 * ((n : ℝ) + 1) ^ 2 + 1) := by
  unfold TD
  refine tsum_congr (fun n => ?_)
  unfold tdTerm
  rw [a_sq, show π ^ 2 * ((n : ℝ) + 1) ^ 2 + 1 / 8 =
      (8 * π ^ 2 * ((n : ℝ) + 1) ^ 2 + 1) / 8 by ring, inv_div]

/-- (79) as a spectral sum: `Tr (8/(8A_DN+I)) = ∑ₙ 8/(8π²(n-1/2)² + 1)`. -/
theorem TDN_a_series : TDN a = ∑' n : ℕ, 8 / (8 * π ^ 2 * ((n : ℝ) + 1 / 2) ^ 2 + 1) := by
  unfold TDN
  refine tsum_congr (fun n => ?_)
  unfold tdnTerm
  rw [a_sq, show π ^ 2 * ((n : ℝ) + 1 / 2) ^ 2 + 1 / 8 =
      (8 * π ^ 2 * ((n : ℝ) + 1 / 2) ^ 2 + 1) / 8 by ring, inv_div]

/-- (83) as a spectral sum: `Tr (64/(8A+I)²) = ∑ₙ 64/(8π²n² + 1)²`. -/
theorem QD_a_series : QD a = ∑' n : ℕ, 64 / (8 * π ^ 2 * ((n : ℝ) + 1) ^ 2 + 1) ^ 2 := by
  unfold QD
  refine tsum_congr (fun n => ?_)
  unfold qdTerm
  rw [a_sq, show π ^ 2 * ((n : ℝ) + 1) ^ 2 + 1 / 8 =
      (8 * π ^ 2 * ((n : ℝ) + 1) ^ 2 + 1) / 8 by ring, div_pow, inv_div]
  norm_num

/-- The companion trace `Tr (2/(2A+I)) = ∑ₙ 2/(2π²n² + 1)`. -/
theorem TD_b_series : TD b = ∑' n : ℕ, 2 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2 + 1) := by
  unfold TD
  refine tsum_congr (fun n => ?_)
  unfold tdTerm
  rw [b_sq, show π ^ 2 * ((n : ℝ) + 1) ^ 2 + 1 / 2 =
      (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2 + 1) / 2 by ring, inv_div]

/-- The companion square trace `Tr (4/(2A+I)²) = ∑ₙ 4/(2π²n² + 1)²`. -/
theorem QD_b_series : QD b = ∑' n : ℕ, 4 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2 + 1) ^ 2 := by
  unfold QD
  refine tsum_congr (fun n => ?_)
  unfold qdTerm
  rw [b_sq, show π ^ 2 * ((n : ℝ) + 1) ^ 2 + 1 / 2 =
      (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2 + 1) / 2 by ring, div_pow, inv_div]
  norm_num

/-- **Proposition 6.3**, (77): `Tr (8/(8A+I)) = √2 [coth(a) - √8]`. -/
theorem trace_special : TD a = Real.sqrt 2 * (Real.cosh a / Real.sinh a - Real.sqrt 8) := by
  have h := trace_master a a_pos
  calc TD a = (2 * a * Real.sqrt 2) * TD a := by rw [two_a_sqrt_two, one_mul]
    _ = Real.sqrt 2 * Lval a := by
        rw [h]
        ring
    _ = Real.sqrt 2 * (Real.cosh a / Real.sinh a - Real.sqrt 8) := by
        rw [Lval, ← one_div, one_div_a]

/-- **Proposition 6.3**, (79): `Tr (8/(8A_DN+I)) = √2 tanh(a)`. -/
theorem trace_B_special : TDN a = Real.sqrt 2 * Real.tanh a := by
  have h := trace_tanh a a_pos
  calc TDN a = (2 * a * Real.sqrt 2) * TDN a := by rw [two_a_sqrt_two, one_mul]
    _ = Real.sqrt 2 * Real.tanh a := by
        rw [h]
        ring

/-- **Corollary 6.4**, (83)–(84): `Tr (64/(8A+I)²) = 2 [2 Tr (8/(8A+I)) - L'(a)]`. -/
theorem hs2_special : QD a = 2 * (2 * TD a - Vval a) := by
  have h := trace_square a a_pos
  linear_combination 2 * h - 8 * QD a * a_sq

/-! ## Proposition 6.2: the Euler products over the two spectra -/

theorem summable_sinhFac_sub (x : ℝ) :
    Summable (fun n : ℕ => x ^ 2 / (π ^ 2 * ((n : ℝ) + 1) ^ 2)) :=
  (summable_base.mul_left (x ^ 2)).congr (fun n => (div_eq_mul_inv _ _).symm)

theorem summable_coshFac_sub (x : ℝ) :
    Summable (fun n : ℕ => x ^ 2 / (π ^ 2 * ((n : ℝ) + 1 / 2) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_base.mul_left (4 * x ^ 2))
  have h0 : 0 < π ^ 2 * ((n : ℝ) + 1) ^ 2 / 4 := by positivity
  calc x ^ 2 / (π ^ 2 * ((n : ℝ) + 1 / 2) ^ 2)
      = x ^ 2 * (π ^ 2 * ((n : ℝ) + 1 / 2) ^ 2)⁻¹ := div_eq_mul_inv _ _
    _ ≤ x ^ 2 * (π ^ 2 * ((n : ℝ) + 1) ^ 2 / 4)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ h0 (quarter_le n)) (sq_nonneg x)
    _ = 4 * x ^ 2 * (π ^ 2 * ((n : ℝ) + 1) ^ 2)⁻¹ := by
        rw [inv_div, div_eq_mul_inv]
        ring

theorem multipliable_sinhFac (x : ℝ) : Multipliable (sinhFac x) :=
  Real.multipliable_one_add_of_summable (summable_sinhFac_sub x)

theorem multipliable_coshFac (x : ℝ) : Multipliable (coshFac x) :=
  Real.multipliable_one_add_of_summable (summable_coshFac_sub x)

/-- **Proposition 6.2**, (13) and (71) in scalar form: `sinh x / x = ∏ₙ (1 + x²/(π²n²))`. -/
theorem hasProd_sinh (x : ℝ) (hx : x ≠ 0) : HasProd (sinhFac x) (Real.sinh x / x) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨ξ, hξdef⟩ : ∃ ξ : ℂ, ξ = (x : ℂ) / (π : ℂ) * Complex.I := ⟨_, rfl⟩
  have hξ : ξ ≠ 0 := by
    rw [hξdef]
    exact mul_ne_zero (div_ne_zero (Complex.ofReal_ne_zero.mpr hx) hπ) Complex.I_ne_zero
  have key := tendsto_euler_sin_prod' hξ
  have hsq : ξ ^ 2 = -(((x : ℂ) / (π : ℂ)) ^ 2) := by
    rw [hξdef, mul_pow, Complex.I_sq]
    ring
  have h1 : ∀ i : ℕ, 1 + sineTerm ξ i = ((sinhFac x i : ℝ) : ℂ) := by
    intro i
    simp only [sineTerm, hsq, sinhFac]
    push_cast
    simp only [neg_neg, div_pow, div_div]
  have h2 : Complex.sin ((π : ℂ) * ξ) / ((π : ℂ) * ξ) = ((Real.sinh x / x : ℝ) : ℂ) := by
    have hπξ : (π : ℂ) * ξ = (x : ℂ) * Complex.I := by
      rw [hξdef, ← mul_assoc, mul_div_cancel₀ _ hπ]
    rw [hπξ, Complex.sin_mul_I, mul_div_mul_right _ _ Complex.I_ne_zero, Complex.ofReal_div,
      Complex.ofReal_sinh]
  simp only [h1, h2] at key
  have key2 : Tendsto (fun n => ((∏ i ∈ Finset.range n, sinhFac x i : ℝ) : ℂ)) atTop
      (𝓝 ((Real.sinh x / x : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_prod] using key
  have key3 := (Complex.continuous_re.tendsto _).comp key2
  simp only [Function.comp_def, Complex.ofReal_re] at key3
  exact (multipliable_sinhFac x).hasProd_iff_tendsto_nat.mpr key3

/-- **Proposition 6.2**, (14) and (72) in scalar form: `cosh x = ∏ₙ (1 + x²/(π²(n-1/2)²))`, from the
splitting of the product over `{π²n²/4}` into the products over `{π²m²}` and `{π²(m-1/2)²}`. -/
theorem hasProd_cosh (x : ℝ) (hx : x ≠ 0) : HasProd (coshFac x) (Real.cosh x) := by
  have hP := (multipliable_coshFac x).hasProd
  have he : (fun k : ℕ => sinhFac (2 * x) (2 * k)) = coshFac x := by
    funext k
    simp only [sinhFac, coshFac]
    push_cast
    congr 1
    have hb : π ^ 2 * (2 * (k : ℝ) + 1) ^ 2 ≠ 0 := by positivity
    have hd : π ^ 2 * ((k : ℝ) + 1 / 2) ^ 2 ≠ 0 := by positivity
    rw [div_eq_div_iff hb hd]
    ring
  have ho : (fun k : ℕ => sinhFac (2 * x) (2 * k + 1)) = sinhFac x := by
    funext k
    simp only [sinhFac]
    push_cast
    congr 1
    have hb : π ^ 2 * (2 * (k : ℝ) + 1 + 1) ^ 2 ≠ 0 := by positivity
    have hd : π ^ 2 * ((k : ℝ) + 1) ^ 2 ≠ 0 := by positivity
    rw [div_eq_div_iff hb hd]
    ring
  have h1 : HasProd (fun k : ℕ => sinhFac (2 * x) (2 * k)) (∏' k, coshFac x k) := by
    rw [he]
    exact hP
  have h2 : HasProd (fun k : ℕ => sinhFac (2 * x) (2 * k + 1)) (Real.sinh x / x) := by
    rw [ho]
    exact hasProd_sinh x hx
  have hsplit := h1.even_mul_odd h2
  have hfull := hasProd_sinh (2 * x) (mul_ne_zero two_ne_zero hx)
  have huniq := hsplit.unique hfull
  have hsx : Real.sinh x / x ≠ 0 := div_ne_zero (Real.sinh_ne_zero.mpr hx) hx
  have hdup : Real.sinh (2 * x) / (2 * x) = Real.cosh x * (Real.sinh x / x) := by
    rw [Real.sinh_two_mul]
    ring
  rw [hdup] at huniq
  have hc : ∏' k, coshFac x k = Real.cosh x := mul_right_cancel₀ hsx huniq
  rw [← hc]
  exact hP

/-- **Proposition 6.2**, (73) in scalar form: `r_E(z₀) = ∏ₙ (1 + 1/(8π²n²))`. -/
theorem eq73 :
    HasProd (fun n : ℕ => 1 + 1 / (8 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) (Real.sinh a / a) ∧
      rE z0 = ((Real.sinh a / a : ℝ) : ℂ) := by
  refine ⟨?_, rE_z0⟩
  have hf : (fun n : ℕ => 1 + 1 / (8 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) = sinhFac a := by
    funext n
    simp only [sinhFac, a_sq]
    congr 1
    first
      | (rw [div_div, mul_assoc]; done)
      | (field_simp; done)
      | (field_simp; ring)
  rw [hf]
  exact hasProd_sinh a a_ne_zero

/-! ## Theorem 7.2: the factorisation (92), the companion form (93), (94)–(96) -/

/-- (92), first equality: the product over the spectrum `{π²n²/4}` of `A₂` at coupling `a`
is `sinh(b)/b`. -/
theorem det_A2 :
    HasProd (fun n : ℕ => 1 + a ^ 2 / (π ^ 2 * ((n : ℝ) + 1) ^ 2 / 4)) (Real.sinh b / b) := by
  have hf : (fun n : ℕ => 1 + a ^ 2 / (π ^ 2 * ((n : ℝ) + 1) ^ 2 / 4)) = sinhFac b := by
    funext n
    simp only [sinhFac]
    rw [b_eq_two_mul_a]
    congr 1
    rw [div_div_eq_mul_div]
    ring
  rw [hf]
  exact hasProd_sinh b b_ne_zero

/-- (92), second equality: the product over `{π²n²/4}` splits into the products over
`{π²m²}` and `{π²(m-1/2)²}`, whose values are `sinh(a)/a` and `cosh(a)`. -/
theorem det_split : (∏' n, sinhFac a n) * (∏' n, coshFac a n) = Real.sinh b / b := by
  rw [(hasProd_sinh a a_ne_zero).tprod_eq, (hasProd_cosh a a_ne_zero).tprod_eq,
    b_eq_two_mul_a, Real.sinh_two_mul]
  ring

/-- **Theorem 7.2**, (92): `r_E(z₁) = ∏ (1 + a²/(π²m²)) ∏ (1 + a²/(π²(m-1/2)²)) = r_E(z₀) cosh(a)`. -/
theorem eq92 :
    rE z1 = (((∏' n, sinhFac a n) * (∏' n, coshFac a n) : ℝ) : ℂ) ∧
      rE z1 = rE z0 * ((Real.cosh a : ℝ) : ℂ) := by
  refine ⟨by rw [det_split, rE_z1], ?_⟩
  rw [modular_duplication.2, mul_comm]

/-- **Theorem 7.2**, (93): `r_E(z₁) = ∏ₙ (1 + 1/(2π²n²))`. -/
theorem eq93 :
    HasProd (fun n : ℕ => 1 + 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) (Real.sinh b / b) ∧
      rE z1 = ((Real.sinh b / b : ℝ) : ℂ) := by
  refine ⟨?_, rE_z1⟩
  have hf : (fun n : ℕ => 1 + 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) = sinhFac b := by
    funext n
    simp only [sinhFac, b_sq]
    congr 1
    first
      | (rw [div_div, mul_assoc]; done)
      | (field_simp; done)
      | (field_simp; ring)
  rw [hf]
  exact hasProd_sinh b b_ne_zero

/-- **Theorem 7.2**, (94): `2 L(b) = L(a) + tanh(a)`. -/
theorem eq94 : 2 * Lval b = Lval a + Real.tanh a := by
  rw [b_eq_two_mul_a]
  exact langevin_dup a a_ne_zero

/-- **Theorem 7.2**, (95): `4 Var_b = Var_a + sech²(a)`. -/
theorem eq95 : 4 * Vval b = Vval a + (Real.cosh a ^ 2)⁻¹ := by
  rw [b_eq_two_mul_a]
  exact var_dup a a_ne_zero

/-- **Theorem 7.2**, (96): `4 Tr (2/(2A+I)) = Tr (8/(8A+I)) + Tr (8/(8A_DN+I))`. -/
theorem eq96 : 4 * TD b = TD a + TDN a := by
  rw [b_eq_two_mul_a]
  exact trace_split a

/-- **Theorem 7.2**, explicit companion value `L(b) = coth(b) - √2`. -/
theorem langevin_b : Lval b = Real.cosh b / Real.sinh b - Real.sqrt 2 := by
  rw [Lval, ← one_div, one_div_b]

/-- **Theorem 7.2**, explicit companion value `Var_b = 2 - csch²(b)`. -/
theorem variance_b : Vval b = 2 - (Real.sinh b ^ 2)⁻¹ := by
  rw [Vval, b_sq]
  norm_num

/-- **Theorem 7.2**, explicit companion value `Tr (A + I/2)⁻¹ = coth(b)/√2 - 1`. -/
theorem trace_b : TD b = Real.cosh b / Real.sinh b / Real.sqrt 2 - 1 := by
  have hs : Real.sqrt 2 ≠ 0 := sqrt_two_pos.ne'
  have hL : Lval b = Real.sqrt 2 * TD b := by rw [trace_master b b_pos, two_b]
  calc TD b = Real.sqrt 2 * TD b / Real.sqrt 2 := (mul_div_cancel_left₀ (TD b) hs).symm
    _ = Lval b / Real.sqrt 2 := by rw [hL]
    _ = (Real.cosh b / Real.sinh b - Real.sqrt 2) / Real.sqrt 2 := by rw [langevin_b]
    _ = Real.cosh b / Real.sinh b / Real.sqrt 2 - 1 := by rw [sub_div, div_self hs]

/-! ## Axiom audit -/

#print axioms S_eq_two_mul_iff
#print axioms S_z1
#print axioms eq91
#print axioms pair_difference
#print axioms trace_master
#print axioms trace_tanh
#print axioms trace_square
#print axioms trace_special
#print axioms trace_B_special
#print axioms hs2_special
#print axioms hasProd_sinh
#print axioms hasProd_cosh
#print axioms eq73
#print axioms eq92
#print axioms eq93
#print axioms eq94
#print axioms eq95
#print axioms eq96
#print axioms trace_b

end Manuscript14Section67

end
