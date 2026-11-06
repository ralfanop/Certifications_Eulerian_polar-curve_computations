import Mathlib

/-!
# Manuscript 14, Sections 8 and 9: the Lean 4 certificate

This module kernel-checks the algebraic and analytic content of Sections 8 and 9 of
manuscript 14 ("Eulerian Fourier profiles at the special point i/√2").

* Theorem 8.1 (quadratic covering): the fibres of `Q(τ) = τ²/2` are the pairs `{τ, -τ}`; every
  continuous self-map `T` of `ℂ \ {0}` with `Q ∘ T = Q` is the identity or `δ(τ) = -τ`, which has
  no fixed point; the Euler factorisation `r_E(τ) = ∏ₙ (1 - Q(τ)/(2π²n²))` as a limit of partial
  products, `r_E ∘ δ = r_E`, the field reversal (`L` odd, `m(-H) = 1 - m(H)`); the algebraic core of
  the winding statements (the lifts `±√2 e^{h/2}`, the parity `(-1)^n` of the monodromy, the doubling
  of winding numbers); the fibre `Q⁻¹(-1/4) = {±z₀}`, the actions `Q(Sτ) = 1/(4Q(τ))`,
  `Q(2τ) = 4Q(τ)`, their agreement exactly at `q = ±1/4`, and the uniqueness of `z₀` in `ℍ`.
* Proposition 8.2 (Montgomery–Taylor constant): `C₀ = 3/2 - z₀ coth z₀ = 1/2 + ∑ₙ 1/(π²n² - 1/2)`,
  the logarithmic-derivative form at `√2`, the companion identity
  `C₀ + ∑ₙ 1/(π²(n-1/2)² - 1/2) = 1/2 + ∑ₙ 4/(π²n² - 2) = 3/2 - √2 cot √2` and the value
  `tan(1/√2)/√2` of the Dirichlet–Neumann sum, from the Mittag-Leffler expansion of the cotangent
  at the real points `y/π`.
* Proposition 8.4 (self-dual Ising coupling): with `K = log(1+√2)/2`, `sinh 2K = 1`,
  `cosh 2K = √2`, `tanh 2K = 1/√2`, `tanh K = e^{-2K} = √2 - 1 = 2Z*`, `4Z*² + 4Z* - 1 = 0` and its
  equivalence with `sinh 2K = 1` through `sinh 2K = 2t/(1-t²)`, `arctan z₀ = 2iK`, the fields
  `H₀ = -tanh 2K`, `H₁ = -coth 2K`; the arcsine moments `(1/π)∫₀^π sin^{2n} = C(2n,n)/4ⁿ`.
* Proposition 8.6: `a_n = 2cos(π/2^{n+1})`, `T₂(a_{n+1}/2) = a_n/2`, `T₂(μ/2) = |z₀|`,
  `T₄(μ/2) = 0`, the quartic of `μ = √(2+√2)`, `U₇(λ/2) = λ(λ²-2)(λ⁴-4λ²+2)`, its zeros
  `2cos(jπ/8)` and the eigenvector relation of the path graph, Viète's product for `2/π`.
* Proposition 8.7: `∑ⱼ (2n)!/(j!²(n-j)!²) = C(2n,n)²` and `(1/2)ₙ² 16ⁿ/(n!)² = C(2n,n)²`.
* Lemma 9.2, Theorem 9.3 (algebraic part), Proposition 9.5, Proposition 9.7 (algebraic part):
  time reversal `Θψ = -iσ₂ψ̄`, `Θ² = -1`, `⟨ψ,Θψ⟩ = 0`, antiunitarity, `Θσⱼ = -σⱼΘ`, no fixed
  ray; the Bloch map: expectations of the Pauli matrices, `ω(Θψ) = -ω(ψ)`, `|ω| = 1`; Brillouin
  `B_{1/2}(y) = 2coth 2y - coth y = tanh y = 2L(2y) - L(y)`, the product split, the thermal
  operator and its time reversal; fixed points of the involutions and the conjugacy of the three
  half-line inversions.

Classical inputs (stated in Section 2.2 of the manuscript) enter as such and are not formalised
here: the covering-space theory of the punctured plane (existence of continuous logarithms and
lifts), the homeomorphism and measure statements of the Bloch map, the identification of the
characteristic polynomial of the path graph with `U_m(λ/2)`, the Kramers–Wannier duality, the
honeycomb connective constant, and the lattice determinants; the numerical statements are in
the Arb certificate `numerics/arb/manuscript14_section89_arb.py`.
-/

open Filter Topology Finset ComplexConjugate
open scoped Real

noncomputable section

namespace Manuscript14Section89

/-! ## Constants -/

/-- `b = 1/√2 = |z₀|`. -/
def b : ℝ := 1 / Real.sqrt 2

/-- The special point `z₀ = i/√2`. -/
def z0 : ℂ := Complex.I / ((Real.sqrt 2 : ℝ) : ℂ)

/-- The modular inversion `S(τ) = -1/τ`. -/
def S (τ : ℂ) : ℂ := -1 / τ

/-- The quadratic map `Q(τ) = τ²/2`. -/
def Q (τ : ℂ) : ℂ := τ ^ 2 / 2

/-- The Eulerian profile `r_E(z) = 2 sin(z/2)/z`, `r_E(0) = 1`. -/
def rE (z : ℂ) : ℂ := if z = 0 then 1 else 2 * Complex.sin (z / 2) / z

/-- The self-dual coupling `K = log(1+√2)/2`. -/
def Kc : ℝ := Real.log (1 + Real.sqrt 2) / 2

/-- The Montgomery–Taylor constant `C₀ = 3/2 - (1/√2) cot(1/√2)`. -/
def C0 : ℝ := 3 / 2 - b * (Real.cos b / Real.sin b)

/-- The boundary value `Z* = (√2 - 1)/2`. -/
def Zstar : ℝ := (Real.sqrt 2 - 1) / 2

/-- The honeycomb constant `μ = √(2+√2)`. -/
def muHex : ℝ := Real.sqrt (2 + Real.sqrt 2)

/-- The hyperbolic cotangent. -/
def coth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x

/-- The Langevin function `L(x) = coth x - 1/x`. -/
def Lval (x : ℝ) : ℝ := coth x - x⁻¹

/-- The centre of the magnetised Eulerian law, `m(H) = (1 + L(H/2))/2`. -/
def mag (H : ℝ) : ℝ := (1 + Lval (H / 2)) / 2

/-- The spectral terms `(π²(n+1)² - s)⁻¹` and `(π²(n+1/2)² - s)⁻¹`. -/
def tmTerm (s : ℝ) (n : ℕ) : ℝ := (π ^ 2 * ((n : ℝ) + 1) ^ 2 - s)⁻¹

def tmnTerm (s : ℝ) (n : ℕ) : ℝ := (π ^ 2 * ((n : ℝ) + 1 / 2) ^ 2 - s)⁻¹

/-- `TM s = ∑ₙ (π²n² - s)⁻¹ = Tr (A - s)⁻¹` and `TMN s = ∑ₙ (π²(n-1/2)² - s)⁻¹ = Tr (A_DN - s)⁻¹`. -/
def TM (s : ℝ) : ℝ := ∑' n : ℕ, tmTerm s n

def TMN (s : ℝ) : ℝ := ∑' n : ℕ, tmnTerm s n

/-! ## Elementary facts on `√2`, `b`, `z₀` -/

theorem sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem one_lt_sqrt_two : 1 < Real.sqrt 2 := by
  nlinarith [sqrt_two_sq, sqrt_two_pos]

theorem sqrt_two_lt_pi : Real.sqrt 2 < π := by
  nlinarith [sqrt_two_sq, sqrt_two_pos, Real.pi_gt_three]

theorem b_pos : 0 < b := by
  unfold b
  exact div_pos one_pos sqrt_two_pos

theorem b_ne_zero : b ≠ 0 := b_pos.ne'

theorem b_sq : b ^ 2 = 1 / 2 := by
  unfold b
  rw [div_pow, sqrt_two_sq]
  norm_num

theorem sqrt_two_eq : Real.sqrt 2 = 2 * b := by
  unfold b
  have hs := sqrt_two_pos.ne'
  rw [mul_one_div, eq_div_iff hs]
  nlinarith [sqrt_two_sq]

theorem b_lt_one : b < 1 := by
  unfold b
  rw [div_lt_one sqrt_two_pos]
  exact one_lt_sqrt_two

theorem b_lt_pi : b < π := by linarith [b_lt_one, Real.pi_gt_three]

theorem sin_b_pos : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi b_pos b_lt_pi

theorem sqrt_two_ne_zero_c : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr sqrt_two_pos.ne'

theorem sqrt_two_sq_c : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, sqrt_two_sq]
  norm_num

theorem z0_eq : z0 = (b : ℂ) * Complex.I := by
  unfold z0 b
  push_cast
  ring

theorem z0_ne_zero : z0 ≠ 0 := by
  rw [z0_eq]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr b_ne_zero) Complex.I_ne_zero

/-! ## Theorem 8.1: the quadratic covering and the antipodal fibre -/

/-- The deck involution preserves `Q`. -/
theorem Q_neg (τ : ℂ) : Q (-τ) = Q τ := by
  unfold Q
  ring

/-- **Theorem 8.1 (i)**: the fibres of `Q` are the pairs `{τ, -τ}`. -/
theorem Q_eq_iff (σ τ : ℂ) : Q σ = Q τ ↔ σ = τ ∨ σ = -τ := by
  unfold Q
  constructor
  · intro h
    have h2 : σ ^ 2 = τ ^ 2 := by linear_combination 2 * h
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h2
  · rintro (h | h) <;> rw [h] <;> ring

/-- **Theorem 8.1 (i)**: the deck involution `δ(τ) = -τ` has no fixed point on `ℂ \ {0}`. -/
theorem delta_no_fixed (τ : ℂ) (hτ : τ ≠ 0) : -τ ≠ τ := by
  intro h
  apply hτ
  linear_combination -h / 2

/-- **Theorem 8.1 (i)**: every continuous self-map `T` of `ℂ \ {0}` with `Q ∘ T = Q` is the identity
or the deck involution `δ`; the deck group is `{id, δ}`. -/
theorem deck (T : ℂ → ℂ) (hT : ContinuousOn T ({0}ᶜ : Set ℂ))
    (hQ : ∀ z ∈ ({0}ᶜ : Set ℂ), Q (T z) = Q z) :
    Set.EqOn T id ({0}ᶜ : Set ℂ) ∨ Set.EqOn T (-id) ({0}ᶜ : Set ℂ) := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    first
      | exact one_lt_two
      | norm_num
      | exact Nat.one_lt_ofNat
  have hconn : IsPreconnected ({0}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank hrank 0).isPreconnected
  refine hconn.eq_or_eq_neg_of_sq_eq hT continuousOn_id ?_ ?_
  · intro z hz
    have h := hQ z hz
    simp only [Q] at h
    simp only [Pi.pow_apply, id]
    linear_combination 2 * h
  · intro z hz
    simpa using hz

/-- **Theorem 8.1 (ii)**: the Euler factorisation `r_E(τ) = ∏ₙ (1 - Q(τ)/(2π²n²))` (partial products). -/
theorem rE_factor (τ : ℂ) :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N,
      (1 - Q τ / (2 * (π : ℂ) ^ 2 * ((n : ℂ) + 1) ^ 2))) atTop (𝓝 (rE τ)) := by
  by_cases hτ : τ = 0
  · subst hτ
    simp [Q, rE]
  · have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    obtain ⟨ξ, hξ⟩ : ∃ ξ : ℂ, ξ = τ / (2 * (π : ℂ)) := ⟨_, rfl⟩
    have hξ0 : ξ ≠ 0 := by
      rw [hξ]
      exact div_ne_zero hτ (mul_ne_zero two_ne_zero hπ)
    have key := tendsto_euler_sin_prod' hξ0
    have h1 : ∀ i : ℕ, 1 + sineTerm ξ i = 1 - Q τ / (2 * (π : ℂ) ^ 2 * ((i : ℂ) + 1) ^ 2) := by
      intro i
      have hi : ((i : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero i
      simp only [sineTerm, Q, hξ]
      first
        | (field_simp; ring)
        | field_simp
    have h2 : Complex.sin ((π : ℂ) * ξ) / ((π : ℂ) * ξ) = rE τ := by
      have h3 : (π : ℂ) * ξ = τ / 2 := by
        rw [hξ]
        first
          | (field_simp; ring)
          | field_simp
      rw [h3]
      simp only [rE, if_neg hτ]
      first
        | (field_simp; ring)
        | field_simp
    simp only [h1, h2] at key
    exact key

/-- **Theorem 8.1 (ii)**: `r_E ∘ δ = r_E`. -/
theorem rE_neg (τ : ℂ) : rE (-τ) = rE τ := by
  unfold rE
  by_cases hτ : τ = 0
  · simp [hτ]
  · have h' : -τ ≠ 0 := neg_ne_zero.mpr hτ
    rw [if_neg h', if_neg hτ, neg_div, Complex.sin_neg, mul_neg, neg_div_neg_eq]

/-- The Langevin function is odd. -/
theorem Lval_neg (x : ℝ) : Lval (-x) = -Lval x := by
  unfold Lval coth
  rw [Real.cosh_neg, Real.sinh_neg, div_neg, inv_neg]
  ring

/-- **Theorem 8.1 (ii)**: under the field reversal the centre of the magnetised law is reflected. -/
theorem mag_neg (H : ℝ) : mag (-H) = 1 - mag H := by
  unfold mag
  rw [show -H / 2 = -(H / 2) by ring, Lval_neg]
  ring

/-- **Theorem 8.1 (iii)**, algebraic core: `Q ∘ exp g = exp(2g)/2`, so that winding numbers double. -/
theorem Q_exp (g : ℂ) : Q (Complex.exp g) = Complex.exp (2 * g) / 2 := by
  unfold Q
  rw [← Complex.exp_nat_mul]
  norm_num

theorem winding_double (g0 g1 : ℂ) (n : ℤ) (h : g1 - g0 = 2 * π * Complex.I * n) :
    2 * g1 - 2 * g0 = 2 * π * Complex.I * ((2 * n : ℤ) : ℂ) := by
  push_cast
  linear_combination 2 * h

/-- **Theorem 8.1 (iii)**: the lifts `±√2 e^{h/2}` of `e^h` through `Q`. -/
theorem lift_Q (h : ℂ) : Q (((Real.sqrt 2 : ℝ) : ℂ) * Complex.exp (h / 2)) = Complex.exp h := by
  unfold Q
  rw [mul_pow, sqrt_two_sq_c, ← Complex.exp_nat_mul]
  first
    | (push_cast; ring_nf)
    | (norm_num; ring_nf)
    | ring_nf

/-- **Theorem 8.1 (iii)**, (109): the endpoint of a lift is multiplied by `(-1)^{wn}`. -/
theorem lift_parity (h0 h1 : ℂ) (n : ℤ) (hn : h1 - h0 = 2 * π * Complex.I * n) :
    ((Real.sqrt 2 : ℝ) : ℂ) * Complex.exp (h1 / 2) =
      (-1 : ℂ) ^ n * (((Real.sqrt 2 : ℝ) : ℂ) * Complex.exp (h0 / 2)) := by
  have e : h1 / 2 = (n : ℂ) * ((π : ℂ) * Complex.I) + h0 / 2 := by linear_combination hn / 2
  rw [e, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  ring

/-- **Theorem 8.1 (iv)**: `Q(z₀) = -1/4`. -/
theorem Q_z0 : Q z0 = -1 / 4 := by
  rw [z0_eq]
  unfold Q
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, b_sq]
  norm_num

/-- **Theorem 8.1 (iv)**: the fibre over `-1/4` is `{z₀, -z₀}`. -/
theorem fibre_neg_quarter (τ : ℂ) : Q τ = -1 / 4 ↔ τ = z0 ∨ τ = -z0 := by
  rw [← Q_z0, Q_eq_iff]

theorem Q_b : Q (b : ℂ) = 1 / 4 := by
  unfold Q
  rw [← Complex.ofReal_pow, b_sq]
  norm_num

/-- **Theorem 8.1 (iv)**: the real fibre over `1/4` is `{±1/√2}`. -/
theorem fibre_quarter (τ : ℂ) : Q τ = 1 / 4 ↔ τ = (b : ℂ) ∨ τ = -(b : ℂ) := by
  rw [← Q_b, Q_eq_iff]

/-- **Theorem 8.1 (iv)**, (111): the modular inversion and the dilation in the variable `q`. -/
theorem Q_S (τ : ℂ) (hτ : τ ≠ 0) : Q (S τ) = 1 / (4 * Q τ) := by
  unfold Q S
  first
    | (field_simp; ring)
    | field_simp

theorem Q_two_mul (τ : ℂ) : Q (2 * τ) = 4 * Q τ := by
  unfold Q
  ring

/-- **Theorem 8.1 (iv)**: `q ↦ 1/(4q)` and `q ↦ 4q` agree exactly at `q = ±1/4`. -/
theorem actions_agree (q : ℂ) (hq : q ≠ 0) : 1 / (4 * q) = 4 * q ↔ q = 1 / 4 ∨ q = -(1 / 4) := by
  have h4 : (4 : ℂ) * q ≠ 0 := mul_ne_zero (by norm_num) hq
  rw [div_eq_iff h4, ← sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · intro h
    linear_combination (-1 / 16 : ℂ) * h
  · intro h
    linear_combination (-16 : ℂ) * h

/-- **Theorem 8.1 (iv)**: `Sτ = 2τ` exactly over `q = -1/4`. -/
theorem S_eq_two_mul_iff (τ : ℂ) (hτ : τ ≠ 0) : S τ = 2 * τ ↔ Q τ = -1 / 4 := by
  unfold S Q
  rw [div_eq_iff hτ]
  constructor
  · intro h
    linear_combination (-1 / 4 : ℂ) * h
  · intro h
    linear_combination (-4 : ℂ) * h

/-- **Theorem 8.1 (iv)**: `Sτ = δ(2τ)` exactly over `q = 1/4`. -/
theorem S_eq_neg_two_mul_iff (τ : ℂ) (hτ : τ ≠ 0) : S τ = -(2 * τ) ↔ Q τ = 1 / 4 := by
  unfold S Q
  rw [div_eq_iff hτ]
  constructor
  · intro h
    linear_combination (1 / 4 : ℂ) * h
  · intro h
    linear_combination (4 : ℂ) * h

/-- **Theorem 8.1 (iv)**: `z₀` is the only point of `Q⁻¹({1/4, -1/4})` in the upper half-plane. -/
theorem unique_in_H (τ : ℂ) (hτ : 0 < τ.im) (hq : Q τ = 1 / 4 ∨ Q τ = -1 / 4) : τ = z0 := by
  rcases hq with h | h
  · rcases (fibre_quarter τ).mp h with h1 | h1
    · rw [h1, Complex.ofReal_im] at hτ
      exact absurd hτ (lt_irrefl 0)
    · rw [h1, Complex.neg_im, Complex.ofReal_im, neg_zero] at hτ
      exact absurd hτ (lt_irrefl 0)
  · rcases (fibre_neg_quarter τ).mp h with h1 | h1
    · exact h1
    · have him : (-z0).im = -b := by
        rw [z0_eq]
        simp
      rw [h1, him] at hτ
      linarith [b_pos]

/-- **Theorem 8.1 (iv)**: `E(-1/4) = r_E(z₀)`, i.e. `r_E(z₀) = ∏ₙ (1 + 1/(8π²n²))`. -/
theorem E_neg_quarter :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N,
      (1 + 1 / (8 * (π : ℂ) ^ 2 * ((n : ℂ) + 1) ^ 2))) atTop (𝓝 (rE z0)) := by
  have h := rE_factor z0
  rw [Q_z0] at h
  refine h.congr (fun N => Finset.prod_congr rfl (fun n _ => ?_))
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hi : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  first
    | (field_simp; ring)
    | field_simp

/-! ## Proposition 8.2: the Montgomery–Taylor constant as a resolvent trace -/

theorem tm_pos (s : ℝ) (hs : s < π ^ 2) (n : ℕ) : 0 < π ^ 2 * ((n : ℝ) + 1) ^ 2 - s := by
  have hn : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    nlinarith
  have : π ^ 2 ≤ π ^ 2 * ((n : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg π]
  linarith

theorem summable_inv_succ_sq : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
  have h0 : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
  have h1 := (summable_nat_add_iff 1).mpr h0
  simpa [Nat.cast_add, Nat.cast_one] using h1

theorem summable_tmTerm (s : ℝ) (hs0 : 0 ≤ s) (hs : s < π ^ 2) : Summable (tmTerm s) := by
  have hc : 0 < π ^ 2 - s := by linarith
  refine Summable.of_nonneg_of_le (fun n => (inv_pos.mpr (tm_pos s hs n)).le) (fun n => ?_)
    (summable_inv_succ_sq.mul_left ((π ^ 2 - s)⁻¹))
  unfold tmTerm
  have hn : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    nlinarith
  have hle : (π ^ 2 - s) * ((n : ℝ) + 1) ^ 2 ≤ π ^ 2 * ((n : ℝ) + 1) ^ 2 - s := by nlinarith
  have hp : 0 < (π ^ 2 - s) * ((n : ℝ) + 1) ^ 2 := by positivity
  calc (π ^ 2 * ((n : ℝ) + 1) ^ 2 - s)⁻¹ ≤ ((π ^ 2 - s) * ((n : ℝ) + 1) ^ 2)⁻¹ := inv_anti₀ hp hle
    _ = (π ^ 2 - s)⁻¹ * (((n : ℝ) + 1) ^ 2)⁻¹ := mul_inv _ _

/-- The cotangent expansion at a real point: `y cot y = 1 - 2y² ∑ₙ (π²n² - y²)⁻¹` for `0 < y < π`. -/
theorem cot_trace (y : ℝ) (hy0 : 0 < y) (hyπ : y < π) :
    y * (Real.cos y / Real.sin y) = 1 - 2 * y ^ 2 * TM (y ^ 2) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hπ' : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hπ
  have hy : y ≠ 0 := hy0.ne'
  have hy' : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy
  have hy2 : y ^ 2 < π ^ 2 := by nlinarith
  have hu0 : 0 < y / π := div_pos hy0 Real.pi_pos
  have hu1 : y / π < 1 := (div_lt_one Real.pi_pos).mpr hyπ
  have hmem : (((y / π : ℝ)) : ℂ) ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    have hn' : (n : ℝ) = y / π := by exact_mod_cast hn
    have h0 : (0 : ℝ) < n := by rw [hn']; exact hu0
    have h1 : (n : ℝ) < 1 := by rw [hn']; exact hu1
    have h0' : (0 : ℤ) < n := by exact_mod_cast h0
    have h1' : n < (1 : ℤ) := by exact_mod_cast h1
    omega
  have h := cot_series_rep' hmem
  have hπu : (π : ℂ) * (((y / π : ℝ)) : ℂ) = (y : ℂ) := by
    rw [← Complex.ofReal_mul, mul_div_cancel₀ _ hπ]
  have hsin : Real.sin y ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hy0 hyπ).ne'
  have hsinc : Complex.sin (y : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]
    exact Complex.ofReal_ne_zero.mpr hsin
  have hL : (π : ℂ) * Complex.cot ((π : ℂ) * (((y / π : ℝ)) : ℂ)) - 1 / (((y / π : ℝ)) : ℂ) =
      ((π * (Real.cos y / Real.sin y) - π / y : ℝ) : ℂ) := by
    rw [hπu, Complex.cot_eq_cos_div_sin]
    push_cast
    first
      | (field_simp; ring)
      | field_simp
  have hR : ∀ n : ℕ, 1 / ((((y / π : ℝ)) : ℂ) - ((n : ℂ) + 1)) +
      1 / ((((y / π : ℝ)) : ℂ) + ((n : ℂ) + 1)) =
      ((-(2 * π * y) * tmTerm (y ^ 2) n : ℝ) : ℂ) := by
    intro n
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hA : y / π - ((n : ℝ) + 1) ≠ 0 := by
      have : y / π < (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      linarith
    have hB : y / π + ((n : ℝ) + 1) ≠ 0 := by linarith
    have hD := (tm_pos (y ^ 2) hy2 n).ne'
    have e : 1 / (y / π - ((n : ℝ) + 1)) + 1 / (y / π + ((n : ℝ) + 1)) =
        -(2 * π * y) * tmTerm (y ^ 2) n := by
      unfold tmTerm
      rw [div_add_div _ _ hA hB, eq_comm, ← div_eq_mul_inv, div_eq_div_iff hD (mul_ne_zero hA hB)]
      field_simp
      ring
    rw [← e]
    first
      | (push_cast; ring)
      | push_cast
      | norm_cast
  have hsum : (∑' n : ℕ, (1 / ((((y / π : ℝ)) : ℂ) - ((n : ℂ) + 1)) +
      1 / ((((y / π : ℝ)) : ℂ) + ((n : ℂ) + 1)))) =
      ((-(2 * π * y) * TM (y ^ 2) : ℝ) : ℂ) := by
    rw [tsum_congr hR, ← Complex.ofReal_tsum, tsum_mul_left]
    rfl
  rw [hL, hsum] at h
  have h' : π * (Real.cos y / Real.sin y) - π / y = -(2 * π * y) * TM (y ^ 2) :=
    Complex.ofReal_injective h
  have h'' : π * (y * (Real.cos y / Real.sin y)) = π * (1 - 2 * y ^ 2 * TM (y ^ 2)) := by
    have e1 : π * (y * (Real.cos y / Real.sin y)) =
        y * (π * (Real.cos y / Real.sin y) - π / y) + π := by
      first
        | (field_simp; ring)
        | field_simp
    rw [e1, h']
    ring
  exact mul_left_cancel₀ hπ h''

/-- **Proposition 8.2 (i)**, (114): `C₀ = 1/2 + ∑ₙ 1/(π²n² - 1/2) = 1/2 + Tr (A + z₀²)⁻¹`. -/
theorem mt_trace : C0 = 1 / 2 + TM (1 / 2) := by
  have h := cot_trace b b_pos b_lt_pi
  rw [b_sq] at h
  unfold C0
  rw [h]
  ring

/-- **Proposition 8.2 (i)**: `z₀ coth z₀ = (1/√2) cot(1/√2)`, so that `C₀ = 3/2 - z₀ coth z₀`. -/
theorem mt_complex : (3 / 2 : ℂ) - z0 * (Complex.cosh z0 / Complex.sinh z0) = (C0 : ℂ) := by
  have hs : Complex.sin (b : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]
    exact Complex.ofReal_ne_zero.mpr sin_b_pos.ne'
  rw [z0_eq, Complex.cosh_mul_I, Complex.sinh_mul_I]
  unfold C0
  push_cast
  first
    | (field_simp; ring)
    | field_simp

/-- **Proposition 8.2 (i)**: the trace is invariant under `z₀ ↦ -z₀` (`z coth z` is even). -/
theorem mt_even : (-z0) * (Complex.cosh (-z0) / Complex.sinh (-z0)) =
    z0 * (Complex.cosh z0 / Complex.sinh z0) := by
  rw [Complex.cosh_neg, Complex.sinh_neg, div_neg]
  ring

/-- The profile on the real axis, `r_E(t) = 2 sin(t/2)/t`. -/
def rEr (t : ℝ) : ℝ := 2 * Real.sin (t / 2) / t

theorem hasDerivAt_rEr (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt rEr (Real.cos (t / 2) / t - 2 * Real.sin (t / 2) / t ^ 2) t := by
  have h0 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) t := (hasDerivAt_id' (x := t)).div_const 2
  have h1 : HasDerivAt (fun x : ℝ => 2 * Real.sin (x / 2)) (2 * (Real.cos (t / 2) * (1 / 2))) t :=
    h0.sin.const_mul 2
  have h2 := h1.fun_div (hasDerivAt_id' (x := t)) ht
  unfold rEr
  refine h2.congr_deriv ?_
  first
    | (field_simp; ring)
    | field_simp

/-- **Proposition 8.2 (ii)**: `C₀ = 1/2 - √2 r_E'(√2)/r_E(√2)`. -/
theorem mt_logderiv : C0 = 1 / 2 - Real.sqrt 2 * deriv rEr (Real.sqrt 2) / rEr (Real.sqrt 2) := by
  rw [(hasDerivAt_rEr _ sqrt_two_pos.ne').deriv]
  unfold rEr C0
  rw [sqrt_two_eq, show 2 * b / 2 = b by ring]
  have hs := sin_b_pos.ne'
  have hb := b_ne_zero
  first
    | (field_simp; ring)
    | field_simp

/-- The reflection splitting of the shifted spectral sums: `4 TM(4s) = TM(s) + TMN(s)`. -/
theorem tm_split (s : ℝ) (hs0 : 0 ≤ s) (hs : 4 * s < π ^ 2) : 4 * TM (4 * s) = TM s + TMN s := by
  have hfs : Summable (tmTerm (4 * s)) := summable_tmTerm (4 * s) (by linarith) hs
  have he : Summable (fun k : ℕ => tmTerm (4 * s) (2 * k)) :=
    hfs.comp_injective (mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0))
  have ho : Summable (fun k : ℕ => tmTerm (4 * s) (2 * k + 1)) :=
    hfs.comp_injective ((add_left_injective 1).comp
      (mul_right_injective₀ (two_ne_zero : (2 : ℕ) ≠ 0)))
  have hsplit := tsum_even_add_odd he ho
  have hev : ∀ k : ℕ, 4 * tmTerm (4 * s) (2 * k) = tmnTerm s k := by
    intro k
    simp only [tmTerm, tmnTerm]
    rw [show π ^ 2 * (((2 * k : ℕ) : ℝ) + 1) ^ 2 - 4 * s =
        4 * (π ^ 2 * ((k : ℝ) + 1 / 2) ^ 2 - s) by push_cast; ring,
      mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), one_mul]
  have hod : ∀ k : ℕ, 4 * tmTerm (4 * s) (2 * k + 1) = tmTerm s k := by
    intro k
    simp only [tmTerm]
    rw [show π ^ 2 * (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2 - 4 * s =
        4 * (π ^ 2 * ((k : ℝ) + 1) ^ 2 - s) by push_cast; ring,
      mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), one_mul]
  calc 4 * TM (4 * s) = 4 * ∑' k, tmTerm (4 * s) k := rfl
    _ = 4 * ((∑' k, tmTerm (4 * s) (2 * k)) + ∑' k, tmTerm (4 * s) (2 * k + 1)) := by
        rw [hsplit]
    _ = (∑' k, 4 * tmTerm (4 * s) (2 * k)) + ∑' k, 4 * tmTerm (4 * s) (2 * k + 1) := by
        rw [mul_add, tsum_mul_left, tsum_mul_left]
    _ = TMN s + TM s := by simp only [hev, hod, TMN, TM]
    _ = TM s + TMN s := add_comm _ _

/-- `cot x - 2 cot 2x = tan x`. -/
theorem cot_sub_two_cot (x : ℝ) (hs : Real.sin x ≠ 0) (hc : Real.cos x ≠ 0) :
    Real.cos x / Real.sin x - 2 * (Real.cos (2 * x) / Real.sin (2 * x)) = Real.tan x := by
  have key := Real.sin_sq_add_cos_sq x
  rw [Real.tan_eq_sin_div_cos, Real.cos_two_mul, Real.sin_two_mul]
  have e1 : 2 * ((2 * Real.cos x ^ 2 - 1) / (2 * Real.sin x * Real.cos x)) =
      (2 * Real.cos x ^ 2 - 1) / (Real.sin x * Real.cos x) := by
    first
      | (field_simp; ring)
      | field_simp
  have e2 : Real.cos x / Real.sin x - (2 * Real.cos x ^ 2 - 1) / (Real.sin x * Real.cos x) =
      (1 - Real.cos x ^ 2) / (Real.sin x * Real.cos x) := by
    first
      | (field_simp; ring)
      | field_simp
  have e3 : (1 - Real.cos x ^ 2) = Real.sin x ^ 2 := by linarith
  rw [e1, e2, e3]
  first
    | (field_simp; ring)
    | field_simp

/-- **Proposition 8.2 (iv)**, (116): the companion identity and the Dirichlet–Neumann value. -/
theorem mt_companion :
    C0 + TMN (1 / 2) = 1 / 2 + 4 * TM 2 ∧
    1 / 2 + 4 * TM 2 = 3 / 2 - Real.sqrt 2 * (Real.cos (Real.sqrt 2) / Real.sin (Real.sqrt 2)) ∧
    TMN (1 / 2) = Real.tan b / Real.sqrt 2 := by
  have hsplit := tm_split (1 / 2) (by norm_num) (by nlinarith [Real.pi_gt_three])
  rw [show 4 * (1 / 2 : ℝ) = 2 by norm_num] at hsplit
  have hA := mt_trace
  have h2 := cot_trace (Real.sqrt 2) sqrt_two_pos sqrt_two_lt_pi
  rw [sqrt_two_sq] at h2
  have hb := cot_trace b b_pos b_lt_pi
  rw [b_sq] at hb
  refine ⟨?_, ?_, ?_⟩
  · linear_combination hA - hsplit
  · linear_combination h2
  · have hs := sin_b_pos.ne'
    have hcpos : 0 < Real.cos b :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [b_pos, Real.pi_gt_three],
        by linarith [b_lt_one, Real.pi_gt_three]⟩
    have hcot := cot_sub_two_cot b hs hcpos.ne'
    have e2b : Real.sqrt 2 = 2 * b := sqrt_two_eq
    have h2' : 2 * b * (Real.cos (2 * b) / Real.sin (2 * b)) = 1 - 4 * TM 2 := by
      rw [← e2b]
      linear_combination h2
    have hbb : b * (Real.cos b / Real.sin b) = 1 - TM (1 / 2) := by linear_combination hb
    have eT : TMN (1 / 2) = b * Real.tan b := by
      rw [← hcot]
      linear_combination -hsplit - hbb + h2'
    rw [eT, e2b, eq_div_iff (mul_ne_zero two_ne_zero b_ne_zero)]
    linear_combination (2 * Real.tan b) * b_sq

/-- The `A₂` spectral sum in the indexing of the manuscript: `∑ₙ (π²n²/4 - 1/2)⁻¹ = 4 TM(2)`. -/
theorem A2_sum : (∑' n : ℕ, (π ^ 2 * ((n : ℝ) + 1) ^ 2 / 4 - 1 / 2)⁻¹) = 4 * TM 2 := by
  unfold TM
  rw [← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  unfold tmTerm
  rw [show π ^ 2 * ((n : ℝ) + 1) ^ 2 / 4 - 1 / 2 = (π ^ 2 * ((n : ℝ) + 1) ^ 2 - 2) / 4 by ring,
    inv_div]
  ring

/-! ## Proposition 8.4: the self-dual Ising coupling -/

theorem exp_two_Kc : Real.exp (2 * Kc) = 1 + Real.sqrt 2 := by
  unfold Kc
  rw [show 2 * (Real.log (1 + Real.sqrt 2) / 2) = Real.log (1 + Real.sqrt 2) by ring,
    Real.exp_log (by linarith [sqrt_two_pos])]

theorem exp_neg_two_Kc : Real.exp (-(2 * Kc)) = Real.sqrt 2 - 1 := by
  rw [Real.exp_neg, exp_two_Kc]
  have h : (1 + Real.sqrt 2) ≠ 0 := by linarith [sqrt_two_pos]
  field_simp
  nlinarith [sqrt_two_sq]

/-- (118): `sinh 2K = 1`. -/
theorem sinh_two_Kc : Real.sinh (2 * Kc) = 1 := by
  rw [Real.sinh_eq, exp_two_Kc, exp_neg_two_Kc]
  ring

theorem cosh_two_Kc : Real.cosh (2 * Kc) = Real.sqrt 2 := by
  rw [Real.cosh_eq, exp_two_Kc, exp_neg_two_Kc]
  ring

/-- **Proposition 8.4 (ii)**, (121): `tanh 2K = |z₀| = b` and `cosh 2K = |z₁| = 1/b`. -/
theorem tanh_two_Kc : Real.tanh (2 * Kc) = b ∧ Real.cosh (2 * Kc) = 1 / b := by
  constructor
  · rw [Real.tanh_eq_sinh_div_cosh, sinh_two_Kc, cosh_two_Kc]
    rfl
  · rw [cosh_two_Kc]
    unfold b
    rw [one_div_one_div]

/-- **Proposition 8.4 (ii)**, (122): `tanh K = e^{-2K} = √2 - 1 = 2Z*`. -/
theorem tanh_Kc : Real.tanh Kc = Real.sqrt 2 - 1 ∧ Real.exp (-(2 * Kc)) = Real.sqrt 2 - 1 ∧
    2 * Zstar = Real.sqrt 2 - 1 := by
  refine ⟨?_, exp_neg_two_Kc, by unfold Zstar; ring⟩
  have he : Real.exp Kc ≠ 0 := (Real.exp_pos Kc).ne'
  have hsq : Real.exp Kc ^ 2 = 1 + Real.sqrt 2 := by
    rw [← exp_two_Kc, ← Real.exp_nat_mul]
    norm_num
  have step : Real.tanh Kc = (Real.exp Kc ^ 2 - 1) / (Real.exp Kc ^ 2 + 1) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
    have h1 : Real.exp Kc ^ 2 + 1 ≠ 0 := by positivity
    first
      | (field_simp; ring)
      | field_simp
  rw [step, hsq, div_eq_iff (by positivity)]
  linear_combination (-1 : ℝ) * sqrt_two_sq

/-- **Proposition 8.4 (ii)**: `4Z*² + 4Z* - 1 = 0`. -/
theorem Zstar_quadratic : 4 * Zstar ^ 2 + 4 * Zstar - 1 = 0 := by
  unfold Zstar
  linear_combination sqrt_two_sq

/-- `sinh 2x = 2 tanh x/(1 - tanh² x)`. -/
theorem sinh_two_mul_tanh (x : ℝ) : Real.sinh (2 * x) = 2 * Real.tanh x / (1 - Real.tanh x ^ 2) := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have key := Real.cosh_sq_sub_sinh_sq x
  have h1 : 1 - Real.tanh x ^ 2 = (Real.cosh x ^ 2)⁻¹ := by
    rw [Real.tanh_eq_sinh_div_cosh, div_pow, one_sub_div (pow_ne_zero 2 hc), key, one_div]
  rw [h1, Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
  first
    | (field_simp; ring)
    | field_simp

/-- **Proposition 8.4 (ii)**: the self-duality condition in the high-temperature variable. -/
theorem selfdual_iff (t : ℝ) (ht : t ^ 2 ≠ 1) : 2 * t / (1 - t ^ 2) = 1 ↔ t ^ 2 + 2 * t - 1 = 0 := by
  have h : 1 - t ^ 2 ≠ 0 := fun h0 => ht (by linarith)
  rw [div_eq_iff h]
  constructor <;> intro e <;> linarith

/-- **Proposition 8.4 (iii)**, (123): `arctan z₀ = 2iK`. -/
theorem arctan_z0 : Complex.arctan z0 = 2 * (Kc : ℂ) * Complex.I := by
  have hs := sqrt_two_pos.ne'
  have hs1 : Real.sqrt 2 + 1 ≠ 0 := by positivity
  have hb1 : (1 : ℝ) + b ≠ 0 := by have := b_pos; positivity
  have e1 : (1 - b) / (1 + b) = (Real.sqrt 2 - 1) / (Real.sqrt 2 + 1) := by
    rw [div_eq_div_iff hb1 hs1]
    unfold b
    first
      | (field_simp; ring)
      | field_simp
  have e2 : (Real.sqrt 2 - 1) / (Real.sqrt 2 + 1) = (Real.sqrt 2 - 1) ^ 2 := by
    rw [div_eq_iff hs1]
    linear_combination (1 - Real.sqrt 2) * sqrt_two_sq
  have e3 : Real.exp (-(4 * Kc)) = (Real.sqrt 2 - 1) ^ 2 := by
    rw [show -(4 * Kc) = -(2 * Kc) + -(2 * Kc) by ring, Real.exp_add, exp_neg_two_Kc]
    ring
  have hreal : (1 - b) / (1 + b) = Real.exp (-(4 * Kc)) := by rw [e1, e2, e3]
  have hlog : Complex.log (((1 - b) / (1 + b) : ℝ) : ℂ) = ((-(4 * Kc) : ℝ) : ℂ) := by
    rw [hreal, ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  have harg : (1 + z0 * Complex.I) / (1 - z0 * Complex.I) = (((1 - b) / (1 + b) : ℝ) : ℂ) := by
    rw [z0_eq, mul_assoc, Complex.I_mul_I]
    push_cast
    ring_nf
  unfold Complex.arctan
  rw [harg, hlog]
  push_cast
  ring

/-- **Proposition 8.4 (iii)**: the fields of `z₀` and `z₁`. -/
theorem fields_Kc : -(1 / Real.sqrt 2) = -Real.tanh (2 * Kc) ∧
    -Real.sqrt 2 = -(Real.cosh (2 * Kc) / Real.sinh (2 * Kc)) ∧
    1 / (-(1 / Real.sqrt 2)) = -Real.sqrt 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [tanh_two_Kc.1]
    rfl
  · rw [sinh_two_Kc, cosh_two_Kc, div_one]
  · rw [one_div_neg_eq_neg_one_div, one_div_one_div]

/-- **Proposition 8.4**, the arcsine moments: `(1/π)∫₀^π sin^{2n} = C(2n,n)/4ⁿ`. -/
theorem arcsine_moment (n : ℕ) :
    (∫ x in (0 : ℝ)..π, Real.sin x ^ (2 * n)) / π = (Nat.centralBinom n : ℝ) / 4 ^ n := by
  rw [integral_sin_pow_even, mul_div_cancel_left₀ _ Real.pi_ne_zero]
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih]
    have h := Nat.succ_mul_centralBinom_succ k
    have h' : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) =
        2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by exact_mod_cast h
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    have e : (Nat.centralBinom (k + 1) : ℝ) = 2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) /
        ((k : ℝ) + 1) := by
      rw [eq_div_iff hk]
      linarith
    rw [e, pow_succ]
    first
      | (field_simp; ring)
      | field_simp

/-! ## Proposition 8.6: Chebyshev, path and honeycomb constants -/

/-- `a_n = sqrtTwoAddSeries 0 n` satisfies `a_n = 2 cos(π/2^{n+1})`. -/
theorem a_eq_cos (n : ℕ) : Real.sqrtTwoAddSeries 0 n = 2 * Real.cos (π / 2 ^ (n + 1)) := by
  rw [Real.cos_pi_over_two_pow]
  ring

theorem a_two : Real.sqrtTwoAddSeries 0 2 = muHex := by
  rw [Real.sqrtTwoAddSeries_two]
  rfl

/-- **Proposition 8.6 (i)**: `T₂(a_{n+1}/2) = a_n/2`. -/
theorem T2_a (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ 2).eval (Real.sqrtTwoAddSeries 0 (n + 1) / 2) =
      Real.sqrtTwoAddSeries 0 n / 2 := by
  have h : Real.sqrtTwoAddSeries 0 (n + 1) ^ 2 = 2 + Real.sqrtTwoAddSeries 0 n := by
    simp only [Real.sqrtTwoAddSeries]
    exact Real.sq_sqrt (by linarith [Real.sqrtTwoAddSeries_zero_nonneg n])
  generalize Real.sqrtTwoAddSeries 0 (n + 1) = u at h ⊢
  rw [Polynomial.Chebyshev.T_two]
  simp
  linear_combination (1 / 2 : ℝ) * h

/-- **Proposition 8.6 (i)**: `T₂(μ/2) = |z₀|`, `T₄(μ/2) = 0` and `μ⁴ - 4μ² + 2 = 0`. -/
theorem T_muHex :
    (Polynomial.Chebyshev.T ℝ 2).eval (muHex / 2) = b ∧
    (Polynomial.Chebyshev.T ℝ 4).eval (muHex / 2) = 0 ∧
    muHex ^ 4 - 4 * muHex ^ 2 + 2 = 0 := by
  have h1 : (Polynomial.Chebyshev.T ℝ 2).eval (muHex / 2) = b := by
    have h := T2_a 1
    rw [show (1 + 1 : ℕ) = 2 from rfl, a_two, Real.sqrtTwoAddSeries_one] at h
    rw [h]
    unfold b
    rw [div_eq_div_iff two_ne_zero sqrt_two_pos.ne']
    nlinarith [sqrt_two_sq]
  have hmu2 : muHex ^ 2 = 2 + Real.sqrt 2 := by
    unfold muHex
    exact Real.sq_sqrt (by linarith [sqrt_two_pos])
  refine ⟨h1, ?_, ?_⟩
  · rw [show (4 : ℤ) = 2 * 2 by norm_num, Polynomial.Chebyshev.T_mul, Polynomial.eval_comp, h1,
      Polynomial.Chebyshev.T_two]
    simp
    rw [b_sq]
    norm_num
  · linear_combination (muHex ^ 2 - 2 + Real.sqrt 2) * hmu2 + sqrt_two_sq

/-- **Proposition 8.6 (ii)**: the eigenvector relation of the path graph `P_m`. -/
theorem path_eigen (θ : ℝ) (k : ℕ) :
    Real.sin (((k : ℝ) - 1) * θ) + Real.sin (((k : ℝ) + 1) * θ) = 2 * Real.cos θ * Real.sin (k * θ) := by
  rw [show ((k : ℝ) - 1) * θ = k * θ - θ by ring, show ((k : ℝ) + 1) * θ = k * θ + θ by ring,
    Real.sin_sub, Real.sin_add]
  ring

theorem path_boundary (m j : ℕ) :
    Real.sin (((m : ℝ) + 1) * (j * π / ((m : ℝ) + 1))) = 0 := by
  have h : ((m : ℝ) + 1) ≠ 0 := by positivity
  have e : ((m : ℝ) + 1) * (j * π / ((m : ℝ) + 1)) = (j : ℝ) * π := by
    first
      | (field_simp; ring)
      | field_simp
  rw [e]
  exact Real.sin_nat_mul_pi j

/-- **Proposition 8.6 (ii)**, (124): `U₇(λ/2) = λ(λ² - 2)(λ⁴ - 4λ² + 2)`. -/
theorem U7_factor (l : ℝ) :
    (Polynomial.Chebyshev.U ℝ 7).eval (l / 2) = l * (l ^ 2 - 2) * (l ^ 4 - 4 * l ^ 2 + 2) := by
  have u3 := Polynomial.Chebyshev.U_add_two ℝ 1
  rw [show (1 : ℤ) + 2 = 3 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num] at u3
  have u4 := Polynomial.Chebyshev.U_add_two ℝ 2
  rw [show (2 : ℤ) + 2 = 4 by norm_num, show (2 : ℤ) + 1 = 3 by norm_num] at u4
  have u5 := Polynomial.Chebyshev.U_add_two ℝ 3
  rw [show (3 : ℤ) + 2 = 5 by norm_num, show (3 : ℤ) + 1 = 4 by norm_num] at u5
  have u6 := Polynomial.Chebyshev.U_add_two ℝ 4
  rw [show (4 : ℤ) + 2 = 6 by norm_num, show (4 : ℤ) + 1 = 5 by norm_num] at u6
  have u7 := Polynomial.Chebyshev.U_add_two ℝ 5
  rw [show (5 : ℤ) + 2 = 7 by norm_num, show (5 : ℤ) + 1 = 6 by norm_num] at u7
  rw [u7, u6, u5, u4, u3, Polynomial.Chebyshev.U_two, Polynomial.Chebyshev.U_one]
  simp
  ring

/-- **Proposition 8.6 (ii)**: the zeros `2cos(jπ/8)` of `U₇(λ/2)`, `1 ≤ j ≤ 7`. -/
theorem U7_zeros (j : ℕ) (hj1 : 1 ≤ j) (hj7 : j ≤ 7) :
    (Polynomial.Chebyshev.U ℝ 7).eval (Real.cos (j * π / 8)) = 0 := by
  have h := Polynomial.Chebyshev.U_real_cos (j * π / 8) 7
  have hθ0 : 0 < (j : ℝ) * π / 8 := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    positivity
  have hθ1 : (j : ℝ) * π / 8 < π := by
    have : (j : ℝ) ≤ 7 := by exact_mod_cast hj7
    nlinarith [Real.pi_pos]
  have hs : Real.sin ((j : ℝ) * π / 8) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ0 hθ1).ne'
  have h8 : Real.sin ((((7 : ℤ) : ℝ) + 1) * ((j : ℝ) * π / 8)) = 0 := by
    rw [show (((7 : ℤ) : ℝ) + 1) * ((j : ℝ) * π / 8) = (j : ℝ) * π by push_cast; ring]
    exact Real.sin_nat_mul_pi j
  rw [h8] at h
  exact (mul_eq_zero.mp h).resolve_right hs

/-- **Proposition 8.6 (ii)**: the Perron root is `2cos(π/8) = μ`, and `±√2 = ±|z₁|` are roots. -/
theorem perron_P7 : 2 * Real.cos (π / 8) = muHex ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 7 → 2 * Real.cos (j * π / 8) ≤ 2 * Real.cos (π / 8)) ∧
    (Real.sqrt 2) * ((Real.sqrt 2) ^ 2 - 2) * ((Real.sqrt 2) ^ 4 - 4 * (Real.sqrt 2) ^ 2 + 2) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := Real.cos_pi_over_two_pow 2
    rw [Real.sqrtTwoAddSeries_two] at h
    rw [show π / 8 = π / 2 ^ (2 + 1) by norm_num, h]
    unfold muHex
    ring
  · intro j hj1 hj7
    have hj : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hj' : (j : ℝ) ≤ 7 := by exact_mod_cast hj7
    have := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ π / 8)
      (by nlinarith [Real.pi_pos] : (j : ℝ) * π / 8 ≤ π) (by nlinarith [Real.pi_pos] : π / 8 ≤ j * π / 8)
    linarith
  · rw [sqrt_two_sq]
    ring

/-- The finite Viète identity `sin x = 2ⁿ sin(x/2ⁿ) ∏_{k<n} cos(x/2^{k+1})`. -/
theorem viete_finite (x : ℝ) (n : ℕ) :
    Real.sin x = 2 ^ n * Real.sin (x / 2 ^ n) * ∏ k ∈ Finset.range n, Real.cos (x / 2 ^ (k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.prod_range_succ]
    have h : Real.sin (x / 2 ^ n) = 2 * Real.sin (x / 2 ^ (n + 1)) * Real.cos (x / 2 ^ (n + 1)) := by
      rw [← Real.sin_two_mul]
      congr 1
      rw [pow_succ]
      first
        | (field_simp; ring)
        | field_simp
    rw [h, pow_succ]
    ring

/-- **Proposition 8.6 (iii)**, (125): Viète's product `2/π = ∏ₖ cos(π/2^{k+2})`. -/
theorem viete_tendsto :
    Tendsto (fun n : ℕ => ∏ k ∈ Finset.range n, Real.cos ((π / 2) / 2 ^ (k + 1))) atTop
      (𝓝 (2 / π)) := by
  set y : ℕ → ℝ := fun n => (π / 2) / 2 ^ n with hy
  have hy0 : Tendsto y atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hypos : ∀ n, 0 < y n := fun n => by simp only [hy]; positivity
  have hyle : ∀ n, y n < π := fun n => by
    simp only [hy]
    have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hyne : Tendsto y atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hy0, Eventually.of_forall (fun n => (hypos n).ne')⟩
  have hs := Real.tendsto_sin_div_nhdsNE_zero.comp hyne
  have hlim : Tendsto (fun n => (2 / π) * (Real.sin (y n) / y n)⁻¹) atTop (𝓝 ((2 / π) * 1⁻¹)) :=
    (hs.inv₀ one_ne_zero).const_mul (2 / π)
  rw [inv_one, mul_one] at hlim
  refine hlim.congr (fun n => ?_)
  have hyv : y n = (π / 2) / 2 ^ n := rfl
  have hsin : Real.sin ((π / 2) / 2 ^ n) ≠ 0 := by
    rw [← hyv]
    exact (Real.sin_pos_of_pos_of_lt_pi (hypos n) (hyle n)).ne'
  have hv := viete_finite (π / 2) n
  rw [Real.sin_pi_div_two] at hv
  have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hP : ∏ k ∈ Finset.range n, Real.cos ((π / 2) / 2 ^ (k + 1)) =
      1 / (2 ^ n * Real.sin ((π / 2) / 2 ^ n)) := by
    rw [eq_div_iff (mul_ne_zero hpow hsin)]
    linear_combination -hv
  rw [hP, hyv]
  have hπ := Real.pi_ne_zero
  first
    | (field_simp; ring)
    | field_simp

/-- **Proposition 8.6 (iii)**: the first two factors of Viète's product are `|z₀|` and `μ/2`. -/
theorem viete_factors : Real.cos ((π / 2) / 2 ^ (0 + 1)) = b ∧
    Real.cos ((π / 2) / 2 ^ (1 + 1)) = muHex / 2 := by
  constructor
  · rw [show (π / 2) / 2 ^ (0 + 1) = π / 4 by ring, Real.cos_pi_div_four]
    unfold b
    rw [div_eq_div_iff two_ne_zero sqrt_two_pos.ne']
    nlinarith [sqrt_two_sq]
  · rw [show (π / 2) / 2 ^ (1 + 1) = π / 2 ^ (2 + 1) by ring, Real.cos_pi_over_two_pow,
      Real.sqrtTwoAddSeries_two]
    rfl

/-! ## Proposition 8.7: the square-lattice return counts -/

/-- `(2n)!/(j!²(n-j)!²) = C(2n,n) C(n,j)²`. -/
theorem walk_term (n j : ℕ) (hj : j ≤ n) :
    ((2 * n).factorial : ℚ) / ((j.factorial : ℚ) ^ 2 * ((n - j).factorial : ℚ) ^ 2) =
      ((2 * n).choose n : ℚ) * ((n.choose j : ℚ)) ^ 2 := by
  have h1 : ((n.choose j : ℚ)) * (j.factorial : ℚ) * ((n - j).factorial : ℚ) = (n.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  have h2 : ((2 * n).choose n : ℚ) * (n.factorial : ℚ) * (n.factorial : ℚ) = ((2 * n).factorial : ℚ) := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at this
    exact_mod_cast this
  have hj0 : (j.factorial : ℚ) ≠ 0 := by positivity
  have hnj0 : ((n - j).factorial : ℚ) ≠ 0 := by positivity
  rw [div_eq_iff (by positivity), ← h2, ← h1]
  ring

/-- **Proposition 8.7**, (127): `∑ⱼ (2n)!/(j!²(n-j)!²) = C(2n,n)²`. -/
theorem walk_count (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1),
      ((2 * n).factorial : ℚ) / ((j.factorial : ℚ) ^ 2 * ((n - j).factorial : ℚ) ^ 2) =
      ((2 * n).choose n : ℚ) ^ 2 := by
  rw [Finset.sum_congr rfl (fun j hj => walk_term n j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))),
    ← Finset.mul_sum]
  have h := Nat.sum_range_choose_sq n
  have h' : (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℚ)) ^ 2) = ((2 * n).choose n : ℚ) := by
    exact_mod_cast h
  rw [h']
  ring

/-- `(1/2)ₙ 4ⁿ n! = (2n)!`. -/
theorem poch_half (n : ℕ) :
    (∏ k ∈ Finset.range n, ((1 : ℝ) / 2 + k)) * 4 ^ n * (n.factorial : ℝ) = ((2 * n).factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e1 : (2 * (n + 1)).factorial = (2 * n + 2) * ((2 * n + 1) * (2 * n).factorial) := by
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    have e2 : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
    rw [Finset.prod_range_succ, e1, e2]
    push_cast
    rw [← ih]
    ring

/-- **Proposition 8.7**, (129): `(1/2)ₙ² 16ⁿ/(n!)² = C(2n,n)²`. -/
theorem hyper_coeff (n : ℕ) :
    (∏ k ∈ Finset.range n, ((1 : ℝ) / 2 + k)) ^ 2 * 16 ^ n / (n.factorial : ℝ) ^ 2 =
      ((2 * n).choose n : ℝ) ^ 2 := by
  have h := poch_half n
  have h2 : ((2 * n).choose n : ℝ) * (n.factorial : ℝ) * (n.factorial : ℝ) = ((2 * n).factorial : ℝ) := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at this
    exact_mod_cast this
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have e : (∏ k ∈ Finset.range n, ((1 : ℝ) / 2 + k)) * 4 ^ n = ((2 * n).choose n : ℝ) * (n.factorial : ℝ) := by
    apply mul_right_cancel₀ hf
    rw [h, ← h2]
  have h16 : (16 : ℝ) ^ n = (4 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm n 2, pow_mul]
    norm_num
  rw [div_eq_iff (pow_ne_zero 2 hf), h16, ← mul_pow, e]
  ring

/-! ## Section 9: time reversal, the Bloch map and the Brillouin splitting -/

/-- Time reversal of a spin one half, `Θψ = -iσ₂ψ̄ = (-ψ̄₁, ψ̄₀)`. -/
def Θ (ψ : Fin 2 → ℂ) : Fin 2 → ℂ := ![-conj (ψ 1), conj (ψ 0)]

/-- The Hermitian product of `ℂ²`, antilinear in the first variable. -/
def inner2 (φ ψ : Fin 2 → ℂ) : ℂ := conj (φ 0) * ψ 0 + conj (φ 1) * ψ 1

/-- The Pauli matrices acting on `ℂ²`. -/
def sigma1 (ψ : Fin 2 → ℂ) : Fin 2 → ℂ := ![ψ 1, ψ 0]

def sigma2 (ψ : Fin 2 → ℂ) : Fin 2 → ℂ := ![-Complex.I * ψ 1, Complex.I * ψ 0]

def sigma3 (ψ : Fin 2 → ℂ) : Fin 2 → ℂ := ![ψ 0, -ψ 1]

/-- **Lemma 9.2**: `Θ² = -1`. -/
theorem Θ_Θ (ψ : Fin 2 → ℂ) : Θ (Θ ψ) = -ψ := by
  funext i
  fin_cases i <;> simp [Θ]

/-- **Lemma 9.2**: `⟨ψ, Θψ⟩ = 0`. -/
theorem inner_Θ (ψ : Fin 2 → ℂ) : inner2 ψ (Θ ψ) = 0 := by
  simp only [inner2, Θ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- **Lemma 9.2**: `Θ` is antiunitary. -/
theorem Θ_antiunitary (φ ψ : Fin 2 → ℂ) : inner2 (Θ φ) (Θ ψ) = conj (inner2 φ ψ) := by
  simp only [inner2, Θ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, map_add,
    map_mul, map_neg, Complex.conj_conj]
  ring

theorem Θ_antilinear (c : ℂ) (φ ψ : Fin 2 → ℂ) : Θ (c • φ + ψ) = conj c • Θ φ + Θ ψ := by
  funext i
  fin_cases i <;> simp [Θ] <;> ring

/-- **Lemma 9.2**: `Θσⱼ = -σⱼΘ` for `j = 1, 2, 3`. -/
theorem Θ_sigma (ψ : Fin 2 → ℂ) :
    Θ (sigma1 ψ) = -sigma1 (Θ ψ) ∧ Θ (sigma2 ψ) = -sigma2 (Θ ψ) ∧ Θ (sigma3 ψ) = -sigma3 (Θ ψ) := by
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;> simp [Θ, sigma1, sigma2, sigma3] <;> ring

/-- **Lemma 9.2**: time reversal has no fixed ray. -/
theorem Θ_no_fixed_ray (ψ : Fin 2 → ℂ) (hψ : ψ ≠ 0) (c : ℂ) : Θ ψ ≠ c • ψ := by
  intro h
  have h1 : inner2 ψ (c • ψ) = 0 := by rw [← h]; exact inner_Θ ψ
  have h2 : inner2 ψ (c • ψ) = c * ((Complex.normSq (ψ 0) + Complex.normSq (ψ 1) : ℝ) : ℂ) := by
    simp only [inner2, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    ring
  have hN : (Complex.normSq (ψ 0) + Complex.normSq (ψ 1)) ≠ 0 := by
    intro h0
    apply hψ
    have a0 : Complex.normSq (ψ 0) = 0 := by
      linarith [Complex.normSq_nonneg (ψ 0), Complex.normSq_nonneg (ψ 1)]
    have a1 : Complex.normSq (ψ 1) = 0 := by
      linarith [Complex.normSq_nonneg (ψ 0), Complex.normSq_nonneg (ψ 1)]
    funext i
    fin_cases i
    · simpa using Complex.normSq_eq_zero.mp a0
    · simpa using Complex.normSq_eq_zero.mp a1
  rw [h2] at h1
  have hc : c = 0 := by
    rcases mul_eq_zero.mp h1 with h3 | h3
    · exact h3
    · exact absurd (Complex.ofReal_eq_zero.mp h3) hN
  rw [hc, zero_smul] at h
  have h4 : Θ (Θ ψ) = 0 := by
    rw [h]
    funext i
    fin_cases i <;> simp [Θ]
  rw [Θ_Θ] at h4
  exact hψ (neg_eq_zero.mp h4)

/-- **Lemma 9.2**: the affine action `ζ ↦ -1/ζ̄` and its absence of fixed points. -/
theorem Θ_affine (ψ : Fin 2 → ℂ) (h0 : ψ 0 ≠ 0) (h1 : ψ 1 ≠ 0) :
    (Θ ψ) 1 / (Θ ψ) 0 = -1 / conj (ψ 1 / ψ 0) := by
  have h1' : conj (ψ 1) ≠ 0 := (map_ne_zero _).mpr h1
  have h0' : conj (ψ 0) ≠ 0 := (map_ne_zero _).mpr h0
  simp only [Θ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, map_div₀]
  first
    | (field_simp; ring)
    | field_simp

theorem affine_no_fixed (ζ : ℂ) (hζ : ζ ≠ 0) : ζ ≠ -1 / conj ζ := by
  intro h
  have hc : conj ζ ≠ 0 := (map_ne_zero _).mpr hζ
  have h2 : ζ * conj ζ = -1 := by
    rw [eq_div_iff hc] at h
    exact h
  rw [Complex.mul_conj] at h2
  have h3 := congrArg Complex.re h2
  simp at h3
  linarith [Complex.normSq_nonneg ζ]

/-- The Bloch numerators `ψ†σⱼψ` and the norm `ψ†ψ`. -/
def blochNum (ψ : Fin 2 → ℂ) : Fin 3 → ℝ :=
  ![2 * (conj (ψ 0) * ψ 1).re, 2 * (conj (ψ 0) * ψ 1).im, Complex.normSq (ψ 0) - Complex.normSq (ψ 1)]

def nrm (ψ : Fin 2 → ℂ) : ℝ := Complex.normSq (ψ 0) + Complex.normSq (ψ 1)

/-- The Bloch map `ω([ψ]) = ψ†σψ/ψ†ψ`. -/
def bloch (ψ : Fin 2 → ℂ) : Fin 3 → ℝ := fun i => blochNum ψ i / nrm ψ

/-- **Definition 9.1**: the numerators are the expectations of the Pauli matrices. -/
theorem bloch_expectations (ψ : Fin 2 → ℂ) :
    inner2 ψ (sigma1 ψ) = (blochNum ψ 0 : ℂ) ∧ inner2 ψ (sigma2 ψ) = (blochNum ψ 1 : ℂ) ∧
    inner2 ψ (sigma3 ψ) = (blochNum ψ 2 : ℂ) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    apply Complex.ext <;>
    simp [inner2, sigma1, sigma2, sigma3, blochNum, Complex.normSq_apply] <;> ring

theorem nrm_Θ (ψ : Fin 2 → ℂ) : nrm (Θ ψ) = nrm ψ := by
  simp only [nrm, Θ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Complex.normSq_neg, Complex.normSq_conj]
  ring

theorem blochNum_Θ (ψ : Fin 2 → ℂ) : blochNum (Θ ψ) = -blochNum ψ := by
  funext i
  fin_cases i <;> simp [blochNum, Θ] <;> ring

/-- **Theorem 9.3**, (131): `ω_B ∘ Θ = -ω_B`. -/
theorem bloch_Θ (ψ : Fin 2 → ℂ) : bloch (Θ ψ) = -bloch ψ := by
  funext i
  simp only [bloch, nrm_Θ, blochNum_Θ, Pi.neg_apply, neg_div]

/-- **Theorem 9.3**: the Bloch vector of a nonzero spinor is a unit vector. -/
theorem bloch_unit (ψ : Fin 2 → ℂ) (h : nrm ψ ≠ 0) :
    bloch ψ 0 ^ 2 + bloch ψ 1 ^ 2 + bloch ψ 2 ^ 2 = 1 := by
  have hw : (conj (ψ 0) * ψ 1).re ^ 2 + (conj (ψ 0) * ψ 1).im ^ 2 =
      Complex.normSq (ψ 0) * Complex.normSq (ψ 1) := by
    rw [← Complex.normSq_conj (ψ 0), ← Complex.normSq_mul, Complex.normSq_apply]
    ring
  have e0 : bloch ψ 0 = 2 * (conj (ψ 0) * ψ 1).re / nrm ψ := rfl
  have e1 : bloch ψ 1 = 2 * (conj (ψ 0) * ψ 1).im / nrm ψ := rfl
  have e2 : bloch ψ 2 = (Complex.normSq (ψ 0) - Complex.normSq (ψ 1)) / nrm ψ := rfl
  rw [e0, e1, e2, div_pow, div_pow, div_pow, ← add_div, ← add_div,
    div_eq_one_iff_eq (pow_ne_zero 2 h)]
  unfold nrm
  linear_combination 4 * hw

/-- The Brillouin function `B_J(y)` of Van Vleck, Chapter IX, §61, Eq. (26). -/
def Bril (J y : ℝ) : ℝ := (2 * J + 1) / (2 * J) * coth ((2 * J + 1) * y / (2 * J)) -
  1 / (2 * J) * coth (y / (2 * J))

/-- **Proposition 9.5 (ii)**, (137): `B_{1/2}(y) = 2coth 2y - coth y = tanh y = 2L(2y) - L(y)`. -/
theorem Bril_half (y : ℝ) (hy : y ≠ 0) :
    Bril (1 / 2) y = 2 * coth (2 * y) - coth y ∧ 2 * coth (2 * y) - coth y = Real.tanh y ∧
    2 * coth (2 * y) - coth y = 2 * Lval (2 * y) - Lval y := by
  have hs : Real.sinh y ≠ 0 := Real.sinh_ne_zero.mpr hy
  have hc : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  refine ⟨?_, ?_, ?_⟩
  · unfold Bril
    rw [show (2 * (1 / 2 : ℝ) + 1) / (2 * (1 / 2)) = 2 by norm_num,
      show (2 * (1 / 2 : ℝ) + 1) * y / (2 * (1 / 2)) = 2 * y by ring,
      show y / (2 * (1 / 2 : ℝ)) = y by ring, show (1 : ℝ) / (2 * (1 / 2)) = 1 by norm_num]
    ring
  · simp only [coth, Real.cosh_two_mul, Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
    first
      | (field_simp; ring)
      | field_simp
  · unfold Lval
    ring

/-- **Proposition 9.5 (ii)**, (138): the dipole of doubled moment as dipole and spin one half. -/
theorem product_split (x : ℝ) (hx : x ≠ 0) :
    Real.sinh (2 * x) / (2 * x) = Real.sinh x / x * ((Real.exp x + Real.exp (-x)) / 2) := by
  rw [← Real.cosh_eq, Real.sinh_two_mul]
  first
    | (field_simp; ring)
    | field_simp

/-- The thermal operator `exp(xσ₃) = diag(eˣ, e⁻ˣ)` of the spin one half. -/
def thermal (x : ℝ) (ψ : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![(Real.exp x : ℂ) * ψ 0, (Real.exp (-x) : ℂ) * ψ 1]

/-- **Proposition 9.5 (i)**, (135): half the trace is `cosh x`. -/
theorem thermal_trace (x : ℝ) : (Real.exp x + Real.exp (-x)) / 2 = Real.cosh x :=
  (Real.cosh_eq x).symm

/-- **Proposition 9.5 (i)**: time reversal maps the thermal state in the field `x` to that in `-x`. -/
theorem Θ_thermal (x : ℝ) (ψ : Fin 2 → ℂ) : Θ (thermal x ψ) = thermal (-x) (Θ ψ) := by
  funext i
  fin_cases i <;> first
    | (simp [Θ, thermal, ← Complex.exp_conj]; done)
    | (simp [Θ, thermal, ← Complex.exp_conj]; ring)
    | (simp only [Θ, thermal, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.zero_eta,
        Fin.mk_one, map_mul, map_neg, Complex.conj_ofReal, neg_neg]; ring)

/-! ## Proposition 9.7: comparison of the involutions -/

/-- **Proposition 9.7 (i)**: a conjugating injection maps fixed points to fixed points. -/
theorem conj_fixed {X Y : Type*} (h : X → Y) (hinj : Function.Injective h) (τ : X → X)
    (σ : Y → Y) (hc : ∀ x, h (τ x) = σ (h x)) (x : X) : τ x = x ↔ σ (h x) = h x := by
  rw [← hc]
  exact hinj.eq_iff.symm

/-- **Proposition 9.7 (iii)**: `S` fixes exactly the point `i` of `ℍ`. -/
theorem S_fixed (τ : ℂ) (hτ : 0 < τ.im) : S τ = τ ↔ τ = Complex.I := by
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_im] at hτ
    exact lt_irrefl 0 hτ
  unfold S
  rw [div_eq_iff hτ0]
  constructor
  · intro h
    have h2 : τ ^ 2 = Complex.I ^ 2 := by
      rw [Complex.I_sq]
      linear_combination -h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h3 | h3
    · exact h3
    · rw [h3, Complex.neg_im, Complex.I_im] at hτ
      linarith
  · intro h
    rw [h, Complex.I_mul_I]

/-- **Proposition 9.7 (iii)**: the conjugation fixes exactly the real axis. -/
theorem conj_fixed_real (z : ℂ) : conj z = z ↔ z.im = 0 := Complex.conj_eq_iff_im

/-- **Proposition 9.7 (iv)**: the three half-line inversions are conjugate. -/
theorem inversions_conjugate (s Z0 : ℝ) (hs : s ≠ 0) (hZ : Z0 ≠ 0) :
    1 / (-s) = -(1 / s) ∧ Z0 ^ 2 / (4 * (Z0 * s / 2)) = Z0 * (1 / s) / 2 := by
  constructor
  · rw [one_div_neg_eq_neg_one_div]
  · first
      | (field_simp; ring)
      | field_simp

/-- **Proposition 9.7 (iv)**: the fixed point of `s ↦ 1/s` on `(0, ∞)` is `s = 1`. -/
theorem inversion_fixed (s : ℝ) (hs : 0 < s) : 1 / s = s ↔ s = 1 := by
  rw [div_eq_iff hs.ne']
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h]
    ring

/-! ## Axiom audit -/

#print axioms deck
#print axioms rE_factor
#print axioms rE_neg
#print axioms mag_neg
#print axioms lift_parity
#print axioms unique_in_H
#print axioms E_neg_quarter
#print axioms actions_agree
#print axioms mt_trace
#print axioms mt_complex
#print axioms mt_logderiv
#print axioms mt_companion
#print axioms tanh_two_Kc
#print axioms tanh_Kc
#print axioms Zstar_quadratic
#print axioms arctan_z0
#print axioms arcsine_moment
#print axioms T_muHex
#print axioms U7_factor
#print axioms U7_zeros
#print axioms perron_P7
#print axioms viete_tendsto
#print axioms walk_count
#print axioms hyper_coeff
#print axioms Θ_Θ
#print axioms Θ_antiunitary
#print axioms Θ_sigma
#print axioms Θ_no_fixed_ray
#print axioms bloch_Θ
#print axioms bloch_unit
#print axioms Bril_half
#print axioms Θ_thermal
#print axioms S_fixed

end Manuscript14Section89
