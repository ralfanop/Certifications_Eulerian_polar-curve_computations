/-
# Algebraic and order-theoretic core of Corollary 3.8 and Theorems 3.12–3.13 (V478)

* Cor. 3.8: polar-curvature numerator of `b + a cos θ`, its minimum `(b-a)(b-2a)`, and the
  inequality chain `b_E > 2/π > 32/(3π³) > 2 a_E` from the bounds of Prop. 3.1.
* Thm 3.12: `c - 2m = 3/π - 1/2 > 0`, and the three-point uniqueness argument for the
  radial minimax affine function.
* Thm 3.13: the endpoint-containment inequality (Eqs. 73–74), the identification of `(a,b)` when
  both endpoint bounds are equalities, and the scalar-balance lemma: if `Q` is antitone then
  `Q h - h` is strictly decreasing, has at most one zero, `Q D ≤ D` forces `D ≥ h_*`, and
  `Q L > L`, `Q U < U` bracket `h_*` (this is the logical step used by the numerical
  certificate of Eq. 70).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds

open Real

namespace EulerianCert.Limacon

/-! ### Corollary 3.8 -/

/-- Derivatives of the limaçon radius. -/
lemma hasDerivAt_limacon (a b θ : ℝ) :
    HasDerivAt (fun t => b + a * Real.cos t) (-a * Real.sin θ) θ := by
  have := ((Real.hasDerivAt_cos θ).const_mul a).const_add b
  convert this using 1; ring

lemma hasDerivAt_limacon' (a θ : ℝ) :
    HasDerivAt (fun t => -a * Real.sin t) (-a * Real.cos θ) θ :=
  (Real.hasDerivAt_sin θ).const_mul (-a)

/-- The polar-curvature numerator `r² + 2r'² - r r''` for `r = b + a cos θ`. -/
lemma limacon_numerator (a b θ : ℝ) :
    (b + a * Real.cos θ) ^ 2 + 2 * (-a * Real.sin θ) ^ 2 - (b + a * Real.cos θ) * (-a * Real.cos θ)
      = b ^ 2 + 3 * a * b * Real.cos θ + 2 * a ^ 2 := by
  have h := Real.sin_sq_add_cos_sq θ
  linear_combination 2 * a ^ 2 * h

/-- Its minimum over `θ` is `(b - a)(b - 2a)` when `a b ≥ 0`. -/
lemma limacon_numerator_ge (a b θ : ℝ) (hab : 0 ≤ a * b) :
    (b - a) * (b - 2 * a) ≤ b ^ 2 + 3 * a * b * Real.cos θ + 2 * a ^ 2 := by
  have := Real.neg_one_le_cos θ
  nlinarith

/-- Strict positivity of the curvature numerator for `b > 2a > 0`, i.e. strict convexity. -/
lemma limacon_numerator_pos (a b θ : ℝ) (ha : 0 < a) (hb : 2 * a < b) :
    0 < b ^ 2 + 3 * a * b * Real.cos θ + 2 * a ^ 2 := by
  have h1 : 0 < (b - a) * (b - 2 * a) := mul_pos (by linarith) (by linarith)
  exact lt_of_lt_of_le h1 (limacon_numerator_ge a b θ (by nlinarith))

/-- The inequality chain of Cor. 3.8: `2/π > 32/(3π³)`. -/
lemma two_div_pi_gt : 32 / (3 * π ^ 3) < 2 / π := by
  have hπ := Real.pi_gt_three
  have hp : 0 < π := Real.pi_pos
  rw [div_lt_div_iff₀ (by positivity) hp]
  nlinarith [sq_nonneg π]

/-- Cor. 3.8, given the bounds `0 < a_E < 16/(3π³)` (Prop. 3.1, `n = 1`) and `b_E > 2/π`
(mean of `r_E > 2/π`): `b_E > 2 a_E > 0`. -/
theorem convexity_chain (aE bE : ℝ) (ha0 : 0 < aE) (ha : aE < 16 / (3 * π ^ 3))
    (hb : 2 / π < bE) : 2 * aE < bE ∧ 0 < 2 * aE := by
  have := two_div_pi_gt
  constructor
  · have : 2 * aE < 32 / (3 * π ^ 3) := by
      have : 2 * (16 / (3 * π ^ 3)) = 32 / (3 * π ^ 3) := by ring
      linarith
    linarith
  · linarith

/-! ### Theorem 3.12 -/

/-- Constants of Eq. (58). -/
noncomputable def q : ℝ := 2 / π
noncomputable def c : ℝ := (1 + q) / 2
noncomputable def m : ℝ := (1 - q) / 2

lemma c_sub_two_m : c - 2 * m = 3 / π - 1 / 2 := by
  unfold c m q; ring

lemma c_sub_two_m_pos : 0 < c - 2 * m := by
  rw [c_sub_two_m]
  have hπ := Real.pi_lt_four
  have hp := Real.pi_pos
  have : 3 / π > 3 / 4 := by
    rw [gt_iff_lt, div_lt_div_iff₀ (by norm_num) hp]; linarith
  linarith

lemma m_pos : 0 < m := by
  unfold m q
  have : 2 / π < 1 := by rw [div_lt_one Real.pi_pos]; linarith [Real.pi_gt_three]
  linarith

/-- Three-point uniqueness (proof of Thm 3.12).  Let `f(-1) = q`, `f(1) = 1`, let the chord be
`ℓ(x) = c + m x`, let `x* ∈ (-1,1)` with `f(x*) = ℓ(x*) + 2ε`.  If the affine `p(x) = β + α x`
satisfies `|f - p| ≤ ε` at the three points, then `α = m` and `β = c + ε`. -/
theorem affine_unique (ε xs fxs α β : ℝ) (hx1 : -1 < xs) (hx2 : xs < 1)
    (hfx : fxs = c + m * xs + 2 * ε)
    (h1 : |q - (β + α * (-1))| ≤ ε) (h2 : |1 - (β + α * 1)| ≤ ε)
    (h3 : |fxs - (β + α * xs)| ≤ ε) :
    α = m ∧ β = c + ε := by
  have e1 := (abs_le.1 h1).1
  have e2 := (abs_le.1 h2).1
  have e3 := (abs_le.1 h3).2
  unfold c m at hfx ⊢
  have l1 : 0 < (1 - xs) / 2 := by linarith
  have l2 : 0 < (1 + xs) / 2 := by linarith
  have A : β - α ≤ q + ε := by linarith
  have B : β + α ≤ 1 + ε := by linarith
  have C : (1 + q) / 2 + (1 - q) / 2 * xs + ε ≤ β + α * xs := by linarith
  have id1 : (1 - xs) / 2 * ((q + ε) - (β - α)) + (1 + xs) / 2 * ((1 + ε) - (β + α))
      = ((1 + q) / 2 + (1 - q) / 2 * xs + ε) - (β + α * xs) := by ring
  have t1 := mul_nonneg l1.le (sub_nonneg.2 A)
  have t2 := mul_nonneg l2.le (sub_nonneg.2 B)
  have z1 : (1 - xs) / 2 * ((q + ε) - (β - α)) = 0 := by linarith
  have z2 : (1 + xs) / 2 * ((1 + ε) - (β + α)) = 0 := by linarith
  have eA : (q + ε) - (β - α) = 0 := (mul_eq_zero.1 z1).resolve_left l1.ne'
  have eB : (1 + ε) - (β + α) = 0 := (mul_eq_zero.1 z2).resolve_left l2.ne'
  constructor <;> linarith

/-! ### Theorem 3.13 -/

/-- Endpoint containment, Eqs. (73)–(74): the two endpoint bounds imply radial containment in
`Ω_D` at every angle. -/
theorem endpoint_containment (a b D t : ℝ) (h1 : b + a ≤ 1 + D) (h2 : b - a ≤ q + D) :
    b + a * Real.cos t ≤ c + D + m * Real.cos t := by
  have w1 : 0 ≤ (1 + Real.cos t) / 2 := by linarith [Real.neg_one_le_cos t]
  have w2 : 0 ≤ (1 - Real.cos t) / 2 := by linarith [Real.cos_le_one t]
  have p1 := mul_le_mul_of_nonneg_left h1 w1
  have p2 := mul_le_mul_of_nonneg_left h2 w2
  have e1 : b + a * Real.cos t =
      (1 + Real.cos t) / 2 * (b + a) + (1 - Real.cos t) / 2 * (b - a) := by ring
  have e2 : c + D + m * Real.cos t =
      (1 + Real.cos t) / 2 * (1 + D) + (1 - Real.cos t) / 2 * (q + D) := by unfold c m; ring
  rw [e1, e2]
  linarith

/-- If either endpoint bound is strict, containment is strict at every off-axis angle. -/
theorem endpoint_containment_strict (a b D t : ℝ) (h1 : b + a ≤ 1 + D) (h2 : b - a ≤ q + D)
    (hs : b + a < 1 + D ∨ b - a < q + D) (ht1 : Real.cos t ≠ 1) (ht2 : Real.cos t ≠ -1) :
    b + a * Real.cos t < c + D + m * Real.cos t := by
  have hc1 : Real.cos t < 1 := lt_of_le_of_ne (Real.cos_le_one t) ht1
  have hc2 : -1 < Real.cos t := lt_of_le_of_ne (Real.neg_one_le_cos t) (Ne.symm ht2)
  have w1 : 0 < (1 + Real.cos t) / 2 := by linarith
  have w2 : 0 < (1 - Real.cos t) / 2 := by linarith
  have e1 : b + a * Real.cos t =
      (1 + Real.cos t) / 2 * (b + a) + (1 - Real.cos t) / 2 * (b - a) := by ring
  have e2 : c + D + m * Real.cos t =
      (1 + Real.cos t) / 2 * (1 + D) + (1 - Real.cos t) / 2 * (q + D) := by unfold c m; ring
  rw [e1, e2]
  rcases hs with hs | hs
  · have := mul_lt_mul_of_pos_left hs w1
    have := mul_le_mul_of_nonneg_left h2 w2.le
    linarith
  · have := mul_le_mul_of_nonneg_left h1 w1.le
    have := mul_lt_mul_of_pos_left hs w2
    linarith

/-- Both endpoint bounds equalities determine the limaçon: `a = m`, `b = c + D`. -/
theorem endpoint_equalities (a b D : ℝ) (h1 : b + a = 1 + D) (h2 : b - a = q + D) :
    a = m ∧ b = c + D := by
  unfold c m; constructor <;> linarith

/-- Scalar balance.  If `Q` is antitone, then `h ↦ Q h - h` is strictly antitone. -/
lemma balance_strictAnti (Q : ℝ → ℝ) (hQ : Antitone Q) : StrictAnti (fun h => Q h - h) := by
  intro x y hxy
  have := hQ hxy.le
  simp only
  linarith

/-- At most one balance point. -/
theorem balance_unique (Q : ℝ → ℝ) (hQ : Antitone Q) (h₁ h₂ : ℝ)
    (e₁ : Q h₁ = h₁) (e₂ : Q h₂ = h₂) : h₁ = h₂ :=
  (balance_strictAnti Q hQ).injective (by simp only [e₁, e₂, sub_self])

/-- Global lower bound: `Q D ≤ D` and `Q h* = h*` force `h* ≤ D`. -/
theorem balance_lower (Q : ℝ → ℝ) (hQ : Antitone Q) (hs D : ℝ) (es : Q hs = hs)
    (hD : Q D ≤ D) : hs ≤ D := by
  by_contra hlt
  push Not at hlt
  have := balance_strictAnti Q hQ hlt
  simp only at this
  linarith

/-- **Logic of the numerical certificate for Eq. (70).**  If `Q` is antitone,
`Q h* = h*`, `Q L > L` and `Q U < U`, then `L < h* < U`. -/
theorem balance_bracket (Q : ℝ → ℝ) (hQ : Antitone Q) (hs L U : ℝ) (es : Q hs = hs)
    (hL : L < Q L) (hU : Q U < U) : L < hs ∧ hs < U := by
  have S := balance_strictAnti Q hQ
  constructor
  · by_contra h; push Not at h
    rcases h.lt_or_eq with h | h
    · have := S h; simp only at this; linarith
    · rw [← h] at hL; linarith
  · by_contra h; push Not at h
    rcases h.lt_or_eq with h | h
    · have := S h; simp only at this; linarith
    · rw [h] at hU; linarith

/-- Strict comparison with the radial optimum, Eq. (71): if `Q ε < ε` then `h* < ε`. -/
theorem balance_lt (Q : ℝ → ℝ) (hQ : Antitone Q) (hs ε : ℝ) (es : Q hs = hs)
    (hε : Q ε < ε) : hs < ε := by
  by_contra h; push Not at h
  rcases h.lt_or_eq with h | h
  · have := balance_strictAnti Q hQ h; simp only at this; linarith
  · rw [h] at hε; linarith

end EulerianCert.Limacon
