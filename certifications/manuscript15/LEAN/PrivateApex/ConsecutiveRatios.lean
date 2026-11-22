import PrivateApex.AngleAllOrders
import Mathlib.Analysis.SpecificLimits.Basic

/-!
PRIVATE.  Manuscript 15, Section 7: ratios of consecutive central slopes and of the
corresponding angular deficits `π - α`.

Three kinds of series occur and are kept apart.

* **Convergent series.**  For even `n` and `N = n + 1 > 3` the ratio `t_n / s_{n+1}` is the
  rational function `2 N² / ((N+1)(N+3))` (`slope_ratio_even_exact`), and
  `t_n / s_{n+1} = 2 + ∑_{j ≥ 1} (-1)^j (3^(j+1) - 1) / N^j` is a convergent series
  (`slope_ratio_even_hasSum`).
* **Asymptotic expansions.**  The ratio `t_{n+1} / s_n` for odd `n` (`slope_ratio_odd_hasExp`)
  and the two ratios of angular deficits (`deficit_ratio_even_hasExp`,
  `deficit_ratio_odd_hasExp`) have expansions to every order in the sense of `HasExp`; no
  convergence is claimed.
* **Formal series.**  The coefficients are obtained by the formal operations `cmul`, `ccomp`
  and the reciprocal `cinv`.  For `t_{n+1} / s_n` they are rational and are evaluated by the
  kernel up to the sixth order (`slopeRatioOddQ_values`); for the deficit ratios they are
  polynomials in `1/π`, and the first two are made explicit.
-/

namespace PrivateApex
open Real Finset

/-! ### Reciprocals of expansions -/

/-- Coefficients of the reciprocal of a series with invertible constant term. -/
def cinv {K : Type*} [Field K] (b : ℕ → K) (m : ℕ) : K :=
  1 / b 0 * ccomp (fun i => (-1) ^ i) (fun i => 1 / b 0 * b (i + 1)) m

theorem map_cinv {K L : Type*} [Field K] [Field L] (φ : K →+* L) (b : ℕ → K) (m : ℕ) :
    φ (cinv b m) = cinv (fun i => φ (b i)) m := by
  unfold cinv
  rw [map_mul, map_ccomp]
  simp only [map_div₀, map_one, map_mul, map_pow, map_neg]

section
variable {α : Type*} {S : Set α} {w : α → ℝ}

theorem geo_hasExp_lower {u : α → ℝ} {c : ℝ} (hc : 0 < c) (hu : ∀ x ∈ S, c ≤ 1 + u x) :
    HasExp S u (fun x => 1 / (1 + u x)) (fun i => (-1 : ℝ) ^ i) := by
  intro P
  refine ⟨1 / c, fun x hx => ?_⟩
  have hpos : 0 < 1 + u x := lt_of_lt_of_le hc (hu x hx)
  have e : 1 / (1 + u x) - ∑ i ∈ range P, (-1 : ℝ) ^ i * u x ^ i = (-u x) ^ P / (1 + u x) := by
    have hgeo : ∑ i ∈ range P, (-1 : ℝ) ^ i * u x ^ i = ∑ i ∈ range P, (-u x) ^ i :=
      sum_congr rfl fun i _ => by rw [neg_pow (u x) i]
    have hq := geom_sum_mul (-u x) P
    rw [hgeo, eq_div_iff hpos.ne', sub_mul, one_div_mul_cancel hpos.ne']
    linear_combination hq
  rw [e, abs_div, abs_of_pos hpos, abs_pow, abs_neg, div_le_iff₀ hpos]
  have h1 : 1 ≤ 1 / c * (1 + u x) := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc]
    linarith [hu x hx]
  calc |u x| ^ P = |u x| ^ P * 1 := (mul_one _).symm
    _ ≤ |u x| ^ P * (1 / c * (1 + u x)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 / c * |u x| ^ P * (1 + u x) := by ring

/-- The reciprocal of an expansion whose function stays away from zero. -/
theorem HasExp.inv {g : α → ℝ} {b : ℕ → ℝ} (hg : HasExp S w g b) (hb0 : b 0 ≠ 0)
    {c : ℝ} (hc : 0 < c) (hlow : ∀ x ∈ S, c ≤ g x / b 0) :
    HasExp S w (fun x => 1 / g x) (cinv b) := by
  have hn : HasExp S w (fun x => 1 / b 0 * g x) (fun i => 1 / b 0 * b i) := hg.smul (1 / b 0)
  have hg1 : ∀ x ∈ S, w x = 0 → g x = b 0 := by
    obtain ⟨C, hC⟩ := hg 1
    intro x hx hw
    have h := hC x hx
    rw [sum_range_one, hw, abs_zero, pow_one, mul_zero, pow_zero, mul_one] at h
    have h' := abs_nonpos_iff.1 h
    linarith
  let y : α → ℝ := fun x => if w x = 0 then 1 / b 0 * b 1 else (g x / b 0 - 1) / w x
  have hy0 : ∀ x, w x = 0 → y x = 1 / b 0 * b 1 := fun x hw => by simp [y, hw]
  have hy1 : ∀ x, w x ≠ 0 → y x = (g x / b 0 - 1) / w x := fun x hw => by simp [y, hw]
  have h1u : ∀ x ∈ S, 1 + w x * y x = g x / b 0 := by
    intro x hx
    by_cases hw : w x = 0
    · rw [hw, zero_mul, add_zero, hg1 x hx hw, div_self hb0]
    · rw [hy1 x hw]
      field_simp
      ring
  have hyexp : HasExp S w y (fun i => 1 / b 0 * b (i + 1)) :=
    hn.shift 1 (g := y)
      (fun x hx => by
        show 1 / b 0 * g x = ∑ i ∈ range 1, 1 / b 0 * b i * w x ^ i + w x ^ 1 * y x
        rw [sum_range_one, pow_zero, pow_one, mul_one, one_div_mul_cancel hb0]
        have := h1u x hx
        rw [one_div_mul_eq_div]
        linarith)
      (fun x _ hw => hy0 x hw)
  have hgeo : HasExp S (fun x => w x * y x) (fun x => 1 / (1 + w x * y x))
      (fun i => (-1 : ℝ) ^ i) :=
    geo_hasExp_lower hc fun x hx => by
      rw [h1u x hx]
      exact hlow x hx
  have hcomp := hgeo.comp (w := w) (y := y) (fun x _ => rfl) hyexp
  refine ((hcomp.smul (1 / b 0)).congr fun x hx => ?_).congr_coeff fun i => rfl
  have hpos : 0 < g x / b 0 := lt_of_lt_of_le hc (hlow x hx)
  have hgx : g x ≠ 0 := fun h => by
    rw [h, zero_div] at hpos
    exact lt_irrefl _ hpos
  show 1 / g x = 1 / b 0 * (1 / (1 + w x * y x))
  rw [h1u x hx]
  field_simp

end

/-- A positive sequence with an expansion of constant term `1` in a gauge tending to zero is
bounded below by a positive constant. -/
theorem lower_of_hasExp {S₀ : ℕ} {w f : ℕ → ℝ} {b : ℕ → ℝ}
    (hf : HasExp {m : ℕ | S₀ ≤ m} w f b) (hb : b 0 = 1)
    (hpos : ∀ m, S₀ ≤ m → 0 < f m)
    (hsmall : ∀ ε > 0, ∃ M : ℕ, ∀ m, M ≤ m → |w m| ≤ ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ m ∈ {m : ℕ | S₀ ≤ m}, c ≤ f m / b 0 := by
  obtain ⟨C, hC⟩ := hf 1
  obtain ⟨M, hM⟩ := hsmall (1 / (2 * (|C| + 1))) (by positivity)
  have hfin : ∀ M : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ m, S₀ ≤ m → m < M → c ≤ f m := by
    intro M
    induction M with
    | zero => exact ⟨1, one_pos, fun m _ h => absurd h (Nat.not_lt_zero m)⟩
    | succ M ih =>
      obtain ⟨c, hc, h⟩ := ih
      by_cases hSM : S₀ ≤ M
      · refine ⟨min c (f M), lt_min hc (hpos M hSM), fun m hm hlt => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h' | h'
        · exact (min_le_left _ _).trans (h m hm h')
        · rw [h']
          exact min_le_right _ _
      · exact ⟨c, hc, fun m hm hlt => h m hm (by omega)⟩
  obtain ⟨c₀, hc₀, hlow⟩ := hfin M
  refine ⟨min c₀ (1 / 2), lt_min hc₀ (by norm_num), fun m hm => ?_⟩
  rw [hb, div_one]
  by_cases hmM : m < M
  · exact (min_le_left _ _).trans (hlow m hm hmM)
  · have h := hC m hm
    rw [sum_range_one, pow_zero, mul_one, pow_one, hb] at h
    have hw := hM m (not_lt.1 hmM)
    have hCw : C * |w m| ≤ 1 / 2 := by
      have h1 : C * |w m| ≤ |C| * (1 / (2 * (|C| + 1))) :=
        mul_le_mul (le_abs_self C) hw (abs_nonneg _) (abs_nonneg _)
      have h2 : |C| * (1 / (2 * (|C| + 1))) ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        linarith [abs_nonneg C]
      linarith
    have h3 := (abs_le.1 h).1
    exact (min_le_right _ _).trans (by linarith)

theorem gauge_even_small : ∀ ε > 0, ∃ M : ℕ, ∀ m, M ≤ m → |1 / ((2 * m + 1 : ℕ) : ℝ)| ≤ ε := by
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  refine ⟨M, fun m hm => ?_⟩
  have hpos : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hmM : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [abs_of_pos (by positivity), div_le_iff₀ hpos]
  rw [div_lt_iff₀ hε] at hM
  push_cast
  nlinarith

theorem gauge_odd_small : ∀ ε > 0, ∃ M : ℕ, ∀ m, M ≤ m → |1 / ((2 * m + 2 : ℕ) : ℝ)| ≤ ε := by
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  refine ⟨M, fun m hm => ?_⟩
  have hpos : (0 : ℝ) < ((2 * m + 2 : ℕ) : ℝ) := by positivity
  have hmM : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [abs_of_pos (by positivity), div_le_iff₀ hpos]
  rw [div_lt_iff₀ hε] at hM
  push_cast
  nlinarith

/-! ### Low-order values of the formal operations -/

section
variable {K : Type*} [CommRing K]

theorem cmul_zero' (a b : ℕ → K) : cmul a b 0 = a 0 * b 0 := by simp [cmul]

theorem cmul_one' (a b : ℕ → K) : cmul a b 1 = a 0 * b 1 + a 1 * b 0 := by
  simp [cmul, sum_range_succ]

theorem ccomp_zero' (a b : ℕ → K) : ccomp a b 0 = a 0 := by simp [ccomp, cpow]

theorem ccomp_one' (a b : ℕ → K) : ccomp a b 1 = a 1 * b 0 := by
  simp [ccomp, cpow, cmul, sum_range_succ]

end

theorem cinv_zero' {K : Type*} [Field K] (b : ℕ → K) : cinv b 0 = 1 / b 0 := by
  simp [cinv, ccomp_zero']

theorem cinv_one' {K : Type*} [Field K] (b : ℕ → K) : cinv b 1 = -(b 1 / (b 0 * b 0)) := by
  unfold cinv
  rw [ccomp_one']
  by_cases h : b 0 = 0
  · simp [h]
  · field_simp

theorem angR_zero' (a : ℝ) (d : ℕ → ℚ) (h0 : d 0 = 1) : angR a d 0 = 1 := by
  simp [angR, angQ, cpow, cmul, h0]

theorem angR_one' (a : ℝ) (d : ℕ → ℚ) (h0 : d 0 = 1) : angR a d 1 = (d 1 : ℝ) - a / 3 := by
  simp [angR, angQ, cpow, cmul, sum_range_succ, h0]
  ring

/-! ### Positivity of the deficits -/

theorem slope_pos_odd {j : ℕ} (hj : 1 ≤ j) : (0 : ℝ) < ((slopeQ (2 * j + 1) : ℚ) : ℝ) := by
  exact_mod_cast (slopeQ_classification (2 * j + 1) (by omega)).1

theorem slope_pos_even {m : ℕ} (hm : 2 ≤ m) : (0 : ℝ) < ((slopeQ (2 * m) : ℚ) : ℝ) := by
  exact_mod_cast (slopeQ_classification (2 * m) (by omega)).1

theorem deficit_odd_eq {j : ℕ} (hj : 1 ≤ j) :
    π - realApexAngle j = 2 * arctan ((slopeQ (2 * j + 1) : ℚ) : ℝ) := by
  rw [realApexAngle_eq, virtualApex_eq (2 * j + 1) (by omega)]
  ring

theorem deficit_even_eq {m : ℕ} (hm : 2 ≤ m) :
    π - virtualApexAngle m = 2 * arctan ((slopeQ (2 * m) : ℚ) : ℝ) := by
  rw [virtualApexAngle_eq' (by omega), virtualApex_eq (2 * m) (by omega)]
  ring

theorem deficit_odd_pos {j : ℕ} (hj : 1 ≤ j) : 0 < π - realApexAngle j := by
  rw [deficit_odd_eq hj]
  have := arctan_pos.2 (slope_pos_odd hj)
  linarith

theorem deficit_even_pos {m : ℕ} (hm : 2 ≤ m) : 0 < π - virtualApexAngle m := by
  rw [deficit_even_eq hm]
  have := arctan_pos.2 (slope_pos_even hm)
  linarith

/-! ### The exact ratio for even orders: a convergent series -/

/-- For even `n = 2m ≥ 4` and `N = n + 1`, `t_n / s_{n+1} = 2 N² / ((N+1)(N+3))`. -/
theorem slope_ratio_even_exact {m : ℕ} (hm : 2 ≤ m) :
    ((slopeQ (2 * m) : ℚ) : ℝ) / ((slopeQ (2 * m + 1) : ℚ) : ℝ) =
      2 * ((2 * m + 1 : ℕ) : ℝ) ^ 2 /
        ((((2 * m + 1 : ℕ) : ℝ) + 1) * (((2 * m + 1 : ℕ) : ℝ) + 3)) := by
  have hs := slope_pos_odd (j := m) (by omega)
  rw [slopeQ_even_cast hm, mul_div_assoc, div_self hs.ne', mul_one]

/-- The rational function `2 N² / ((N+1)(N+3))` as a convergent series in `1/N`, `N > 3`:
`2 + ∑_{i ≥ 0} (-1)^(i+1) (3^(i+2) - 1) / N^(i+1)`. -/
theorem slope_ratio_even_hasSum {N : ℝ} (hN : 3 < N) :
    HasSum (fun i : ℕ => (-1 : ℝ) ^ (i + 1) * (3 ^ (i + 2) - 1) / N ^ (i + 1))
      (2 * N ^ 2 / ((N + 1) * (N + 3)) - 2) := by
  have hN0 : 0 < N := by linarith
  have h1 : |(-1 / N)| < 1 := by
    rw [abs_div, abs_neg, abs_one, abs_of_pos hN0, div_lt_one hN0]
    linarith
  have h3 : |(-3 / N)| < 1 := by
    rw [abs_div, abs_neg, abs_of_pos hN0, div_lt_one hN0]
    simp only [Nat.abs_ofNat]
    exact hN
  have g1 := (hasSum_geometric_of_abs_lt_one h1).mul_left (1 / N)
  have g3 := (hasSum_geometric_of_abs_lt_one h3).mul_left (9 / N)
  have e1 : 1 / N * (1 - -1 / N)⁻¹ = 1 / (N + 1) := by
    have h : (1 - -1 / N) = (N + 1) / N := by
      field_simp
      ring
    rw [h, inv_div]
    field_simp
  have e3 : 9 / N * (1 - -3 / N)⁻¹ = 9 / (N + 3) := by
    have h : (1 - -3 / N) = (N + 3) / N := by
      field_simp
      ring
    rw [h, inv_div]
    field_simp
  rw [e1] at g1
  rw [e3] at g3
  have g := g1.sub g3
  have ev : 2 * N ^ 2 / ((N + 1) * (N + 3)) - 2 = 1 / (N + 1) - 9 / (N + 3) := by
    field_simp
    ring
  rw [ev]
  convert g using 1
  funext i
  rw [div_pow, div_pow, neg_pow, neg_pow 3, pow_succ (-1 : ℝ), pow_succ N]
  field_simp
  ring

/-! ### Asymptotic expansions of the other ratios -/

/-- Rational coefficients of `t_{n+1} / s_n`, `n` odd, in powers of `1 / (n + 1)`. -/
def slopeRatioOddQ : ℕ → ℚ := fun i =>
  2 * cmul (cmul (binQc 1) (ccomp eC (geoQ 1))) (cinv dC) i

/-- The coefficients are evaluated with `eDirect`, which equals `eC` at every order. -/
theorem slopeRatioOddQ_values :
    slopeRatioOddQ 0 = 2 ∧ slopeRatioOddQ 1 = -10 ∧ slopeRatioOddQ 2 = 60 ∧
    slopeRatioOddQ 3 = -1656 / 5 ∧ slopeRatioOddQ 4 = 43776 / 25 ∧
    slopeRatioOddQ 5 = -1569312 / 175 ∧ slopeRatioOddQ 6 = 39207744 / 875 := by
  unfold slopeRatioOddQ
  rw [← eDirect_eq_eC]
  decide +kernel

theorem ratio_identity_slope {t s σ r : ℝ} (hs : s ≠ 0) (hσ : σ ≠ 0) (hr : r ≠ 0) :
    t / s = 2 * (r * (t / (2 * (σ * r))) * (1 / (s / σ))) := by
  field_simp

theorem ratio_identity_even {X Y σ r : ℝ} (hY : Y ≠ 0) (hσ : σ ≠ 0) (hr : r ≠ 0) :
    X / Y = 2 * (X / (2 * (2 * σ)) * (1 / (r * (Y / (2 * (σ * r)))))) := by
  field_simp

theorem ratio_identity_odd {X Y σ r : ℝ} (hY : Y ≠ 0) (hσ : σ ≠ 0) (hr : r ≠ 0) :
    X / Y = 2 * (r * (X / (2 * (2 * (σ * r)))) * (1 / (Y / (2 * σ)))) := by
  field_simp

theorem bin1_fun {x : ℝ} (hx : 0 < x) :
    (1 + 1 * (1 / x)) ^ (-1 / 2 : ℝ) = √(x / (x + 1)) := by
  have e : 1 / (1 + 1 * (1 / x)) = x / (x + 1) := by field_simp
  rw [rpow_neg_half (by positivity), e]

/-- **Slope ratio, odd orders.**  For odd `n = 2j + 1 ≥ 3` and `x = n + 1`, the ratio
`t_{n+1} / s_n` has an asymptotic expansion in powers of `1/x` with the rational coefficients
`slopeRatioOddQ`. -/
theorem slope_ratio_odd_hasExp :
    HasExp {j : ℕ | 1 ≤ j} (fun j => 1 / ((2 * j + 2 : ℕ) : ℝ))
      (fun j => ((slopeQ (2 * (j + 1)) : ℚ) : ℝ) / ((slopeQ (2 * j + 1) : ℚ) : ℝ))
      (fun i => (slopeRatioOddQ i : ℝ)) := by
  have hw0 : ∀ j ∈ {j : ℕ | 1 ≤ j}, (0 : ℝ) ≤ 1 / ((2 * j + 2 : ℕ) : ℝ) :=
    fun j _ => by positivity
  have hS := odd_slope_hasExp
  have hT0 := even_slope_hasExp.comap (T := {j : ℕ | 1 ≤ j}) (fun j => j + 1)
    (fun j (hj : 1 ≤ j) => (show 2 ≤ j + 1 by omega))
  have hy1 : HasExp {j : ℕ | 1 ≤ j} (fun j => 1 / ((2 * j + 2 : ℕ) : ℝ))
      (fun j => 1 / (1 + 1 * (1 / ((2 * j + 2 : ℕ) : ℝ)))) (fun i => (-1 : ℝ) ^ i) :=
    geo_hasExp 1 zero_le_one hw0
  have hTw := hT0.comp (w := fun j => 1 / ((2 * j + 2 : ℕ) : ℝ))
    (y := fun j => 1 / (1 + 1 * (1 / ((2 * j + 2 : ℕ) : ℝ))))
    (fun j _ => by
      show 1 / ((2 * (j + 1) + 1 : ℕ) : ℝ) =
        1 / ((2 * j + 2 : ℕ) : ℝ) * (1 / (1 + 1 * (1 / ((2 * j + 2 : ℕ) : ℝ))))
      push_cast
      field_simp) hy1
  have hρ : HasExp {j : ℕ | 1 ≤ j} (fun j => 1 / ((2 * j + 2 : ℕ) : ℝ))
      (fun j => (1 + 1 * (1 / ((2 * j + 2 : ℕ) : ℝ))) ^ (-1 / 2 : ℝ))
      (fun i => (binQ i : ℝ) * 1 ^ i) :=
    bin_hasExp 1 zero_le_one fun j _ => by
      have h2 : (2 : ℝ) ≤ ((2 * j + 2 : ℕ) : ℝ) := by
        push_cast
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      constructor
      · positivity
      · rw [one_mul, div_le_iff₀ (by linarith)]
        linarith
  have hd0 : ((dC 0 : ℚ) : ℝ) = 1 := by rw [dC_values.1, Rat.cast_one]
  obtain ⟨c, hc, hlow⟩ := lower_of_hasExp (S₀ := 1) hS hd0
    (fun j hj => div_pos (slope_pos_odd hj) (sig_pos' (by positivity))) gauge_odd_small
  have hinv := hS.inv (by rw [hd0]; exact one_ne_zero) hc hlow
  have hprod := ((hρ.mul hTw).mul hinv).smul 2
  refine (hprod.congr fun j hj => ?_).congr_coeff fun i => ?_
  · have hj' : 1 ≤ j := hj
    have hx : (0 : ℝ) < ((2 * j + 2 : ℕ) : ℝ) := by positivity
    have hD : ((2 * (j + 1) + 1 : ℕ) : ℝ) = ((2 * j + 2 : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    show ((slopeQ (2 * (j + 1)) : ℚ) : ℝ) / ((slopeQ (2 * j + 1) : ℚ) : ℝ) =
      2 * ((1 + 1 * (1 / ((2 * j + 2 : ℕ) : ℝ))) ^ (-1 / 2 : ℝ) *
        (((slopeQ (2 * (j + 1)) : ℚ) : ℝ) / (2 * sig ((2 * (j + 1) + 1 : ℕ) : ℝ))) *
        (1 / (((slopeQ (2 * j + 1) : ℚ) : ℝ) / sig ((2 * j + 2 : ℕ) : ℝ))))
    rw [bin1_fun hx, hD, sig_succ hx]
    exact ratio_identity_slope (slope_pos_odd hj').ne' (sig_pos' hx).ne'
      (sqrt_pos.2 (by positivity)).ne'
  · have h1 : (fun i => ((cmul (binQc 1) (ccomp eC (geoQ 1)) i : ℚ) : ℝ)) =
        cmul (fun i => ((binQc 1 i : ℚ) : ℝ)) (fun i => ((ccomp eC (geoQ 1) i : ℚ) : ℝ)) :=
      funext fun i => map_cmul (Rat.castHom ℝ) _ _ i
    have h2 : (fun i => ((ccomp eC (geoQ 1) i : ℚ) : ℝ)) =
        ccomp (fun i => (eC i : ℝ)) (fun i => ((geoQ 1 i : ℚ) : ℝ)) :=
      funext fun i => map_ccomp (Rat.castHom ℝ) _ _ i
    have h3 : (fun i => ((cinv dC i : ℚ) : ℝ)) = cinv (fun i => (dC i : ℝ)) :=
      funext fun i => map_cinv (Rat.castHom ℝ) dC i
    have h4 : ((cmul (cmul (binQc 1) (ccomp eC (geoQ 1))) (cinv dC) i : ℚ) : ℝ) =
        cmul (fun i => ((cmul (binQc 1) (ccomp eC (geoQ 1)) i : ℚ) : ℝ))
          (fun i => ((cinv dC i : ℚ) : ℝ)) i := map_cmul (Rat.castHom ℝ) _ _ i
    show ((slopeRatioOddQ i : ℚ) : ℝ) = _
    unfold slopeRatioOddQ
    rw [Rat.cast_mul, h4, h1, h2, h3, geoQ_cast, binQc_cast]
    simp only [Rat.cast_ofNat, Rat.cast_one]

/-- Real coefficient sequences of the two angular-deficit expansions. -/
noncomputable def Ac : ℕ → ℝ := angR (216 / π) dC

/-- See `Ac`. -/
noncomputable def Bc : ℕ → ℝ := angR (864 / π) eC

/-- Coefficients of the deficit ratio for even `n`. -/
noncomputable def deficitRatioEvenC : ℕ → ℝ := fun i =>
  2 * cmul Bc (cinv (cmul (fun i => (binQ i : ℝ) * 1 ^ i) (ccomp Ac (fun i => (-1 : ℝ) ^ i)))) i

/-- Coefficients of the deficit ratio for odd `n`. -/
noncomputable def deficitRatioOddC : ℕ → ℝ := fun i =>
  2 * cmul (cmul (fun i => (binQ i : ℝ) * 1 ^ i) (ccomp Bc (fun i => (-1 : ℝ) ^ i))) (cinv Ac) i

theorem Ac_zero : Ac 0 = 1 := angR_zero' _ _ dC_values.1

theorem Bc_zero : Bc 0 = 1 := angR_zero' _ _ eC_values.1

theorem Ac_one : Ac 1 = -15 / 4 - 72 / π := by
  unfold Ac
  rw [angR_one' _ _ dC_values.1, dC_values.2.1]
  push_cast
  ring

theorem Bc_one : Bc 1 = -33 / 4 - 288 / π := by
  unfold Bc
  rw [angR_one' _ _ eC_values.1, eC_values.2.1]
  push_cast
  ring

/-- **Deficit ratio, even orders.**  For even `n = 2m ≥ 4` and `N = n + 1`, the ratio
`(π - α_n^virt) / (π - α_{n+1})` has an asymptotic expansion in powers of `1/N`. -/
theorem deficit_ratio_even_hasExp :
    HasExp {m : ℕ | 2 ≤ m} (fun m => 1 / ((2 * m + 1 : ℕ) : ℝ))
      (fun m => (π - virtualApexAngle m) / (π - realApexAngle m)) deficitRatioEvenC := by
  have hw0 : ∀ m ∈ {m : ℕ | 2 ≤ m}, (0 : ℝ) ≤ 1 / ((2 * m + 1 : ℕ) : ℝ) :=
    fun m _ => by positivity
  have hB := even_angle_hasExp
  have hA0 := odd_angle_hasExp.mono fun m (hmem : 2 ≤ m) => (show 1 ≤ m by omega)
  have hy1 : HasExp {m : ℕ | 2 ≤ m} (fun m => 1 / ((2 * m + 1 : ℕ) : ℝ))
      (fun m => 1 / (1 + 1 * (1 / ((2 * m + 1 : ℕ) : ℝ)))) (fun i => (-1 : ℝ) ^ i) :=
    geo_hasExp 1 zero_le_one hw0
  have hAw := hA0.comp (w := fun m => 1 / ((2 * m + 1 : ℕ) : ℝ))
    (y := fun m => 1 / (1 + 1 * (1 / ((2 * m + 1 : ℕ) : ℝ))))
    (fun m _ => by
      show 1 / ((2 * m + 2 : ℕ) : ℝ) =
        1 / ((2 * m + 1 : ℕ) : ℝ) * (1 / (1 + 1 * (1 / ((2 * m + 1 : ℕ) : ℝ))))
      push_cast
      field_simp
      ring) hy1
  have hρ : HasExp {m : ℕ | 2 ≤ m} (fun m => 1 / ((2 * m + 1 : ℕ) : ℝ))
      (fun m => (1 + 1 * (1 / ((2 * m + 1 : ℕ) : ℝ))) ^ (-1 / 2 : ℝ))
      (fun i => (binQ i : ℝ) * 1 ^ i) :=
    bin_hasExp 1 zero_le_one fun m hmem => by
      have h5 : (5 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 5 ≤ 2 * m + 1 by have : 2 ≤ m := hmem; omega)
      constructor
      · positivity
      · rw [one_mul, div_le_iff₀ (by linarith)]
        linarith
  have hden := hρ.mul hAw
  have hb0 : cmul (fun i => (binQ i : ℝ) * 1 ^ i)
      (ccomp (angR (216 / π) dC) (fun i => (-1 : ℝ) ^ i)) 0 = 1 := by
    rw [cmul_zero', ccomp_zero', angR_zero' _ _ dC_values.1]
    simp [binQ]
  obtain ⟨c, hc, hlow⟩ := lower_of_hasExp (S₀ := 2) hden hb0
    (fun m hmem => mul_pos (rpow_pos_of_pos (by positivity) _)
      (div_pos (deficit_odd_pos (by omega)) (by
        have := sig_pos' (x := ((2 * m + 2 : ℕ) : ℝ)) (by positivity)
        positivity))) gauge_even_small
  have hinv := hden.inv (by rw [hb0]; exact one_ne_zero) hc hlow
  have hprod := (hB.mul hinv).smul 2
  refine (hprod.congr fun m hmem => ?_).congr_coeff fun i => rfl
  have hm' : 2 ≤ m := hmem
  have hN0 : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hD : ((2 * m + 2 : ℕ) : ℝ) = ((2 * m + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  show (π - virtualApexAngle m) / (π - realApexAngle m) =
    2 * ((π - virtualApexAngle m) / (2 * (2 * sig ((2 * m + 1 : ℕ) : ℝ))) *
      (1 / ((1 + 1 * (1 / ((2 * m + 1 : ℕ) : ℝ))) ^ (-1 / 2 : ℝ) *
        ((π - realApexAngle m) / (2 * sig ((2 * m + 2 : ℕ) : ℝ))))))
  rw [bin1_fun hN0, hD, sig_succ hN0]
  exact ratio_identity_even (deficit_odd_pos (by omega)).ne' (sig_pos' hN0).ne'
    (sqrt_pos.2 (by positivity)).ne'

/-- **Deficit ratio, odd orders.**  For odd `n = 2j + 1 ≥ 3` and `x = n + 1`, the ratio
`(π - α_{n+1}^virt) / (π - α_n)` has an asymptotic expansion in powers of `1/x`. -/
theorem deficit_ratio_odd_hasExp :
    HasExp {j : ℕ | 1 ≤ j} (fun j => 1 / ((2 * j + 2 : ℕ) : ℝ))
      (fun j => (π - virtualApexAngle (j + 1)) / (π - realApexAngle j)) deficitRatioOddC := by
  have hw0 : ∀ j ∈ {j : ℕ | 1 ≤ j}, (0 : ℝ) ≤ 1 / ((2 * j + 2 : ℕ) : ℝ) :=
    fun j _ => by positivity
  have hA := odd_angle_hasExp
  have hB0 := even_angle_hasExp.comap (T := {j : ℕ | 1 ≤ j}) (fun j => j + 1)
    (fun j (hj : 1 ≤ j) => (show 2 ≤ j + 1 by omega))
  have hy1 : HasExp {j : ℕ | 1 ≤ j} (fun j => 1 / ((2 * j + 2 : ℕ) : ℝ))
      (fun j => 1 / (1 + 1 * (1 / ((2 * j + 2 : ℕ) : ℝ)))) (fun i => (-1 : ℝ) ^ i) :=
    geo_hasExp 1 zero_le_one hw0
  have hBw := hB0.comp (w := fun j => 1 / ((2 * j + 2 : ℕ) : ℝ))
    (y := fun j => 1 / (1 + 1 * (1 / ((2 * j + 2 : ℕ) : ℝ))))
    (fun j _ => by
      show 1 / ((2 * (j + 1) + 1 : ℕ) : ℝ) =
        1 / ((2 * j + 2 : ℕ) : ℝ) * (1 / (1 + 1 * (1 / ((2 * j + 2 : ℕ) : ℝ))))
      push_cast
      field_simp) hy1
  have hρ : HasExp {j : ℕ | 1 ≤ j} (fun j => 1 / ((2 * j + 2 : ℕ) : ℝ))
      (fun j => (1 + 1 * (1 / ((2 * j + 2 : ℕ) : ℝ))) ^ (-1 / 2 : ℝ))
      (fun i => (binQ i : ℝ) * 1 ^ i) :=
    bin_hasExp 1 zero_le_one fun j _ => by
      have h2 : (2 : ℝ) ≤ ((2 * j + 2 : ℕ) : ℝ) := by
        push_cast
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      constructor
      · positivity
      · rw [one_mul, div_le_iff₀ (by linarith)]
        linarith
  obtain ⟨c, hc, hlow⟩ := lower_of_hasExp (S₀ := 1) hA (angR_zero' _ _ dC_values.1)
    (fun j hj => div_pos (deficit_odd_pos hj) (by
      have := sig_pos' (x := ((2 * j + 2 : ℕ) : ℝ)) (by positivity)
      positivity)) gauge_odd_small
  have hinv := hA.inv (by rw [angR_zero' _ _ dC_values.1]; exact one_ne_zero) hc hlow
  have hprod := ((hρ.mul hBw).mul hinv).smul 2
  refine (hprod.congr fun j hj => ?_).congr_coeff fun i => rfl
  have hj' : 1 ≤ j := hj
  have hx : (0 : ℝ) < ((2 * j + 2 : ℕ) : ℝ) := by positivity
  have hD : ((2 * (j + 1) + 1 : ℕ) : ℝ) = ((2 * j + 2 : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  show (π - virtualApexAngle (j + 1)) / (π - realApexAngle j) =
    2 * ((1 + 1 * (1 / ((2 * j + 2 : ℕ) : ℝ))) ^ (-1 / 2 : ℝ) *
      ((π - virtualApexAngle (j + 1)) / (2 * (2 * sig ((2 * (j + 1) + 1 : ℕ) : ℝ)))) *
      (1 / ((π - realApexAngle j) / (2 * sig ((2 * j + 2 : ℕ) : ℝ)))))
  rw [bin1_fun hx, hD, sig_succ hx]
  exact ratio_identity_odd (deficit_odd_pos hj').ne' (sig_pos' hx).ne'
    (sqrt_pos.2 (by positivity)).ne'

/-! ### The first two coefficients of the deficit ratios, with `π` symbolic -/

theorem bin1_values : ((binQ 0 : ℚ) : ℝ) * 1 ^ 0 = 1 ∧ ((binQ 1 : ℚ) : ℝ) * 1 ^ 1 = -1 / 2 := by
  constructor <;> simp [binQ]

theorem deficitRatioEvenC_zero : deficitRatioEvenC 0 = 2 := by
  unfold deficitRatioEvenC
  rw [cmul_zero', cinv_zero', cmul_zero', ccomp_zero', Ac_zero, Bc_zero, bin1_values.1]
  norm_num

theorem deficitRatioEvenC_one : deficitRatioEvenC 1 = -(8 + 432 / π) := by
  unfold deficitRatioEvenC
  rw [cmul_one', cinv_zero', cinv_one', cmul_zero', cmul_one', ccomp_zero', ccomp_one', Ac_zero,
    Bc_zero, Ac_one, Bc_one, bin1_values.1, bin1_values.2]
  ring

theorem deficitRatioOddC_zero : deficitRatioOddC 0 = 2 := by
  unfold deficitRatioOddC
  rw [cmul_zero', cinv_zero', cmul_zero', ccomp_zero', Ac_zero, Bc_zero, bin1_values.1]
  norm_num

theorem deficitRatioOddC_one : deficitRatioOddC 1 = -(10 + 432 / π) := by
  unfold deficitRatioOddC
  rw [cmul_one', cinv_zero', cinv_one', cmul_zero', cmul_one', ccomp_zero', ccomp_one', Ac_zero,
    Bc_zero, Ac_one, Bc_one, bin1_values.1, bin1_values.2]
  ring

end PrivateApex
