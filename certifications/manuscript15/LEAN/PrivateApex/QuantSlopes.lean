import PrivateApex.QuantLaplace
import PrivateApex.ConsecutiveRatios

/-!
PRIVATE.  Manuscript 15: the central-slope expansions with explicit remainders.

For the orders `p ≤ 7` and `x = n + 1`,

* `odd_slope_explicit`: for odd `n = 2j + 1 ≥ 3`,
  `|s_n - √(216/(π x)) ∑ i < p, dC i / x^i| ≤ √(216/(π x)) (oddK p / x^p + lapT p e^(-x/12))`;
* `even_slope_explicit`: for even `n = 2m ≥ 4`,
  `|t_n - √(864/(π x)) ∑ i < p, eC i / x^i| ≤ √(864/(π x)) (evenK p / x^p + lapT p e^(-x/12))`;
* `explicit_constants`: rational upper bounds of `oddK p`, `evenK p`, `lapT p`, `p ≤ 7`,
  evaluated by the kernel (`oddKtab`, `evenKtab`, `lapTtab`);
* `odd_slope_remainder`, `even_slope_remainder`: the same bounds with the tabulated constants;
* `odd_slope_remainder_power`, `even_slope_remainder_power`: bounds `K / x^p` for every `n`;
* `odd_slope_remainder_large`, `even_slope_remainder_large`: for `x ≥ 1000` the exponentially
  small term is at most `1 / x^p`.

The remainder is split into the remainder of the Laplace expansion (`laplace_explicit`) and the
remainder of an elementary function (`odd_elementary`, `even_elementary`), whose constants are
computed by the calculus of `QuantCalculus`.  These bounds are rigorous but not optimal; no
statement about optimal constants is made here.
-/

namespace PrivateApex
open Real Finset MeasureTheory

/-! ### Elementary expansions with explicit constants -/

section Elementary
variable {α : Type*} {S : Set α} {w : α → ℝ}

/-- `1 / (1 + c w)`, with remainder constants `c ^ P`. -/
theorem geo_hasExpQ (c : ℚ) (hc : 0 ≤ c) (hw : ∀ x ∈ S, 0 ≤ w x) (n : ℕ) :
    HasExpQ S w n (fun x => 1 / (1 + (c : ℝ) * w x)) (geoQ c) (fun P => c ^ P) := by
  intro P _ x hx
  have hc' : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hcw : 0 ≤ (c : ℝ) * w x := mul_nonneg hc' (hw x hx)
  have hpos : 0 < 1 + (c : ℝ) * w x := by linarith
  have e : 1 / (1 + (c : ℝ) * w x) - ∑ i ∈ range P, ((geoQ c i : ℚ) : ℝ) * w x ^ i =
      (-(c : ℝ) * w x) ^ P / (1 + (c : ℝ) * w x) := by
    have hgeo : ∑ i ∈ range P, ((geoQ c i : ℚ) : ℝ) * w x ^ i =
        ∑ i ∈ range P, (-(c : ℝ) * w x) ^ i :=
      sum_congr rfl fun i _ => by
        rw [show ((geoQ c i : ℚ) : ℝ) = (-(c : ℝ)) ^ i by simp [geoQ], ← mul_pow]
    have hq := geom_sum_mul (-(c : ℝ) * w x) P
    rw [hgeo, eq_div_iff hpos.ne', sub_mul, one_div_mul_cancel hpos.ne']
    linear_combination hq
  rw [e, abs_div, abs_of_pos hpos, abs_pow, abs_mul, abs_neg, abs_of_nonneg hc', mul_pow]
  push_cast
  exact div_le_self (by positivity) (by linarith)

/-- Constants of a polynomial of degree `< m` in a gauge bounded by `W`. -/
def polyK (a : ℕ → ℚ) (W : ℚ) (m : ℕ) (P : ℕ) : ℚ :=
  |(0 : ℚ)| * W ^ (m - P) + ∑ i ∈ range (m - P), |a (P + i)| * W ^ i

theorem poly_hasExpQ {W : ℚ} (hW : ∀ x ∈ S, |w x| ≤ (W : ℝ)) (a : ℕ → ℚ) (m : ℕ) :
    HasExpQ S w m (fun x => ∑ i ∈ range m, (a i : ℝ) * w x ^ i) a (polyK a W m) :=
  HasExpQ.of_top hW (D := 0) fun x _ => by simp

/-- Coefficients of `1 + c z`. -/
def onePlus (c : ℚ) (i : ℕ) : ℚ := if i = 0 then 1 else if i = 1 then c else 0

/-- The binomial coefficients of `(1 + c z)^(-1/2)`, truncated at the order `m`. -/
def binT (c : ℚ) (m : ℕ) (i : ℕ) : ℚ := if i < m then binQc c i else 0

/-- Constant of `|1 - (1 + c w) T(w)^2| ≤ binD |w|^m`, `T` the truncated binomial series. -/
def binD (c W : ℚ) (m : ℕ) : ℚ :=
  mulC (onePlus c) (polyK (onePlus c) W m)
    (mulC (binT c m) (polyK (binT c m) W m) (polyK (binT c m) W m)) m

/-- Constants of the expansion of `(1 + c w)^(-1/2)` up to the order `m`. -/
def binK (c W : ℚ) (m : ℕ) (P : ℕ) : ℚ :=
  |binD c W m| * W ^ (m - P) + ∑ i ∈ range (m - P), |binQc c (P + i)| * W ^ i

/-- `(1 + c w)^(-1/2)` with explicit constants.  The two numerical hypotheses are checked by
the kernel in the applications: the truncated series `T` satisfies `(1 + c z) T^2 = 1 + O(z^m)`
as polynomials, and `T ≥ 0` on the range of the gauge. -/
theorem bin_hasExpQ (c W : ℚ) (hc : 0 ≤ c) (m : ℕ) (hm : 2 ≤ m)
    (hw : ∀ x ∈ S, 0 ≤ w x ∧ w x ≤ (W : ℝ))
    (hcoef : ∀ i ∈ range m,
      cmul (onePlus c) (cmul (binT c m) (binT c m)) i = if i = 0 then 1 else 0)
    (hT : polyK (binT c m) W m 1 * W ≤ 1) :
    HasExpQ S w m (fun x => (1 + (c : ℝ) * w x) ^ (-1 / 2 : ℝ)) (binQc c) (binK c W m) := by
  have hW : ∀ x ∈ S, |w x| ≤ (W : ℝ) := fun x hx => by
    rw [abs_of_nonneg (hw x hx).1]
    exact (hw x hx).2
  have hc' : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hTexp : HasExpQ S w m (fun x => ∑ i ∈ range m, (binT c m i : ℝ) * w x ^ i) (binT c m)
      (polyK (binT c m) W m) := poly_hasExpQ hW (binT c m) m
  have h1exp : HasExpQ S w m (fun x => 1 + (c : ℝ) * w x) (onePlus c)
      (polyK (onePlus c) W m) := by
    refine (poly_hasExpQ hW (onePlus c) m).congr fun x _ => ?_
    obtain ⟨m', rfl⟩ : ∃ m', m = 2 + m' := ⟨m - 2, by omega⟩
    rw [sum_range_add, sum_range_succ, sum_range_one]
    have hz : ∑ i ∈ range m', ((onePlus c (2 + i) : ℚ) : ℝ) * w x ^ (2 + i) = 0 :=
      sum_eq_zero fun i _ => by
        have h1 : onePlus c (2 + i) = 0 := by
          unfold onePlus
          split_ifs <;> first | omega | rfl
        rw [h1]
        simp
    rw [hz]
    simp [onePlus]
  have hE := h1exp.mul (hTexp.mul hTexp)
  have hEtop : ∀ x ∈ S,
      |(1 + (c : ℝ) * w x) * ((∑ i ∈ range m, (binT c m i : ℝ) * w x ^ i) *
        (∑ i ∈ range m, (binT c m i : ℝ) * w x ^ i)) - 1| ≤ (binD c W m : ℝ) * |w x| ^ m := by
    intro x hx
    have h := hE m le_rfl x hx
    have hs : ∑ i ∈ range m,
        ((cmul (onePlus c) (cmul (binT c m) (binT c m)) i : ℚ) : ℝ) * w x ^ i = 1 := by
      have h' : ∀ i ∈ range m,
          ((cmul (onePlus c) (cmul (binT c m) (binT c m)) i : ℚ) : ℝ) * w x ^ i =
            (if i = 0 then (1 : ℝ) else 0) * w x ^ i := fun i hi => by
        rw [hcoef i hi]
        split_ifs <;> simp
      rw [sum_congr rfl h']
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [sum_range_succ']
      simp
    rw [hs] at h
    exact h
  have htop : ∀ x ∈ S, |(1 + (c : ℝ) * w x) ^ (-1 / 2 : ℝ) -
      ∑ i ∈ range m, (binQc c i : ℝ) * w x ^ i| ≤ (binD c W m : ℝ) * |w x| ^ m := by
    intro x hx
    obtain ⟨h0, h1⟩ := hw x hx
    have e : ∑ i ∈ range m, (binQc c i : ℝ) * w x ^ i =
        ∑ i ∈ range m, (binT c m i : ℝ) * w x ^ i :=
      sum_congr rfl fun i hi => by simp [binT, mem_range.1 hi]
    rw [e]
    set T : ℝ := ∑ i ∈ range m, (binT c m i : ℝ) * w x ^ i with hTdef
    have hcw : 0 ≤ (c : ℝ) * w x := mul_nonneg hc' h0
    have hpos : 0 < 1 + (c : ℝ) * w x := by linarith
    set q : ℝ := (1 + (c : ℝ) * w x) ^ (-1 / 2 : ℝ) with hqdef
    have hq0 : 0 < q := rpow_pos_of_pos hpos _
    have hqq : q * q * (1 + (c : ℝ) * w x) = 1 := by
      rw [hqdef, rpow_neg_half hpos, ← sq, sq_sqrt (by positivity)]
      field_simp
    -- `T ≥ 0`
    have hT0 : 0 ≤ T := by
      have h := hTexp 1 (by omega) x hx
      have hb0 : ((binT c m 0 : ℚ) : ℝ) = 1 := by
        have hb : binT c m 0 = binQc c 0 := by
          unfold binT
          split_ifs with h
          · rfl
          · omega
        have : binT c m 0 = 1 := by
          rw [hb]
          simp [binQc, binQ]
        rw [this]
        norm_num
      simp only [sum_range_one, pow_zero, mul_one, hb0, pow_one] at h
      have hK : (0 : ℝ) ≤ (polyK (binT c m) W m 1 : ℝ) := by
        have hW0 : (0 : ℚ) ≤ W := by
          have : (0 : ℝ) ≤ (W : ℝ) := h0.trans h1
          exact_mod_cast this
        have : (0 : ℚ) ≤ polyK (binT c m) W m 1 := by
          unfold polyK
          positivity
        exact_mod_cast this
      have h2 : (polyK (binT c m) W m 1 : ℝ) * |w x| ≤ 1 :=
        (mul_le_mul_of_nonneg_left (hW x hx) hK).trans (by exact_mod_cast hT)
      linarith [(abs_le.mp h).1]
    have hfac : (q - T) * ((q + T) * (1 + (c : ℝ) * w x)) =
        -((1 + (c : ℝ) * w x) * (T * T) - 1) := by
      linear_combination hqq
    have hqle : q ≤ 1 := by
      by_contra hgt
      rw [not_le] at hgt
      have : 1 < q * q * (1 + (c : ℝ) * w x) := by nlinarith
      linarith
    have hden : 1 ≤ (q + T) * (1 + (c : ℝ) * w x) := by
      have h1' : 1 ≤ q * (1 + (c : ℝ) * w x) := by
        by_contra hlt
        rw [not_le] at hlt
        have : q * (q * (1 + (c : ℝ) * w x)) < 1 := by nlinarith
        linarith [hqq]
      nlinarith [mul_nonneg hT0 hpos.le]
    have habs : |q - T| ≤ |(1 + (c : ℝ) * w x) * (T * T) - 1| := by
      have h := congrArg abs hfac
      rw [abs_mul, abs_neg] at h
      rw [← h]
      have hd : 1 ≤ |(q + T) * (1 + (c : ℝ) * w x)| := hden.trans (le_abs_self _)
      nlinarith [abs_nonneg (q - T)]
    exact habs.trans (hEtop x hx)
  exact HasExpQ.of_top hW htop

end Elementary

/-! ### Numerical checks for the two binomial expansions -/

theorem bin_check_two : ∀ i ∈ range 9,
    cmul (onePlus 2) (cmul (binT 2 9) (binT 2 9)) i = if i = 0 then 1 else 0 := by
  decide +kernel

theorem bin_T_two : polyK (binT 2 9) (1 / 4) 9 1 * (1 / 4) ≤ 1 := by decide +kernel

theorem bin_check_one : ∀ i ∈ range 9,
    cmul (onePlus 1) (cmul (binT 1 9) (binT 1 9)) i = if i = 0 then 1 else 0 := by
  decide +kernel

theorem bin_T_one : polyK (binT 1 9) (1 / 5) 9 1 * (1 / 5) ≤ 1 := by decide +kernel

/-- The Laplace coefficients `c_0, …, c_6`. -/
def cTab : ℕ → ℚ := fun i =>
  ([1, -3 / 4, 29 / 160, 351 / 3200, 17877 / 358400, -465741 / 5120000,
    -110563031 / 401408000] : List ℚ).getD i 0

theorem cC_eq_cTab : ∀ i ∈ range 7, cC i = cTab i := by decide +kernel

/-! ### Odd orders -/

/-- Constant of the elementary part, odd orders. -/
def oddG (p : ℕ) : ℚ :=
  mulC (ccomp cTab (geoQ 2)) (compC cTab (geoQ 2) (polyK cTab 1 p) (fun P => 2 ^ P))
    (mulC (geoQ 2) (fun P => 2 ^ P) (binK 2 (1 / 4) 9)) p

theorem odd_coeff_check : ∀ i ∈ range 7,
    cmul (ccomp cTab (geoQ 2)) (cmul (geoQ 2) (binQc 2)) i = dTab i := by decide +kernel

/-- The elementary part of the odd-order remainder: the truncated Laplace series, transported
from the variable `1 / (N + 2)` to `1 / N` and multiplied by `(1 + 2/N)^(-3/2)`. -/
theorem odd_elementary {p : ℕ} (hp : p ≤ 7) {N : ℕ} (hN : 4 ≤ N) :
    |(∑ j ∈ range p, (cTab j : ℝ) * (1 / ((N : ℝ) + 2)) ^ j) *
        (1 / (1 + 2 * (1 / (N : ℝ))) * (1 + 2 * (1 / (N : ℝ))) ^ (-1 / 2 : ℝ)) -
        ∑ i ∈ range p, (dC i : ℝ) * (1 / (N : ℝ)) ^ i| ≤ (oddG p : ℝ) * |1 / (N : ℝ)| ^ p := by
  have hw0 : ∀ N ∈ {N : ℕ | 4 ≤ N}, (0 : ℝ) ≤ 1 / (N : ℝ) := fun N _ => by positivity
  have hwW : ∀ N ∈ {N : ℕ | 4 ≤ N}, (0 : ℝ) ≤ 1 / (N : ℝ) ∧ 1 / (N : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := by
    intro N hN
    have h4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 4 ≤ N from hN)
    refine ⟨by positivity, ?_⟩
    push_cast
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h2 : ((2 : ℚ) : ℝ) = 2 := by norm_num
  have hy : HasExpQ {N : ℕ | 4 ≤ N} (fun N => 1 / (N : ℝ)) 9
      (fun N => 1 / (1 + 2 * (1 / (N : ℝ)))) (geoQ 2) (fun P => 2 ^ P) := by
    have h := geo_hasExpQ (S := {N : ℕ | 4 ≤ N}) (w := fun N => 1 / (N : ℝ)) 2 (by norm_num) hw0 9
    rw [h2] at h
    exact h
  have hρ : HasExpQ {N : ℕ | 4 ≤ N} (fun N => 1 / (N : ℝ)) 9
      (fun N => (1 + 2 * (1 / (N : ℝ))) ^ (-1 / 2 : ℝ)) (binQc 2) (binK 2 (1 / 4) 9) := by
    have h := bin_hasExpQ (S := {N : ℕ | 4 ≤ N}) (w := fun N => 1 / (N : ℝ)) 2 (1 / 4)
      (by norm_num) 9 (by norm_num) hwW bin_check_two bin_T_two
    rw [h2] at h
    exact h
  have hv1 : ∀ N ∈ {N : ℕ | 4 ≤ N}, |1 / ((N : ℝ) + 2)| ≤ ((1 : ℚ) : ℝ) := by
    intro N _
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
    push_cast
    linarith
  have hQ := poly_hasExpQ (S := {N : ℕ | 4 ≤ N}) (w := fun N => 1 / ((N : ℝ) + 2)) hv1 cTab p
  have hQw := hQ.comp (w := fun N : ℕ => 1 / (N : ℝ))
    (y := fun N : ℕ => 1 / (1 + 2 * (1 / (N : ℝ))))
    (fun N hN => by
      have h4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 4 ≤ N from hN)
      have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
      show 1 / ((N : ℝ) + 2) = 1 / (N : ℝ) * (1 / (1 + 2 * (1 / (N : ℝ))))
      field_simp) (hy.mono_order (by omega))
  have hfull := hQw.mul ((hy.mul hρ).mono_order (by omega : p ≤ 9))
  have h := hfull p le_rfl N hN
  have e : ∑ i ∈ range p,
      ((cmul (ccomp cTab (geoQ 2)) (cmul (geoQ 2) (binQc 2)) i : ℚ) : ℝ) * (1 / (N : ℝ)) ^ i =
      ∑ i ∈ range p, (dC i : ℝ) * (1 / (N : ℝ)) ^ i :=
    sum_congr rfl fun i hi => by
      have hi' := mem_range.1 hi
      rw [odd_coeff_check i (mem_range.2 (by omega)), ← dC_eq_dTab i (mem_range.2 (by omega))]
  rw [e] at h
  exact h

/-- Algebraic constant of the odd-order remainder. -/
def oddK (p : ℕ) : ℚ := lapA p + oddG p

theorem lap_nonneg : ∀ p ∈ range 8, 0 ≤ lapA p ∧ 0 ≤ lapT p := by decide +kernel

/-- **Odd central slopes with explicit remainder**, orders `p ≤ 7`: for `n = 2j + 1 ≥ 3` and
`x = n + 1`. -/
theorem odd_slope_explicit {p : ℕ} (hp : p ≤ 7) {j : ℕ} (hj : 1 ≤ j) :
    |((slopeQ (2 * j + 1) : ℚ) : ℝ) - √(216 / (π * ((2 * j + 2 : ℕ) : ℝ))) *
        ∑ i ∈ range p, (dC i : ℝ) / ((2 * j + 2 : ℕ) : ℝ) ^ i| ≤
      √(216 / (π * ((2 * j + 2 : ℕ) : ℝ))) *
        ((oddK p : ℝ) / ((2 * j + 2 : ℕ) : ℝ) ^ p +
          (lapT p : ℝ) * exp (-(((2 * j + 2 : ℕ) : ℝ) / 12))) := by
  have hN4 : 4 ≤ 2 * j + 2 := by omega
  generalize hNdef : 2 * j + 2 = N at hN4 ⊢
  have hN : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hM1 : (1 : ℝ) ≤ (N : ℝ) + 2 := by linarith
  have hM0 : (0 : ℝ) < (N : ℝ) + 2 := by linarith
  have hhm : 0 < hm ((N : ℝ) + 2) 1 := lt_of_lt_of_le (by positivity) (hm_one_lower hM1)
  have hsig : 0 < sig (N : ℝ) := sig_pos' hN0
  obtain ⟨hA0, hT0⟩ := lap_nonneg p (mem_range.2 (by omega))
  have hA0' : (0 : ℝ) ≤ (lapA p : ℝ) := by exact_mod_cast hA0
  have hT0' : (0 : ℝ) ≤ (lapT p : ℝ) := by exact_mod_cast hT0
  -- the Laplace remainder
  have hL := laplace_explicit (p := p) (by omega) (N := N) (by omega)
  have hsI : ((slopeQ (2 * j + 1) : ℚ) : ℝ) =
      4 * (N : ℝ) / π * ∫ x in Set.Ioi (0 : ℝ), weight N x := by
    rw [slopeQ_odd_eq_integral hj, hNdef]
  generalize (∫ x in Set.Ioi (0 : ℝ), weight N x) = I at hL hsI
  set Q : ℝ := ∑ j ∈ range p, (cC j : ℝ) / ((N : ℝ) + 2) ^ j with hQdef
  have hF : |I / hm ((N : ℝ) + 2) 1 - Q| ≤
      (lapA p : ℝ) / ((N : ℝ) + 2) ^ p + exp (-(((N : ℝ) + 2) / 12)) * (lapT p : ℝ) := by
    have e : I / hm ((N : ℝ) + 2) 1 - Q =
        (I - hm ((N : ℝ) + 2) 1 * Q) / hm ((N : ℝ) + 2) 1 := by field_simp
    rw [e, abs_div, abs_of_pos hhm, div_le_iff₀ hhm]
    calc _ ≤ _ := hL
      _ = _ := by ring
  -- the factor `Y = (N/(N+2))^(3/2)`
  have hy1 : 1 / (1 + 2 * (1 / (N : ℝ))) = (N : ℝ) / ((N : ℝ) + 2) := by field_simp
  have hρ1 : (1 + 2 * (1 / (N : ℝ))) ^ (-1 / 2 : ℝ) = √((N : ℝ) / ((N : ℝ) + 2)) := by
    rw [rpow_neg_half (by positivity), hy1]
  have hfrac0 : 0 ≤ (N : ℝ) / ((N : ℝ) + 2) := by positivity
  have hfrac1 : (N : ℝ) / ((N : ℝ) + 2) ≤ 1 := by
    rw [div_le_one hM0]
    linarith
  have hsq1 : √((N : ℝ) / ((N : ℝ) + 2)) ≤ 1 := by
    rw [show (1 : ℝ) = √1 from sqrt_one.symm]
    exact sqrt_le_sqrt hfrac1
  set Y : ℝ := (N : ℝ) / ((N : ℝ) + 2) * √((N : ℝ) / ((N : ℝ) + 2)) with hYdef
  have hY0 : 0 ≤ Y := mul_nonneg hfrac0 (sqrt_nonneg _)
  have hY1 : Y ≤ 1 := by
    calc Y ≤ 1 * 1 := mul_le_mul hfrac1 hsq1 (sqrt_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hs : ((slopeQ (2 * j + 1) : ℚ) : ℝ) = sig (N : ℝ) * (Y * (I / hm ((N : ℝ) + 2) 1)) := by
    have hfour := four_D_hm hN0
    have e : 4 * (N : ℝ) / π * I =
        (4 * (N : ℝ) / π * hm ((N : ℝ) + 2) 1) * (I / hm ((N : ℝ) + 2) 1) := by field_simp
    rw [hsI, e, hfour, hYdef]
    ring
  -- the elementary remainder
  have hE := odd_elementary hp hN4
  have hQ' : ∑ j ∈ range p, (cTab j : ℝ) * (1 / ((N : ℝ) + 2)) ^ j = Q := by
    rw [hQdef]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    rw [cC_eq_cTab i (mem_range.2 (by omega)), one_div, inv_pow, div_eq_mul_inv]
  rw [hQ', hy1, hρ1, ← hYdef] at hE
  have hz : |1 / (N : ℝ)| ^ p = 1 / (N : ℝ) ^ p := by
    rw [abs_of_pos (by positivity), one_div, inv_pow, one_div]
  rw [hz] at hE
  have hd : ∑ i ∈ range p, (dC i : ℝ) * (1 / (N : ℝ)) ^ i =
      ∑ i ∈ range p, (dC i : ℝ) / (N : ℝ) ^ i :=
    sum_congr rfl fun i _ => by rw [one_div, inv_pow, div_eq_mul_inv]
  rw [hd] at hE
  set Dsum : ℝ := ∑ i ∈ range p, (dC i : ℝ) / (N : ℝ) ^ i with hDdef
  -- assembly
  have hsig216 : √(216 / (π * (N : ℝ))) = sig (N : ℝ) := rfl
  rw [hsig216]
  have key : ((slopeQ (2 * j + 1) : ℚ) : ℝ) - sig (N : ℝ) * Dsum =
      sig (N : ℝ) * (Y * (I / hm ((N : ℝ) + 2) 1 - Q) + (Q * Y - Dsum)) := by
    rw [hs]
    ring
  rw [key, abs_mul, abs_of_pos hsig]
  refine mul_le_mul_of_nonneg_left ?_ hsig.le
  have h1 : |Y * (I / hm ((N : ℝ) + 2) 1 - Q)| ≤
      (lapA p : ℝ) / ((N : ℝ) + 2) ^ p + exp (-(((N : ℝ) + 2) / 12)) * (lapT p : ℝ) := by
    rw [abs_mul, abs_of_nonneg hY0]
    calc Y * |I / hm ((N : ℝ) + 2) 1 - Q| ≤ 1 * |I / hm ((N : ℝ) + 2) 1 - Q| :=
          mul_le_mul_of_nonneg_right hY1 (abs_nonneg _)
      _ = |I / hm ((N : ℝ) + 2) 1 - Q| := one_mul _
      _ ≤ _ := hF
  have h2 : (lapA p : ℝ) / ((N : ℝ) + 2) ^ p ≤ (lapA p : ℝ) / (N : ℝ) ^ p :=
    div_le_div_of_nonneg_left hA0' (by positivity)
      (pow_le_pow_left₀ hN0.le (by linarith) p)
  have h3 : exp (-(((N : ℝ) + 2) / 12)) ≤ exp (-((N : ℝ) / 12)) :=
    exp_le_exp.mpr (by linarith)
  have h4 : exp (-(((N : ℝ) + 2) / 12)) * (lapT p : ℝ) ≤
      (lapT p : ℝ) * exp (-((N : ℝ) / 12)) := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left h3 hT0'
  have hK : ((oddK p : ℚ) : ℝ) = (lapA p : ℝ) + (oddG p : ℝ) := by simp [oddK]
  calc |Y * (I / hm ((N : ℝ) + 2) 1 - Q) + (Q * Y - Dsum)|
      ≤ |Y * (I / hm ((N : ℝ) + 2) 1 - Q)| + |Q * Y - Dsum| := abs_add_le _ _
    _ ≤ ((lapA p : ℝ) / (N : ℝ) ^ p + (lapT p : ℝ) * exp (-((N : ℝ) / 12))) +
          (oddG p : ℝ) * (1 / (N : ℝ) ^ p) := add_le_add (h1.trans (add_le_add h2 h4)) hE
    _ = (oddK p : ℝ) / (N : ℝ) ^ p + (lapT p : ℝ) * exp (-((N : ℝ) / 12)) := by
        rw [hK]
        ring

/-! ### Even orders -/

/-- Constant of the elementary part, even orders. -/
def evenH (p : ℕ) : ℚ :=
  mulC (ccomp dTab (geoQ 1)) (compC dTab (geoQ 1) (polyK dTab 1 p) (fun P => 1 ^ P))
    (mulC (cmul (geoQ 1) (geoQ 3)) (mulC (geoQ 1) (fun P => 1 ^ P) (fun P => 3 ^ P))
      (binK 1 (1 / 5) 9)) p

theorem even_coeff_check : ∀ i ∈ range 7,
    cmul (ccomp dTab (geoQ 1)) (cmul (cmul (geoQ 1) (geoQ 3)) (binQc 1)) i = eTab i := by
  decide +kernel

/-- The elementary part of the even-order remainder. -/
theorem even_elementary {p : ℕ} (hp : p ≤ 7) {N : ℕ} (hN : 5 ≤ N) :
    |(∑ i ∈ range p, (dTab i : ℝ) * (1 / ((N : ℝ) + 1)) ^ i) *
        (1 / (1 + 1 * (1 / (N : ℝ))) * (1 / (1 + 3 * (1 / (N : ℝ)))) *
          (1 + 1 * (1 / (N : ℝ))) ^ (-1 / 2 : ℝ)) -
        ∑ i ∈ range p, (eC i : ℝ) * (1 / (N : ℝ)) ^ i| ≤ (evenH p : ℝ) * |1 / (N : ℝ)| ^ p := by
  have hw0 : ∀ N ∈ {N : ℕ | 5 ≤ N}, (0 : ℝ) ≤ 1 / (N : ℝ) := fun N _ => by positivity
  have hwW : ∀ N ∈ {N : ℕ | 5 ≤ N}, (0 : ℝ) ≤ 1 / (N : ℝ) ∧ 1 / (N : ℝ) ≤ ((1 / 5 : ℚ) : ℝ) := by
    intro N hN
    have h5 : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 5 ≤ N from hN)
    refine ⟨by positivity, ?_⟩
    push_cast
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h1c : ((1 : ℚ) : ℝ) = 1 := by norm_num
  have h3c : ((3 : ℚ) : ℝ) = 3 := by norm_num
  have hy1 : HasExpQ {N : ℕ | 5 ≤ N} (fun N => 1 / (N : ℝ)) 9
      (fun N => 1 / (1 + 1 * (1 / (N : ℝ)))) (geoQ 1) (fun P => 1 ^ P) := by
    have h := geo_hasExpQ (S := {N : ℕ | 5 ≤ N}) (w := fun N => 1 / (N : ℝ)) 1 (by norm_num) hw0 9
    rw [h1c] at h
    exact h
  have hy3 : HasExpQ {N : ℕ | 5 ≤ N} (fun N => 1 / (N : ℝ)) 9
      (fun N => 1 / (1 + 3 * (1 / (N : ℝ)))) (geoQ 3) (fun P => 3 ^ P) := by
    have h := geo_hasExpQ (S := {N : ℕ | 5 ≤ N}) (w := fun N => 1 / (N : ℝ)) 3 (by norm_num) hw0 9
    rw [h3c] at h
    exact h
  have hρ : HasExpQ {N : ℕ | 5 ≤ N} (fun N => 1 / (N : ℝ)) 9
      (fun N => (1 + 1 * (1 / (N : ℝ))) ^ (-1 / 2 : ℝ)) (binQc 1) (binK 1 (1 / 5) 9) := by
    have h := bin_hasExpQ (S := {N : ℕ | 5 ≤ N}) (w := fun N => 1 / (N : ℝ)) 1 (1 / 5)
      (by norm_num) 9 (by norm_num) hwW bin_check_one bin_T_one
    rw [h1c] at h
    exact h
  have hv1 : ∀ N ∈ {N : ℕ | 5 ≤ N}, |1 / ((N : ℝ) + 1)| ≤ ((1 : ℚ) : ℝ) := by
    intro N _
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
    push_cast
    linarith
  have hD := poly_hasExpQ (S := {N : ℕ | 5 ≤ N}) (w := fun N => 1 / ((N : ℝ) + 1)) hv1 dTab p
  have hDw := hD.comp (w := fun N : ℕ => 1 / (N : ℝ))
    (y := fun N : ℕ => 1 / (1 + 1 * (1 / (N : ℝ))))
    (fun N hN => by
      have h5 : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 5 ≤ N from hN)
      have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
      show 1 / ((N : ℝ) + 1) = 1 / (N : ℝ) * (1 / (1 + 1 * (1 / (N : ℝ))))
      field_simp) (hy1.mono_order (by omega))
  have hfull := hDw.mul (((hy1.mul hy3).mul hρ).mono_order (by omega : p ≤ 9))
  have h := hfull p le_rfl N hN
  have e : ∑ i ∈ range p,
      ((cmul (ccomp dTab (geoQ 1)) (cmul (cmul (geoQ 1) (geoQ 3)) (binQc 1)) i : ℚ) : ℝ) *
        (1 / (N : ℝ)) ^ i = ∑ i ∈ range p, (eC i : ℝ) * (1 / (N : ℝ)) ^ i :=
    sum_congr rfl fun i hi => by
      have hi' := mem_range.1 hi
      rw [even_coeff_check i (mem_range.2 (by omega)), ← eC_eq_eTab i (mem_range.2 (by omega))]
  rw [e] at h
  exact h

/-- Algebraic constant of the even-order remainder. -/
def evenK (p : ℕ) : ℚ := oddK p + evenH p

theorem oddK_nonneg : ∀ p ∈ range 8, 0 ≤ oddK p := by decide +kernel

/-- **Even central slopes with explicit remainder**, orders `p ≤ 7`: for `n = 2m ≥ 4` and
`x = n + 1`. -/
theorem even_slope_explicit {p : ℕ} (hp : p ≤ 7) {m : ℕ} (hm : 2 ≤ m) :
    |((slopeQ (2 * m) : ℚ) : ℝ) - √(864 / (π * ((2 * m + 1 : ℕ) : ℝ))) *
        ∑ i ∈ range p, (eC i : ℝ) / ((2 * m + 1 : ℕ) : ℝ) ^ i| ≤
      √(864 / (π * ((2 * m + 1 : ℕ) : ℝ))) *
        ((evenK p : ℝ) / ((2 * m + 1 : ℕ) : ℝ) ^ p +
          (lapT p : ℝ) * exp (-(((2 * m + 1 : ℕ) : ℝ) / 12))) := by
  have hodd := odd_slope_explicit hp (j := m) (by omega)
  have hN5 : 5 ≤ 2 * m + 1 := by omega
  have hsucc : ((2 * m + 2 : ℕ) : ℝ) = ((2 * m + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  have hcast := slopeQ_even_cast hm
  rw [hsucc] at hodd
  generalize hNdef : 2 * m + 1 = N at hN5 hodd hcast ⊢
  have hN : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN5
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hsig : 0 < sig (N : ℝ) := sig_pos' hN0
  obtain ⟨_, hT0⟩ := lap_nonneg p (mem_range.2 (by omega))
  have hT0' : (0 : ℝ) ≤ (lapT p : ℝ) := by exact_mod_cast hT0
  have hK0 : (0 : ℝ) ≤ (oddK p : ℝ) := by
    exact_mod_cast oddK_nonneg p (mem_range.2 (by omega))
  set r : ℝ := √((N : ℝ) / ((N : ℝ) + 1)) with hrdef
  have hr0 : 0 < r := sqrt_pos.2 (by positivity)
  have hr1 : r ≤ 1 := by
    have hfr : (N : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    calc r = √((N : ℝ) / ((N : ℝ) + 1)) := hrdef
      _ ≤ √1 := sqrt_le_sqrt hfr
      _ = 1 := sqrt_one
  have hsig' : √(216 / (π * ((N : ℝ) + 1))) = sig (N : ℝ) * r := sig_succ hN0
  rw [hsig'] at hodd
  generalize ((slopeQ N : ℚ) : ℝ) = s at hodd hcast
  -- the odd-order remainder, divided by `σ r`
  set D' : ℝ := ∑ i ∈ range p, (dC i : ℝ) / ((N : ℝ) + 1) ^ i with hD'def
  have hσr : 0 < sig (N : ℝ) * r := mul_pos hsig hr0
  have hR : |s / (sig (N : ℝ) * r) - D'| ≤
      (oddK p : ℝ) / ((N : ℝ) + 1) ^ p + (lapT p : ℝ) * exp (-(((N : ℝ) + 1) / 12)) := by
    have e : s / (sig (N : ℝ) * r) - D' = (s - sig (N : ℝ) * r * D') / (sig (N : ℝ) * r) := by
      field_simp
    rw [e, abs_div, abs_of_pos hσr, div_le_iff₀ hσr]
    calc _ ≤ _ := hodd
      _ = _ := by ring
  -- the factor `G`
  have hy1e : 1 / (1 + 1 * (1 / (N : ℝ))) = (N : ℝ) / ((N : ℝ) + 1) := by field_simp
  have hy3e : 1 / (1 + 3 * (1 / (N : ℝ))) = (N : ℝ) / ((N : ℝ) + 3) := by field_simp
  have hρe : (1 + 1 * (1 / (N : ℝ))) ^ (-1 / 2 : ℝ) = r := by
    rw [rpow_neg_half (by positivity), hy1e]
  set G : ℝ := (N : ℝ) / ((N : ℝ) + 1) * ((N : ℝ) / ((N : ℝ) + 3)) * r with hGdef
  have hG0 : 0 ≤ G := by positivity
  have hG1 : G ≤ 1 := by
    have ha : (N : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have hb : (N : ℝ) / ((N : ℝ) + 3) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have ha0 : 0 ≤ (N : ℝ) / ((N : ℝ) + 1) := by positivity
    have hb0 : 0 ≤ (N : ℝ) / ((N : ℝ) + 3) := by positivity
    calc G ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul ha hb hb0 zero_le_one) hr1 hr0.le (by norm_num)
      _ = 1 := by norm_num
  have ht : ((slopeQ (2 * m) : ℚ) : ℝ) = 2 * sig (N : ℝ) * (G * (s / (sig (N : ℝ) * r))) := by
    rw [hcast, hGdef]
    field_simp
  -- the elementary remainder
  have hE := even_elementary hp hN5
  have hD'' : ∑ i ∈ range p, (dTab i : ℝ) * (1 / ((N : ℝ) + 1)) ^ i = D' := by
    rw [hD'def]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    rw [dC_eq_dTab i (mem_range.2 (by omega)), one_div, inv_pow, div_eq_mul_inv]
  rw [hD'', hy1e, hy3e, hρe, ← hGdef] at hE
  have hz : |1 / (N : ℝ)| ^ p = 1 / (N : ℝ) ^ p := by
    rw [abs_of_pos (by positivity), one_div, inv_pow, one_div]
  rw [hz] at hE
  have he : ∑ i ∈ range p, (eC i : ℝ) * (1 / (N : ℝ)) ^ i =
      ∑ i ∈ range p, (eC i : ℝ) / (N : ℝ) ^ i :=
    sum_congr rfl fun i _ => by rw [one_div, inv_pow, div_eq_mul_inv]
  rw [he] at hE
  set Esum : ℝ := ∑ i ∈ range p, (eC i : ℝ) / (N : ℝ) ^ i with hEdef
  rw [sqrt_864]
  have key : ((slopeQ (2 * m) : ℚ) : ℝ) - 2 * sig (N : ℝ) * Esum =
      2 * sig (N : ℝ) * (G * (s / (sig (N : ℝ) * r) - D') + (D' * G - Esum)) := by
    rw [ht]
    ring
  have h2σ : 0 < 2 * sig (N : ℝ) := by positivity
  rw [key, abs_mul, abs_of_pos h2σ]
  refine mul_le_mul_of_nonneg_left ?_ h2σ.le
  have h1 : |G * (s / (sig (N : ℝ) * r) - D')| ≤
      (oddK p : ℝ) / ((N : ℝ) + 1) ^ p + (lapT p : ℝ) * exp (-(((N : ℝ) + 1) / 12)) := by
    rw [abs_mul, abs_of_nonneg hG0]
    calc G * |s / (sig (N : ℝ) * r) - D'| ≤ 1 * |s / (sig (N : ℝ) * r) - D'| :=
          mul_le_mul_of_nonneg_right hG1 (abs_nonneg _)
      _ = |s / (sig (N : ℝ) * r) - D'| := one_mul _
      _ ≤ _ := hR
  have h2 : (oddK p : ℝ) / ((N : ℝ) + 1) ^ p ≤ (oddK p : ℝ) / (N : ℝ) ^ p :=
    div_le_div_of_nonneg_left hK0 (by positivity)
      (pow_le_pow_left₀ hN0.le (by linarith) p)
  have h3 : (lapT p : ℝ) * exp (-(((N : ℝ) + 1) / 12)) ≤
      (lapT p : ℝ) * exp (-((N : ℝ) / 12)) :=
    mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) hT0'
  have hK : ((evenK p : ℚ) : ℝ) = (oddK p : ℝ) + (evenH p : ℝ) := by simp [evenK]
  calc |G * (s / (sig (N : ℝ) * r) - D') + (D' * G - Esum)|
      ≤ |G * (s / (sig (N : ℝ) * r) - D')| + |D' * G - Esum| := abs_add_le _ _
    _ ≤ ((oddK p : ℝ) / (N : ℝ) ^ p + (lapT p : ℝ) * exp (-((N : ℝ) / 12))) +
          (evenH p : ℝ) * (1 / (N : ℝ) ^ p) := add_le_add (h1.trans (add_le_add h2 h3)) hE
    _ = (evenK p : ℝ) / (N : ℝ) ^ p + (lapT p : ℝ) * exp (-((N : ℝ) / 12)) := by
        rw [hK]
        ring

/-! ### Numerical values of the constants -/

/-- Upper bounds of `oddK p`, `p = 0, …, 7`. -/
def oddKtab : ℕ → ℚ := fun p =>
  ([1, 664 / 125, 983 / 50, 1221 / 20, 2039 / 10, 4416 / 5, 6033, 71350] : List ℚ).getD p 0

/-- Upper bounds of `evenK p`, `p = 0, …, 7`. -/
def evenKtab : ℕ → ℚ := fun p =>
  ([1, 519 / 50, 3009 / 50, 2873 / 10, 1284, 5593, 25430, 148000] : List ℚ).getD p 0

/-- Upper bounds of `lapT p`, `p = 0, …, 7`. -/
def lapTtab : ℕ → ℚ := fun p =>
  ([54, 58, 70, 888 / 5, 1662, 29180, 669100, 18570000] : List ℚ).getD p 0

theorem explicit_constants : ∀ p ∈ range 8,
    oddK p ≤ oddKtab p ∧ evenK p ≤ evenKtab p ∧ lapT p ≤ lapTtab p ∧ 0 ≤ lapT p := by
  decide +kernel

/-- Odd orders, with the tabulated constants. -/
theorem odd_slope_remainder {p : ℕ} (hp : p ≤ 7) {j : ℕ} (hj : 1 ≤ j) :
    |((slopeQ (2 * j + 1) : ℚ) : ℝ) - √(216 / (π * ((2 * j + 2 : ℕ) : ℝ))) *
        ∑ i ∈ range p, (dC i : ℝ) / ((2 * j + 2 : ℕ) : ℝ) ^ i| ≤
      √(216 / (π * ((2 * j + 2 : ℕ) : ℝ))) *
        ((oddKtab p : ℝ) / ((2 * j + 2 : ℕ) : ℝ) ^ p +
          (lapTtab p : ℝ) * exp (-(((2 * j + 2 : ℕ) : ℝ) / 12))) := by
  obtain ⟨h1, _, h3, _⟩ := explicit_constants p (mem_range.2 (by omega))
  refine (odd_slope_explicit hp hj).trans (mul_le_mul_of_nonneg_left ?_ (sqrt_nonneg _))
  have hx : (0 : ℝ) < ((2 * j + 2 : ℕ) : ℝ) := by positivity
  exact add_le_add
    (div_le_div_of_nonneg_right (by exact_mod_cast h1) (by positivity))
    (mul_le_mul_of_nonneg_right (by exact_mod_cast h3) (exp_pos _).le)

/-- Even orders, with the tabulated constants. -/
theorem even_slope_remainder {p : ℕ} (hp : p ≤ 7) {m : ℕ} (hm : 2 ≤ m) :
    |((slopeQ (2 * m) : ℚ) : ℝ) - √(864 / (π * ((2 * m + 1 : ℕ) : ℝ))) *
        ∑ i ∈ range p, (eC i : ℝ) / ((2 * m + 1 : ℕ) : ℝ) ^ i| ≤
      √(864 / (π * ((2 * m + 1 : ℕ) : ℝ))) *
        ((evenKtab p : ℝ) / ((2 * m + 1 : ℕ) : ℝ) ^ p +
          (lapTtab p : ℝ) * exp (-(((2 * m + 1 : ℕ) : ℝ) / 12))) := by
  obtain ⟨_, h2, h3, _⟩ := explicit_constants p (mem_range.2 (by omega))
  refine (even_slope_explicit hp hm).trans (mul_le_mul_of_nonneg_left ?_ (sqrt_nonneg _))
  have hx : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  exact add_le_add
    (div_le_div_of_nonneg_right (by exact_mod_cast h2) (by positivity))
    (mul_le_mul_of_nonneg_right (by exact_mod_cast h3) (exp_pos _).le)

/-! ### Pure power bounds -/

/-- For `x ≥ 1`, `K / x^p + L e^(-x/12) ≤ (K + L p! 12^p) / x^p`. -/
theorem two_term_le_power {K L x : ℝ} (hL : 0 ≤ L) (hx : 1 ≤ x) (p : ℕ) :
    K / x ^ p + L * exp (-(x / 12)) ≤ (K + L * ((p.factorial : ℝ) * 12 ^ p)) / x ^ p := by
  have h := exp_small p hx
  have hx0 : 0 < x ^ p := pow_pos (by linarith) p
  rw [add_div]
  refine add_le_add le_rfl ?_
  calc L * exp (-(x / 12)) ≤ L * ((p.factorial : ℝ) * 12 ^ p / x ^ p) :=
        mul_le_mul_of_nonneg_left h hL
    _ = L * ((p.factorial : ℝ) * 12 ^ p) / x ^ p := by ring

/-- For `x ≥ 1000`, `L e^(-x/12) ≤ 1 / x^p` as soon as `L (p+40)! 12^(p+40) ≤ 1000^40`. -/
theorem exp_term_small {L x : ℝ} (hL : 0 ≤ L) (hx : 1000 ≤ x) (p : ℕ)
    (hnum : L * (((p + 40).factorial : ℝ) * 12 ^ (p + 40)) ≤ 1000 ^ 40) :
    L * exp (-(x / 12)) ≤ 1 / x ^ p := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have h := exp_small (p + 40) hx1
  have h40 : (1000 : ℝ) ^ 40 ≤ x ^ 40 := pow_le_pow_left₀ (by norm_num) hx 40
  have hxp : 0 < x ^ p := pow_pos hx0 p
  have hx40 : 0 < x ^ 40 := pow_pos hx0 40
  calc L * exp (-(x / 12))
      ≤ L * (((p + 40).factorial : ℝ) * 12 ^ (p + 40) / x ^ (p + 40)) :=
        mul_le_mul_of_nonneg_left h hL
    _ = L * (((p + 40).factorial : ℝ) * 12 ^ (p + 40)) / x ^ 40 / x ^ p := by
        rw [show x ^ (p + 40) = x ^ p * x ^ 40 from pow_add x p 40]
        field_simp
    _ ≤ 1 / x ^ p := by
        apply div_le_div_of_nonneg_right _ hxp.le
        rw [div_le_one hx40]
        exact hnum.trans h40

theorem lapT_threshold : ∀ p ∈ range 8,
    lapTtab p * (((p + 40).factorial : ℚ) * 12 ^ (p + 40)) ≤ 1000 ^ 40 ∧ 0 ≤ lapTtab p := by
  decide +kernel

/-- Odd orders: a bound `K / x^p` valid for every odd `n ≥ 3`. -/
theorem odd_slope_remainder_power {p : ℕ} (hp : p ≤ 7) {j : ℕ} (hj : 1 ≤ j) :
    |((slopeQ (2 * j + 1) : ℚ) : ℝ) - √(216 / (π * ((2 * j + 2 : ℕ) : ℝ))) *
        ∑ i ∈ range p, (dC i : ℝ) / ((2 * j + 2 : ℕ) : ℝ) ^ i| ≤
      √(216 / (π * ((2 * j + 2 : ℕ) : ℝ))) *
        (((oddKtab p : ℝ) + (lapTtab p : ℝ) * ((p.factorial : ℝ) * 12 ^ p)) /
          ((2 * j + 2 : ℕ) : ℝ) ^ p) := by
  obtain ⟨_, hL0⟩ := lapT_threshold p (mem_range.2 (by omega))
  have hx : (1 : ℝ) ≤ ((2 * j + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * j + 2 by omega)
  exact (odd_slope_remainder hp hj).trans (mul_le_mul_of_nonneg_left
    (two_term_le_power (by exact_mod_cast hL0) hx p) (sqrt_nonneg _))

/-- Even orders: a bound `K / x^p` valid for every even `n ≥ 4`. -/
theorem even_slope_remainder_power {p : ℕ} (hp : p ≤ 7) {m : ℕ} (hm : 2 ≤ m) :
    |((slopeQ (2 * m) : ℚ) : ℝ) - √(864 / (π * ((2 * m + 1 : ℕ) : ℝ))) *
        ∑ i ∈ range p, (eC i : ℝ) / ((2 * m + 1 : ℕ) : ℝ) ^ i| ≤
      √(864 / (π * ((2 * m + 1 : ℕ) : ℝ))) *
        (((evenKtab p : ℝ) + (lapTtab p : ℝ) * ((p.factorial : ℝ) * 12 ^ p)) /
          ((2 * m + 1 : ℕ) : ℝ) ^ p) := by
  obtain ⟨_, hL0⟩ := lapT_threshold p (mem_range.2 (by omega))
  have hx : (1 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * m + 1 by omega)
  exact (even_slope_remainder hp hm).trans (mul_le_mul_of_nonneg_left
    (two_term_le_power (by exact_mod_cast hL0) hx p) (sqrt_nonneg _))

/-- Odd orders, `x = n + 1 ≥ 1000`: the exponentially small term is at most `1 / x^p`. -/
theorem odd_slope_remainder_large {p : ℕ} (hp : p ≤ 7) {j : ℕ} (hj : 499 ≤ j) :
    |((slopeQ (2 * j + 1) : ℚ) : ℝ) - √(216 / (π * ((2 * j + 2 : ℕ) : ℝ))) *
        ∑ i ∈ range p, (dC i : ℝ) / ((2 * j + 2 : ℕ) : ℝ) ^ i| ≤
      √(216 / (π * ((2 * j + 2 : ℕ) : ℝ))) *
        (((oddKtab p : ℝ) + 1) / ((2 * j + 2 : ℕ) : ℝ) ^ p) := by
  obtain ⟨hnum, hL0⟩ := lapT_threshold p (mem_range.2 (by omega))
  have hx : (1000 : ℝ) ≤ ((2 * j + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 1000 ≤ 2 * j + 2 by omega)
  have hsmall := exp_term_small (L := (lapTtab p : ℝ)) (by exact_mod_cast hL0) hx p
    (by exact_mod_cast hnum)
  refine (odd_slope_remainder hp (by omega)).trans
    (mul_le_mul_of_nonneg_left ?_ (sqrt_nonneg _))
  rw [add_div]
  exact add_le_add le_rfl hsmall

/-- Even orders, `x = n + 1 ≥ 1000`: the exponentially small term is at most `1 / x^p`. -/
theorem even_slope_remainder_large {p : ℕ} (hp : p ≤ 7) {m : ℕ} (hm : 500 ≤ m) :
    |((slopeQ (2 * m) : ℚ) : ℝ) - √(864 / (π * ((2 * m + 1 : ℕ) : ℝ))) *
        ∑ i ∈ range p, (eC i : ℝ) / ((2 * m + 1 : ℕ) : ℝ) ^ i| ≤
      √(864 / (π * ((2 * m + 1 : ℕ) : ℝ))) *
        (((evenKtab p : ℝ) + 1) / ((2 * m + 1 : ℕ) : ℝ) ^ p) := by
  obtain ⟨hnum, hL0⟩ := lapT_threshold p (mem_range.2 (by omega))
  have hx : (1000 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1000 ≤ 2 * m + 1 by omega)
  have hsmall := exp_term_small (L := (lapTtab p : ℝ)) (by exact_mod_cast hL0) hx p
    (by exact_mod_cast hnum)
  refine (even_slope_remainder hp (by omega)).trans
    (mul_le_mul_of_nonneg_left ?_ (sqrt_nonneg _))
  rw [add_div]
  exact add_le_add le_rfl hsmall

end PrivateApex
