import PrivateApex.ExpansionCalculus
import PrivateApex.SincExpBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Exponential

/-!
PRIVATE.  The series of `-log (sin u / u)` to every order.

On `0 ≤ u ≤ 1` and in the gauge `u ^ 2`:

* `sinc_hasExp`   : `sin u / u` has the coefficients `sincC k = (-1)^k / (2k+1)!`;
* `Lsinc_hasExp`  : `-log (sin u / u)` has the rational coefficients `logC`, the formal
  logarithm of the sine series, computed by the substitution `ccomp`;
* `kap_hasExp`    : `kap u = (-log (sin u / u) - u^2/6) / u^4` has the coefficients
  `kapC i = logC (i + 2)`.

The values `logC k = ζ(2k) / (k π^(2k))` for `k ≤ 8` are checked by kernel evaluation in
`logC_table`; they are not used in the proofs.
-/

namespace PrivateApex
open Real Finset

/-- Coefficients of `sin u / u` in powers of `u ^ 2`. -/
def sincC (k : ℕ) : ℚ := (-1) ^ k / (2 * k + 1).factorial

/-- Coefficients of `(1 - sin u / u) / u ^ 2`. -/
def yC (k : ℕ) : ℚ := -sincC (k + 1)

/-- Coefficients of `-log (1 - x)`. -/
def hC (i : ℕ) : ℚ := if i = 0 then 0 else 1 / i

/-- Coefficients of `-log (sin u / u)` in powers of `u ^ 2`. -/
def logC : ℕ → ℚ := ccomp hC yC

/-- Coefficients of `(-log (sin u / u) - u ^ 2 / 6) / u ^ 4` in powers of `u ^ 2`. -/
def kapC (i : ℕ) : ℚ := logC (i + 2)

theorem logC_values : logC 0 = 0 ∧ logC 1 = 1 / 6 ∧ logC 2 = 1 / 180 := by decide +kernel

/-- The first eight coefficients agree with `ζ(2k) / (k π^(2k))`. -/
theorem logC_table : logC 3 = 1 / 2835 ∧ logC 4 = 1 / 37800 ∧ logC 5 = 1 / 467775 ∧
    logC 6 = 691 / 3831077250 ∧ logC 7 = 2 / 127702575 ∧
    logC 8 = 3617 / 2605132530000 := by decide +kernel

/-! ### The sine series with remainder -/

theorem I_pow_two_mul (P : ℕ) : Complex.I ^ (2 * P) = (-1) ^ P := by
  rw [pow_mul, Complex.I_sq]

theorem sin_partial_im (u : ℝ) (P : ℕ) :
    (∑ m ∈ range (2 * P + 1), ((u : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).im =
      ∑ k ∈ range P, (-1) ^ k * u ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
  induction P with
  | zero => simp
  | succ P ih =>
    have e : 2 * (P + 1) + 1 = 2 * P + 1 + 1 + 1 := by ring
    have h1 : (((u : ℂ) * Complex.I) ^ (2 * P + 1) / ((2 * P + 1).factorial : ℂ)).im =
        (-1) ^ P * u ^ (2 * P + 1) / ((2 * P + 1).factorial : ℝ) := by
      have h : ((u : ℂ) * Complex.I) ^ (2 * P + 1) / ((2 * P + 1).factorial : ℂ) =
          (((-1) ^ P * u ^ (2 * P + 1) / ((2 * P + 1).factorial : ℝ) : ℝ) : ℂ) * Complex.I := by
        rw [mul_pow, pow_succ Complex.I, I_pow_two_mul]
        push_cast
        ring
      rw [h, Complex.im_ofReal_mul, Complex.I_im, mul_one]
    have h2 : (((u : ℂ) * Complex.I) ^ (2 * P + 1 + 1) /
        ((2 * P + 1 + 1).factorial : ℂ)).im = 0 := by
      have e2 : 2 * P + 1 + 1 = 2 * (P + 1) := by ring
      have h : ((u : ℂ) * Complex.I) ^ (2 * P + 1 + 1) / ((2 * P + 1 + 1).factorial : ℂ) =
          (((-1) ^ (P + 1) * u ^ (2 * P + 1 + 1) /
            ((2 * P + 1 + 1).factorial : ℝ) : ℝ) : ℂ) := by
        rw [mul_pow, e2, I_pow_two_mul]
        push_cast
        ring
      rw [h, Complex.ofReal_im]
    rw [e, sum_range_succ, sum_range_succ, Complex.add_im, Complex.add_im, ih, sum_range_succ,
      h1, h2, add_zero]

theorem sin_taylor (P : ℕ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    |sin u - ∑ k ∈ range P, (-1) ^ k * u ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)| ≤
      2 * u ^ (2 * P + 1) := by
  have hn : ‖(u : ℂ) * Complex.I‖ = u := by simp [abs_of_nonneg h0]
  have hb := Complex.exp_bound (x := (u : ℂ) * Complex.I) (by rw [hn]; exact h1)
    (n := 2 * P + 1) (by omega)
  have him := Complex.abs_im_le_norm (Complex.exp ((u : ℂ) * Complex.I) -
    ∑ m ∈ range (2 * P + 1), ((u : ℂ) * Complex.I) ^ m / (m.factorial : ℂ))
  rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im, sin_partial_im] at him
  refine him.trans (hb.trans ?_)
  rw [hn, mul_comm (2 : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h0 _)
  have hf : (1 : ℝ) ≤ ((2 * P + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hP : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg P
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  push_cast
  nlinarith [mul_nonneg (sub_nonneg.2 hf) (by positivity : (0 : ℝ) ≤ 2 * (P : ℝ) + 1)]

/-! ### `sin u / u` -/

theorem sinc_hasExp :
    HasExp (Set.Icc (0 : ℝ) 1) (fun u => u ^ 2) sinc (fun k => (sincC k : ℝ)) := by
  intro P
  refine ⟨2, fun u hu => ?_⟩
  obtain ⟨h0, h1⟩ := hu
  show |sinc u - ∑ i ∈ range P, (sincC i : ℝ) * (u ^ 2) ^ i| ≤ 2 * |u ^ 2| ^ P
  rcases eq_or_lt_of_le h0 with rfl | hpos
  · rcases P with _ | P
    · simp
    · have hs : ∑ i ∈ range (P + 1), (sincC i : ℝ) * ((0 : ℝ) ^ 2) ^ i = 1 := by
        rw [sum_range_succ']
        simp [sincC]
      rw [hs]
      simp
  · have ht := sin_taylor P h0 h1
    have e : sinc u - ∑ i ∈ range P, (sincC i : ℝ) * (u ^ 2) ^ i =
        (sin u - ∑ k ∈ range P, (-1) ^ k * u ^ (2 * k + 1) /
          ((2 * k + 1).factorial : ℝ)) / u := by
      rw [sinc_of_ne_zero hpos.ne', sub_div, sum_div]
      congr 1
      refine sum_congr rfl fun k _ => ?_
      simp only [sincC]
      push_cast
      field_simp
      ring
    rw [e, abs_div, abs_of_pos hpos, div_le_iff₀ hpos,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ 2)]
    calc _ ≤ 2 * u ^ (2 * P + 1) := ht
      _ = _ := by ring

/-- `(1 - sin u / u) / u ^ 2`, continued by `1 / 6` at the origin. -/
noncomputable def ysinc (u : ℝ) : ℝ := if u = 0 then 1 / 6 else (1 - sinc u) / u ^ 2

theorem one_sub_sinc (u : ℝ) : 1 - sinc u = u ^ 2 * ysinc u := by
  unfold ysinc
  split_ifs with h
  · simp [h]
  · field_simp

theorem ysinc_hasExp :
    HasExp (Set.Icc (0 : ℝ) 1) (fun u => u ^ 2) ysinc (fun k => (yC k : ℝ)) := by
  have e0 : sincC 0 = 1 := by decide +kernel
  have e1 : sincC 1 = -1 / 6 := by decide +kernel
  have h := sinc_hasExp.shift 1 (g := fun u => -ysinc u)
    (fun u _ => by
      show sinc u = ∑ i ∈ range 1, (sincC i : ℝ) * (u ^ 2) ^ i + (u ^ 2) ^ 1 * -ysinc u
      rw [sum_range_one, e0]
      have := one_sub_sinc u
      push_cast
      linarith)
    (fun u _ hu => by
      have hu0 : u = 0 := by simpa using hu
      show -ysinc u = ((sincC 1 : ℚ) : ℝ)
      rw [e1, hu0]
      simp [ysinc]
      norm_num)
  exact (h.neg.congr fun u _ => by simp).congr_coeff fun i => by simp [yC]

/-! ### The logarithm -/

theorem sinc_ge {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : 5 / 6 ≤ sinc u := by
  have h := poly6_le_sinc h0
  have h2 : u ^ 2 ≤ 1 := by nlinarith
  have h4 : 0 ≤ u ^ 4 := by positivity
  have h6 : u ^ 6 ≤ u ^ 4 := by
    calc u ^ 6 = u ^ 4 * u ^ 2 := by ring
      _ ≤ u ^ 4 * 1 := mul_le_mul_of_nonneg_left h2 h4
      _ = u ^ 4 := by ring
  linarith

theorem sinc_le_one' {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : sinc u ≤ 1 := by
  have hg := sinc_le_gaussian (x := u) ⟨h0, by linarith [pi_gt_three]⟩
  have he : exp (-(u ^ 2 / 6)) ≤ 1 := exp_le_one_iff.2 (by nlinarith [sq_nonneg u])
  exact hg.trans he

/-- `-log (sin u / u)`. -/
noncomputable def Lsinc (u : ℝ) : ℝ := -log (sinc u)

theorem log_taylor_hasExp :
    HasExp (Set.Icc (0 : ℝ) 1) (fun u => 1 - sinc u) Lsinc (fun i => (hC i : ℝ)) := by
  intro P
  refine ⟨6 / 5, fun u hu => ?_⟩
  obtain ⟨h0, h1⟩ := hu
  show |Lsinc u - ∑ i ∈ range P, (hC i : ℝ) * (1 - sinc u) ^ i| ≤ 6 / 5 * |1 - sinc u| ^ P
  have hx0 : 0 ≤ 1 - sinc u := by linarith [sinc_le_one' h0 h1]
  have hx1 : 1 - sinc u ≤ 1 / 6 := by linarith [sinc_ge h0 h1]
  have hL : Lsinc u = -log (1 - (1 - sinc u)) := by
    rw [sub_sub_cancel]
    rfl
  rw [hL]
  generalize 1 - sinc u = x at hx0 hx1 ⊢
  have habs : |x| = x := abs_of_nonneg hx0
  have hax : |x| ≤ 1 / 6 := by rw [habs]; exact hx1
  have hlt : |x| < 1 := by linarith
  rcases P with _ | n
  · have h := abs_log_sub_add_sum_range_le hlt 0
    simp only [range_zero, sum_empty, zero_add, pow_one] at h
    simp only [range_zero, sum_empty, sub_zero, pow_zero, mul_one, abs_neg]
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]
    linarith
  · have h := abs_log_sub_add_sum_range_le hlt n
    have hs : ∑ i ∈ range (n + 1), (hC i : ℝ) * x ^ i =
        ∑ i ∈ range n, x ^ (i + 1) / ((i : ℝ) + 1) := by
      rw [sum_range_succ']
      have h0' : (hC 0 : ℝ) = 0 := by simp [hC]
      rw [h0', zero_mul, add_zero]
      refine sum_congr rfl fun i _ => ?_
      have hi : (hC (i + 1) : ℝ) = 1 / ((i : ℝ) + 1) := by simp [hC]
      rw [hi]
      ring
    have e : -log (1 - x) - ∑ i ∈ range n, x ^ (i + 1) / ((i : ℝ) + 1) =
        -((∑ i ∈ range n, x ^ (i + 1) / ((i : ℝ) + 1)) + log (1 - x)) := by ring
    rw [hs, e, abs_neg]
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (pow_nonneg (abs_nonneg x) (n + 1))
      (by linarith : (0 : ℝ) ≤ 1 / 6 - |x|)]

theorem Lsinc_hasExp :
    HasExp (Set.Icc (0 : ℝ) 1) (fun u => u ^ 2) Lsinc (fun i => (logC i : ℝ)) := by
  have h := log_taylor_hasExp.comp (w := fun u => u ^ 2) (y := ysinc)
    (fun u _ => one_sub_sinc u) ysinc_hasExp
  exact h.congr_coeff fun i => map_ccomp (Rat.castHom ℝ) hC yC i

/-! ### The correction to the Gaussian exponent -/

/-- `(-log (sin u / u) - u ^ 2 / 6) / u ^ 4`, continued by `1 / 180` at the origin. -/
noncomputable def kap (u : ℝ) : ℝ := if u = 0 then 1 / 180 else (Lsinc u - u ^ 2 / 6) / u ^ 4

theorem Lsinc_eq (u : ℝ) : Lsinc u = u ^ 2 / 6 + u ^ 4 * kap u := by
  unfold kap
  split_ifs with h
  · simp [h, Lsinc]
  · field_simp
    ring

theorem kap_hasExp :
    HasExp (Set.Icc (0 : ℝ) 1) (fun u => u ^ 2) kap (fun i => (kapC i : ℝ)) := by
  obtain ⟨hl0, hl1, hl2⟩ := logC_values
  have h := Lsinc_hasExp.shift 2 (g := kap)
    (fun u _ => by
      show Lsinc u = ∑ i ∈ range 2, (logC i : ℝ) * (u ^ 2) ^ i + (u ^ 2) ^ 2 * kap u
      rw [sum_range_succ, sum_range_one, hl0, hl1, Lsinc_eq u]
      push_cast
      ring)
    (fun u _ hu => by
      have hu0 : u = 0 := by simpa using hu
      show kap u = ((logC 2 : ℚ) : ℝ)
      rw [hl2, hu0]
      simp [kap])
  exact h.congr_coeff fun i => rfl

theorem sinc_eq_exp {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    sinc u = exp (-(u ^ 2 / 6 + u ^ 4 * kap u)) := by
  have hs : 0 < sinc u := by linarith [sinc_ge h0 h1]
  rw [← Lsinc_eq, Lsinc, neg_neg, exp_log hs]

theorem kap_nonneg {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : 0 ≤ kap u := by
  unfold kap
  split_ifs with h
  · norm_num
  · have hs : 0 < sinc u := by linarith [sinc_ge h0 h1]
    have hg := sinc_le_gaussian (x := u) ⟨h0, by linarith [pi_gt_three]⟩
    have hl : log (sinc u) ≤ -(u ^ 2 / 6) := by
      have h' := log_le_log hs hg
      rwa [log_exp] at h'
    apply div_nonneg _ (by positivity)
    unfold Lsinc
    linarith

theorem measurable_kap : Measurable kap := by
  unfold kap Lsinc
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  have hs : Measurable sinc := continuous_sinc.measurable
  have hl : Measurable fun u : ℝ => log (sinc u) := measurable_log.comp hs
  exact ((hl.neg).sub ((measurable_id.pow_const 2).div_const 6)).div (measurable_id.pow_const 4)

theorem kap_bdd : ∃ K : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) 1, |kap u| ≤ K := kap_hasExp.bdd

end PrivateApex
