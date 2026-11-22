import PrivateApex.EvenDirect
import PrivateApex.ApexDefinitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
PRIVATE.  Manuscript 15, Section 7: the angular deficits to every asymptotic order.

For odd `n = 2j + 1 ≥ 3` the interior angle at the real apex is `α_n = 2 arccot(s_n)`, and for
even `n = 2m ≥ 4` the interior angle at the virtual apex is `α_n^virt = 2 arccot(t_n)`.  With
`x = n + 1`, for every `p`,

  `π - α_n      = 2 √(216/(π x)) (∑ i < p, A i / x ^ i + O(x ^ (-p)))`   (`odd_angle_all_orders`),
  `π - α_n^virt = 2 √(864/(π x)) (∑ i < p, B i / x ^ i + O(x ^ (-p)))`   (`even_angle_all_orders`),

where `A i = angR (216/π) dC i` and `B i = angR (864/π) eC i` are polynomials in `1/π` with
rational coefficients:

  `angR a d i = ∑ k ≤ i, angQ d i k * a ^ k`,  `angQ d i k = (-1)^k/(2k+1) [z^(i-k)] D(z)^(2k+1)`.

These are asymptotic expansions in half-integer powers of `1/x`; they are obtained by composing
the asymptotic expansions of the slopes with the remainder estimate of the arctangent series
(`arctan_taylor`, valid for every nonnegative argument).  The rational numbers `angQ dC i k` and
`angQ eC i k` are evaluated by the kernel for `k ≤ i ≤ 8` (`angQ_dC_table`, `angQ_eC_table`);
the constant `π` is kept symbolic throughout.
-/

namespace PrivateApex
open Real Finset
open EulerianCert.LocalLimit (nonneg_of_deriv_nonneg)

/-! ### A termwise expansion lemma -/

section
variable {α : Type*} {S : Set α} {w f : α → ℝ}

/-- If `f` is approximated to every order `P` by `∑ i < P, c i * w ^ i * g i` and every `g i`
has an expansion with coefficients `B i`, then `f` has the expansion with coefficients
`∑ i ≤ m, c i * B i (m - i)`. -/
theorem HasExp.of_series {c : ℕ → ℝ} {g : ℕ → α → ℝ} {B : ℕ → ℕ → ℝ}
    (hf : ∀ P : ℕ, ∃ C : ℝ, ∀ x ∈ S,
      |f x - ∑ i ∈ range P, c i * w x ^ i * g i x| ≤ C * |w x| ^ P)
    (hg : ∀ i, HasExp S w (g i) (B i)) :
    HasExp S w f (fun m => ∑ i ∈ range (m + 1), c i * B i (m - i)) := by
  intro P
  obtain ⟨Cf, hCf⟩ := hf P
  have hpow : ∀ i : ℕ, ∃ C : ℝ, ∀ x ∈ S,
      |g i x - ∑ l ∈ range (P - i), B i l * w x ^ l| ≤ C * |w x| ^ (P - i) :=
    fun i => (hg i) (P - i)
  choose Cp hCp using hpow
  refine ⟨|Cf| + ∑ i ∈ range P, |c i| * |Cp i|, fun x hx => ?_⟩
  show |f x - ∑ m ∈ range P, (∑ i ∈ range (m + 1), c i * B i (m - i)) * w x ^ m| ≤
    (|Cf| + ∑ i ∈ range P, |c i| * |Cp i|) * |w x| ^ P
  have h1 : ∑ m ∈ range P, (∑ i ∈ range (m + 1), c i * B i (m - i)) * w x ^ m =
      ∑ i ∈ range P, ∑ l ∈ range (P - i), c i * B i l * w x ^ (i + l) := by
    rw [sum_triangle (fun i l => c i * B i l * w x ^ (i + l)) P]
    refine sum_congr rfl fun n _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i + (n - i) = n := by
      have := mem_range.1 hi
      omega
    show c i * B i (n - i) * w x ^ n = c i * B i (n - i) * w x ^ (i + (n - i))
    rw [hi']
  have h2 : ∀ i ∈ range P,
      c i * w x ^ i * (g i x - ∑ l ∈ range (P - i), B i l * w x ^ l) =
        c i * w x ^ i * g i x - ∑ l ∈ range (P - i), c i * B i l * w x ^ (i + l) := by
    intro i _
    rw [mul_sub, mul_sum]
    congr 1
    exact sum_congr rfl fun l _ => by ring
  have key : f x - ∑ m ∈ range P, (∑ i ∈ range (m + 1), c i * B i (m - i)) * w x ^ m =
      (f x - ∑ i ∈ range P, c i * w x ^ i * g i x) +
        ∑ i ∈ range P, c i * w x ^ i * (g i x - ∑ l ∈ range (P - i), B i l * w x ^ l) := by
    rw [h1, sum_congr rfl h2, sum_sub_distrib]
    ring
  have e1 : |f x - ∑ i ∈ range P, c i * w x ^ i * g i x| ≤ |Cf| * |w x| ^ P :=
    (hCf x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have e2 : |∑ i ∈ range P, c i * w x ^ i * (g i x - ∑ l ∈ range (P - i), B i l * w x ^ l)| ≤
      (∑ i ∈ range P, |c i| * |Cp i|) * |w x| ^ P := by
    rw [sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
    have hi' := mem_range.1 hi
    rw [abs_mul, abs_mul, abs_pow]
    have h' : |g i x - ∑ l ∈ range (P - i), B i l * w x ^ l| ≤ |Cp i| * |w x| ^ (P - i) :=
      (hCp i x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have hp : |w x| ^ i * |w x| ^ (P - i) = |w x| ^ P := by
      rw [← pow_add]
      congr 1
      omega
    calc |c i| * |w x| ^ i * |g i x - ∑ l ∈ range (P - i), B i l * w x ^ l|
        ≤ |c i| * |w x| ^ i * (|Cp i| * |w x| ^ (P - i)) :=
          mul_le_mul_of_nonneg_left h' (by positivity)
      _ = |c i| * |Cp i| * (|w x| ^ i * |w x| ^ (P - i)) := by ring
      _ = |c i| * |Cp i| * |w x| ^ P := by rw [hp]
  rw [key, add_mul]
  exact (abs_add_le _ _).trans (add_le_add e1 e2)

end

/-! ### The arctangent series with remainder -/

/-- Partial sums of the arctangent series. -/
noncomputable def arctanSum (P : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range P, (-1) ^ k * x ^ (2 * k + 1) / (2 * k + 1)

theorem hasDerivAt_arctanSum (P : ℕ) (x : ℝ) :
    HasDerivAt (arctanSum P) (∑ k ∈ range P, (-x ^ 2) ^ k) x := by
  have h : ∀ k ∈ range P,
      HasDerivAt (fun y : ℝ => (-1) ^ k * y ^ (2 * k + 1) / (2 * k + 1)) ((-x ^ 2) ^ k) x := by
    intro k _
    have h1 := ((hasDerivAt_pow (2 * k + 1) x).const_mul ((-1 : ℝ) ^ k)).div_const
      ((2 * k + 1 : ℝ))
    convert h1 using 1
    rw [Nat.add_sub_cancel, neg_pow, ← pow_mul]
    push_cast
    field_simp
  exact HasDerivAt.fun_sum h

/-- For `x ≥ 0` the remainder of the arctangent series is at most its first omitted power;
no restriction `x ≤ 1` is needed. -/
theorem arctan_taylor (P : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |arctan x - arctanSum P x| ≤ x ^ (2 * P + 1) := by
  have hd : ∀ y : ℝ, |1 / (1 + y ^ 2) - ∑ k ∈ range P, (-y ^ 2) ^ k| ≤ (y ^ 2) ^ P := by
    intro y
    have hpos : 0 < 1 + y ^ 2 := by positivity
    have hq := geom_sum_mul (-y ^ 2) P
    have e : 1 / (1 + y ^ 2) - ∑ k ∈ range P, (-y ^ 2) ^ k = (-y ^ 2) ^ P / (1 + y ^ 2) := by
      rw [eq_div_iff hpos.ne', sub_mul, one_div_mul_cancel hpos.ne']
      linear_combination hq
    rw [e, abs_div, abs_of_pos hpos, abs_pow, abs_neg, abs_of_nonneg (sq_nonneg y)]
    exact div_le_self (by positivity) (by nlinarith [sq_nonneg y])
  have hB : ∀ y : ℝ, HasDerivAt (fun y : ℝ => y ^ (2 * P + 1) / (2 * P + 1))
      ((y ^ 2) ^ P) y := by
    intro y
    have h := (hasDerivAt_pow (2 * P + 1) y).div_const ((2 * P + 1 : ℝ))
    convert h using 1
    rw [Nat.add_sub_cancel, ← pow_mul]
    push_cast
    field_simp
  have hR : ∀ y : ℝ, HasDerivAt (fun y => arctan y - arctanSum P y)
      (1 / (1 + y ^ 2) - ∑ k ∈ range P, (-y ^ 2) ^ k) y :=
    fun y => (hasDerivAt_arctan y).sub (hasDerivAt_arctanSum P y)
  have h0 : arctanSum P 0 = 0 := by
    unfold arctanSum
    simp
  have up : 0 ≤ x ^ (2 * P + 1) / (2 * P + 1) - (arctan x - arctanSum P x) :=
    nonneg_of_deriv_nonneg
      (f := fun y => y ^ (2 * P + 1) / (2 * P + 1) - (arctan y - arctanSum P y))
      (f' := fun y => (y ^ 2) ^ P - (1 / (1 + y ^ 2) - ∑ k ∈ range P, (-y ^ 2) ^ k))
      (fun y => (hB y).sub (hR y)) (by simp [h0])
      (fun y _ => by
        have h := abs_le.1 (hd y)
        linarith [h.2]) hx
  have lo : 0 ≤ x ^ (2 * P + 1) / (2 * P + 1) + (arctan x - arctanSum P x) :=
    nonneg_of_deriv_nonneg
      (f := fun y => y ^ (2 * P + 1) / (2 * P + 1) + (arctan y - arctanSum P y))
      (f' := fun y => (y ^ 2) ^ P + (1 / (1 + y ^ 2) - ∑ k ∈ range P, (-y ^ 2) ^ k))
      (fun y => (hB y).add (hR y)) (by simp [h0])
      (fun y _ => by
        have h := abs_le.1 (hd y)
        linarith [h.1]) hx
  have hle : x ^ (2 * P + 1) / (2 * (P : ℝ) + 1) ≤ x ^ (2 * P + 1) :=
    div_le_self (pow_nonneg hx _) (by
      have : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg P
      linarith)
  rw [abs_le]
  constructor <;> linarith

/-! ### Composition with the arctangent -/

section
variable {α : Type*} {S : Set α}

/-- If `σ ^ 2 = a * w` and `Sn` expands in `w` with coefficients `d`, then
`arctan (σ * Sn) / σ` expands in `w` with the coefficients
`∑ k ≤ m, (-1)^k/(2k+1) a^k [z^(m-k)] D(z)^(2k+1)`. -/
theorem arctan_hasExp {w σ Sn : α → ℝ} {d : ℕ → ℝ} (a : ℝ) (ha : 0 ≤ a)
    (hw : ∀ x ∈ S, 0 ≤ w x) (hσ : ∀ x ∈ S, 0 < σ x) (hσ2 : ∀ x ∈ S, σ x ^ 2 = a * w x)
    (hs : ∀ x ∈ S, 0 ≤ Sn x) (hS : HasExp S w Sn d) :
    HasExp S w (fun x => arctan (σ x * Sn x) / σ x)
      (fun m => ∑ k ∈ range (m + 1),
        ((-1) ^ k / (2 * k + 1) * a ^ k) * cpow d (2 * k + 1) (m - k)) := by
  refine HasExp.of_series (c := fun k => (-1) ^ k / (2 * k + 1) * a ^ k)
    (g := fun k x => Sn x ^ (2 * k + 1)) (B := fun k => cpow d (2 * k + 1)) ?_
    (fun k => hS.pow (2 * k + 1))
  intro P
  obtain ⟨Y, hY⟩ := hS.bdd
  refine ⟨a ^ P * |Y| ^ (2 * P + 1), fun x hx => ?_⟩
  have hσx := hσ x hx
  have hwx := hw x hx
  have hsx := hs x hx
  have hterm : ∀ k ∈ range P,
      (-1 : ℝ) ^ k * (σ x * Sn x) ^ (2 * k + 1) / (2 * k + 1) =
        σ x * (((-1) ^ k / (2 * k + 1) * a ^ k) * w x ^ k * Sn x ^ (2 * k + 1)) := by
    intro k _
    have e : σ x ^ (2 * k + 1) = (a * w x) ^ k * σ x := by rw [pow_succ, pow_mul, hσ2 x hx]
    rw [mul_pow, e, mul_pow]
    ring
  have hsum : arctanSum P (σ x * Sn x) = σ x * ∑ k ∈ range P,
      ((-1) ^ k / (2 * k + 1) * a ^ k) * w x ^ k * Sn x ^ (2 * k + 1) := by
    unfold arctanSum
    rw [mul_sum]
    exact sum_congr rfl hterm
  have hs0 : 0 ≤ σ x * Sn x := mul_nonneg hσx.le hsx
  have ht := arctan_taylor P hs0
  have e : arctan (σ x * Sn x) / σ x - ∑ k ∈ range P,
      ((-1) ^ k / (2 * k + 1) * a ^ k) * w x ^ k * Sn x ^ (2 * k + 1) =
      (arctan (σ x * Sn x) - arctanSum P (σ x * Sn x)) / σ x := by
    rw [hsum]
    field_simp
  show |arctan (σ x * Sn x) / σ x - ∑ k ∈ range P,
      ((-1) ^ k / (2 * k + 1) * a ^ k) * w x ^ k * Sn x ^ (2 * k + 1)| ≤
    a ^ P * |Y| ^ (2 * P + 1) * |w x| ^ P
  rw [e, abs_div, abs_of_pos hσx, div_le_iff₀ hσx, abs_of_nonneg hwx]
  have hpow : (σ x * Sn x) ^ (2 * P + 1) = (a * w x) ^ P * σ x * Sn x ^ (2 * P + 1) := by
    rw [mul_pow, pow_succ (σ x), pow_mul, hσ2 x hx]
  have hSn : Sn x ^ (2 * P + 1) ≤ |Y| ^ (2 * P + 1) :=
    pow_le_pow_left₀ hsx ((le_abs_self _).trans ((hY x hx).trans (le_abs_self Y))) _
  calc |arctan (σ x * Sn x) - arctanSum P (σ x * Sn x)| ≤ (σ x * Sn x) ^ (2 * P + 1) := ht
    _ = (a * w x) ^ P * σ x * Sn x ^ (2 * P + 1) := hpow
    _ ≤ (a * w x) ^ P * σ x * |Y| ^ (2 * P + 1) :=
        mul_le_mul_of_nonneg_left hSn (by positivity)
    _ = a ^ P * |Y| ^ (2 * P + 1) * w x ^ P * σ x := by
        rw [mul_pow]
        ring

end

/-! ### Coefficients -/

/-- `angQ d j k = (-1)^k/(2k+1) [z^(j-k)] D(z)^(2k+1)`: the rational coefficient of `a ^ k` in
the `j`-th coefficient of the angular-deficit expansion. -/
def angQ (d : ℕ → ℚ) (j k : ℕ) : ℚ := (-1) ^ k / (2 * k + 1) * cpow d (2 * k + 1) (j - k)

/-- The `j`-th coefficient of the angular-deficit expansion, a polynomial in the constant `a`. -/
noncomputable def angR (a : ℝ) (d : ℕ → ℚ) (j : ℕ) : ℝ :=
  ∑ k ∈ range (j + 1), (angQ d j k : ℝ) * a ^ k

theorem angR_eq (a : ℝ) (d : ℕ → ℚ) (j : ℕ) :
    angR a d j = ∑ k ∈ range (j + 1),
      ((-1) ^ k / (2 * k + 1) * a ^ k) * cpow (fun i => (d i : ℝ)) (2 * k + 1) (j - k) := by
  unfold angR angQ
  refine sum_congr rfl fun k _ => ?_
  push_cast
  rw [show ((cpow d (2 * k + 1) (j - k) : ℚ) : ℝ) = cpow (fun i => (d i : ℝ)) (2 * k + 1) (j - k)
    from map_cpow (Rat.castHom ℝ) d (2 * k + 1) (j - k)]
  ring

/-! ### The angular deficits -/

theorem realApexAngle_eq (j : ℕ) : realApexAngle j = virtualApex (2 * j + 1) := by
  unfold realApexAngle virtualApex
  rw [sOdd_eq]

theorem virtualApexAngle_eq' {m : ℕ} (hm : 1 ≤ m) : virtualApexAngle m = virtualApex (2 * m) := by
  unfold virtualApexAngle virtualApex
  rw [tEven_eq hm]

/-- Odd orders, normalised form. -/
theorem odd_angle_hasExp :
    HasExp {j : ℕ | 1 ≤ j} (fun j => 1 / ((2 * j + 2 : ℕ) : ℝ))
      (fun j => (π - realApexAngle j) / (2 * sig ((2 * j + 2 : ℕ) : ℝ)))
      (angR (216 / π) dC) := by
  have h := arctan_hasExp (S := {j : ℕ | 1 ≤ j}) (w := fun j => 1 / ((2 * j + 2 : ℕ) : ℝ))
    (σ := fun j => sig ((2 * j + 2 : ℕ) : ℝ))
    (Sn := fun j => ((slopeQ (2 * j + 1) : ℚ) : ℝ) / sig ((2 * j + 2 : ℕ) : ℝ))
    (216 / π) (by positivity) (fun j _ => by positivity)
    (fun j _ => sig_pos' (by positivity))
    (fun j _ => by
      show sig ((2 * j + 2 : ℕ) : ℝ) ^ 2 = 216 / π * (1 / ((2 * j + 2 : ℕ) : ℝ))
      unfold sig
      rw [sq_sqrt (by positivity)]
      field_simp)
    (fun j hj => by
      have hpos : (0 : ℝ) < ((slopeQ (2 * j + 1) : ℚ) : ℝ) := by
        exact_mod_cast (slopeQ_classification (2 * j + 1)
          (by have : 1 ≤ j := hj; omega)).1
      exact div_nonneg hpos.le (sig_pos' (by positivity)).le)
    odd_slope_hasExp
  refine (h.congr fun j hj => ?_).congr_coeff fun i => angR_eq (216 / π) dC i
  have hj' : 1 ≤ j := hj
  have hsig := sig_pos' (x := ((2 * j + 2 : ℕ) : ℝ)) (by positivity)
  have e : sig ((2 * j + 2 : ℕ) : ℝ) *
      (((slopeQ (2 * j + 1) : ℚ) : ℝ) / sig ((2 * j + 2 : ℕ) : ℝ)) =
      ((slopeQ (2 * j + 1) : ℚ) : ℝ) := by field_simp
  show (π - realApexAngle j) / (2 * sig ((2 * j + 2 : ℕ) : ℝ)) =
    arctan (sig ((2 * j + 2 : ℕ) : ℝ) *
      (((slopeQ (2 * j + 1) : ℚ) : ℝ) / sig ((2 * j + 2 : ℕ) : ℝ))) /
      sig ((2 * j + 2 : ℕ) : ℝ)
  rw [e, realApexAngle_eq, virtualApex_eq (2 * j + 1) (by omega),
    div_eq_div_iff (by positivity) hsig.ne']
  ring

/-- Even orders, normalised form. -/
theorem even_angle_hasExp :
    HasExp {m : ℕ | 2 ≤ m} (fun m => 1 / ((2 * m + 1 : ℕ) : ℝ))
      (fun m => (π - virtualApexAngle m) / (2 * (2 * sig ((2 * m + 1 : ℕ) : ℝ))))
      (angR (864 / π) eC) := by
  have h := arctan_hasExp (S := {m : ℕ | 2 ≤ m}) (w := fun m => 1 / ((2 * m + 1 : ℕ) : ℝ))
    (σ := fun m => 2 * sig ((2 * m + 1 : ℕ) : ℝ))
    (Sn := fun m => ((slopeQ (2 * m) : ℚ) : ℝ) / (2 * sig ((2 * m + 1 : ℕ) : ℝ)))
    (864 / π) (by positivity) (fun m _ => by positivity)
    (fun m _ => by
      have := sig_pos' (x := ((2 * m + 1 : ℕ) : ℝ)) (by positivity)
      positivity)
    (fun m _ => by
      show (2 * sig ((2 * m + 1 : ℕ) : ℝ)) ^ 2 = 864 / π * (1 / ((2 * m + 1 : ℕ) : ℝ))
      unfold sig
      rw [mul_pow, sq_sqrt (by positivity)]
      field_simp
      ring)
    (fun m hmem => by
      have hpos : (0 : ℝ) < ((slopeQ (2 * m) : ℚ) : ℝ) := by
        exact_mod_cast (slopeQ_classification (2 * m)
          (by have : 2 ≤ m := hmem; omega)).1
      have := sig_pos' (x := ((2 * m + 1 : ℕ) : ℝ)) (by positivity)
      exact div_nonneg hpos.le (by positivity))
    even_slope_hasExp
  refine (h.congr fun m hmem => ?_).congr_coeff fun i => angR_eq (864 / π) eC i
  have hm' : 2 ≤ m := hmem
  have hsig := sig_pos' (x := ((2 * m + 1 : ℕ) : ℝ)) (by positivity)
  have e : 2 * sig ((2 * m + 1 : ℕ) : ℝ) *
      (((slopeQ (2 * m) : ℚ) : ℝ) / (2 * sig ((2 * m + 1 : ℕ) : ℝ))) =
      ((slopeQ (2 * m) : ℚ) : ℝ) := by field_simp
  show (π - virtualApexAngle m) / (2 * (2 * sig ((2 * m + 1 : ℕ) : ℝ))) =
    arctan (2 * sig ((2 * m + 1 : ℕ) : ℝ) *
      (((slopeQ (2 * m) : ℚ) : ℝ) / (2 * sig ((2 * m + 1 : ℕ) : ℝ)))) /
      (2 * sig ((2 * m + 1 : ℕ) : ℝ))
  rw [e, virtualApexAngle_eq' (by omega), virtualApex_eq (2 * m) (by omega),
    div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **Angular deficit at the real apex, odd orders, to every order.**  For `n = 2j + 1 ≥ 3` and
`x = n + 1`, `π - α_n = 2 √(216/(π x)) (∑ i < p, A i / x ^ i + O(x ^ (-p)))`. -/
theorem odd_angle_all_orders (p : ℕ) : ∃ K : ℝ, ∀ j : ℕ, 1 ≤ j →
    |(π - realApexAngle j) - 2 * √(216 / (π * ((2 * j + 2 : ℕ) : ℝ))) *
        ∑ i ∈ range p, angR (216 / π) dC i / ((2 * j + 2 : ℕ) : ℝ) ^ i| ≤
      K * (2 * √(216 / (π * ((2 * j + 2 : ℕ) : ℝ)))) / ((2 * j + 2 : ℕ) : ℝ) ^ p := by
  obtain ⟨C, hC⟩ := odd_angle_hasExp p
  refine ⟨C, fun j hj => ?_⟩
  have hx : (0 : ℝ) < ((2 * j + 2 : ℕ) : ℝ) := by positivity
  have hσ : 0 < 2 * sig ((2 * j + 2 : ℕ) : ℝ) := by
    have := sig_pos' hx
    positivity
  exact of_ratio (σ := 2 * sig ((2 * j + 2 : ℕ) : ℝ)) hσ hx (hC j hj)

/-- **Angular deficit at the virtual apex, even orders, to every order.**  For `n = 2m ≥ 4` and
`x = n + 1`, `π - α_n^virt = 2 √(864/(π x)) (∑ i < p, B i / x ^ i + O(x ^ (-p)))`. -/
theorem even_angle_all_orders (p : ℕ) : ∃ K : ℝ, ∀ m : ℕ, 2 ≤ m →
    |(π - virtualApexAngle m) - 2 * √(864 / (π * ((2 * m + 1 : ℕ) : ℝ))) *
        ∑ i ∈ range p, angR (864 / π) eC i / ((2 * m + 1 : ℕ) : ℝ) ^ i| ≤
      K * (2 * √(864 / (π * ((2 * m + 1 : ℕ) : ℝ)))) / ((2 * m + 1 : ℕ) : ℝ) ^ p := by
  obtain ⟨C, hC⟩ := even_angle_hasExp p
  refine ⟨C, fun m hm => ?_⟩
  have hx : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hσ : 0 < 2 * (2 * sig ((2 * m + 1 : ℕ) : ℝ)) := by
    have := sig_pos' hx
    positivity
  rw [sqrt_864]
  exact of_ratio (σ := 2 * (2 * sig ((2 * m + 1 : ℕ) : ℝ))) hσ hx (hC m hm)

/-! ### Explicit coefficients up to the eighth order -/

theorem cpow_congr {K : Type*} [CommRing K] {a b : ℕ → K} (r : ℕ) :
    ∀ n : ℕ, (∀ i ≤ n, a i = b i) → cpow a r n = cpow b r n := by
  induction r with
  | zero =>
    intro n _
    rfl
  | succ r ih =>
    intro n h
    rw [cpow_succ, cpow_succ]
    unfold cmul
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hi)
    rw [ih i (fun l hl => h l (hl.trans hi')), h (n - i) (Nat.sub_le n i)]

/-- The odd-order slope coefficients `d_0, …, d_8`. -/
def dTab : ℕ → ℚ := fun i =>
  [1, -15 / 4, 1829 / 160, -101709 / 3200, 29934309 / 358400, -7564058487 / 35840000, 1040050193381 / 2007040000, -9992447718861 / 8028160000, 41506811168654933 / 14129561600000].getD i 0

/-- The even-order slope coefficients `e_0, …, e_8`. -/
def eTab : ℕ → ℚ := fun i =>
  [1, -33 / 4, 7589 / 160, -744579 / 3200, 373339749 / 358400, -157351476537 / 35840000, 7113539517793 / 401408000, -555794725125891 / 8028160000, 3724416486067410773 / 14129561600000].getD i 0

theorem dC_eq_dTab : ∀ i ∈ range 9, dC i = dTab i := by decide +kernel

theorem eDirect_eq_eTab : ∀ i ∈ range 9, eDirect i = eTab i := by decide +kernel

theorem eC_eq_eTab : ∀ i ∈ range 9, eC i = eTab i := fun i hi => by
  rw [← eDirect_apply]
  exact eDirect_eq_eTab i hi

/-- `oddAngTab j k = angQ dC j k` for `k ≤ j ≤ 8`. -/
def oddAngTab : ℕ → ℕ → ℚ := fun j k =>
  (([
    [1],
    [-15 / 4, -1 / 3],
    [1829 / 160, 15 / 4, 1 / 5],
    [-101709 / 3200, -4079 / 160, -15 / 4, -1 / 7],
    [29934309 / 358400, 432309 / 3200, 6329 / 160, 15 / 4, 1 / 9],
    [-7564058487 / 35840000, -219816743 / 358400, -987909 / 3200, -8579 / 160, -15 / 4, -1 / 11],
    [1040050193381 / 2007040000, 89640079527 / 35840000, 711028177 / 358400, 1768509 / 3200, 10829 / 160, 15 / 4, 1 / 13],
    [-9992447718861 / 8028160000, -56708519836061 / 6021120000, -397778706567 / 35840000, -1645318611 / 358400, -2774109 / 3200, -13079 / 160, -15 / 4, -1 / 15],
    [41506811168654933 / 14129561600000, 1338132434647257 / 40140800000, 112190884148073 / 2007040000, 1168607939607 / 35840000, 632887609 / 71680, 4004709 / 3200, 15329 / 160, 15 / 4, 1 / 17]] : List (List ℚ)).getD j []).getD k 0

/-- `evenAngTab j k = angQ eC j k` for `k ≤ j ≤ 8`. -/
def evenAngTab : ℕ → ℕ → ℚ := fun j k =>
  (([
    [1],
    [-33 / 4, -1 / 3],
    [7589 / 160, 33 / 4, 1 / 5],
    [-744579 / 3200, -18479 / 160, -33 / 4, -1 / 7],
    [373339749 / 358400, 3847899 / 3200, 29369 / 160, 33 / 4, 1 / 9],
    [-157351476537 / 35840000, -148505663 / 14336, -9347019 / 3200, -40259 / 160, -33 / 4, -1 / 11],
    [7113539517793 / 401408000, 2797238275977 / 35840000, 13340308561 / 358400, 17241939 / 3200, 51149 / 160, 33 / 4, 1 / 13],
    [-555794725125891 / 8028160000, -3201360486378077 / 6021120000, -2065771223631 / 5120000, -32576919507 / 358400, -27532659 / 3200, -62039 / 160, -33 / 4, -1 / 15],
    [3724416486067410773 / 14129561600000, 134353820443360887 / 40140800000, 7749184740459753 / 2007040000, 46070530360857 / 35840000, 64743053213 / 358400, 40219179 / 3200, 72929 / 160, 33 / 4, 1 / 17]] : List (List ℚ)).getD j []).getD k 0

theorem angQ_dTab_table : ∀ j ∈ range 9, ∀ k ∈ range (j + 1), angQ dTab j k = oddAngTab j k := by
  decide +kernel

theorem angQ_eTab_table :
    ∀ j ∈ range 9, ∀ k ∈ range (j + 1), angQ eTab j k = evenAngTab j k := by
  decide +kernel

theorem angQ_congr {a b : ℕ → ℚ} {j : ℕ} (h : ∀ i ≤ j, a i = b i) (k : ℕ) :
    angQ a j k = angQ b j k := by
  unfold angQ
  rw [cpow_congr (2 * k + 1) (j - k) fun i hi => h i (hi.trans (Nat.sub_le j k))]

/-- The rational coefficients of the odd-order angular deficit, `k ≤ j ≤ 8`. -/
theorem angQ_dC_table {j k : ℕ} (hj : j ≤ 8) (hk : k ≤ j) : angQ dC j k = oddAngTab j k := by
  rw [angQ_congr (b := dTab) (fun i hi => dC_eq_dTab i (mem_range.2 (by omega))) k]
  exact angQ_dTab_table j (mem_range.2 (by omega)) k (mem_range.2 (by omega))

/-- The rational coefficients of the even-order angular deficit, `k ≤ j ≤ 8`. -/
theorem angQ_eC_table {j k : ℕ} (hj : j ≤ 8) (hk : k ≤ j) : angQ eC j k = evenAngTab j k := by
  rw [angQ_congr (b := eTab) (fun i hi => eC_eq_eTab i (mem_range.2 (by omega))) k]
  exact angQ_eTab_table j (mem_range.2 (by omega)) k (mem_range.2 (by omega))

theorem angR_dC_explicit {j : ℕ} (hj : j ≤ 8) :
    angR (216 / π) dC j = ∑ k ∈ range (j + 1), (oddAngTab j k : ℝ) * (216 / π) ^ k := by
  unfold angR
  refine sum_congr rfl fun k hk => ?_
  rw [angQ_dC_table hj (Nat.lt_succ_iff.1 (mem_range.1 hk))]

theorem angR_eC_explicit {j : ℕ} (hj : j ≤ 8) :
    angR (864 / π) eC j = ∑ k ∈ range (j + 1), (evenAngTab j k : ℝ) * (864 / π) ^ k := by
  unfold angR
  refine sum_congr rfl fun k hk => ?_
  rw [angQ_eC_table hj (Nat.lt_succ_iff.1 (mem_range.1 hk))]

/-- Odd orders with the nine explicit coefficients `A_0, …, A_8` and remainder `O(x ^ (-9))`;
`π` is kept symbolic and the rational numbers are those of `oddAngTab`. -/
theorem odd_angle_eighth_order : ∃ K : ℝ, ∀ j : ℕ, 1 ≤ j →
    |(π - realApexAngle j) - 2 * √(216 / (π * ((2 * j + 2 : ℕ) : ℝ))) *
        ∑ i ∈ range 9, (∑ k ∈ range (i + 1), (oddAngTab i k : ℝ) * (216 / π) ^ k) /
          ((2 * j + 2 : ℕ) : ℝ) ^ i| ≤
      K * (2 * √(216 / (π * ((2 * j + 2 : ℕ) : ℝ)))) / ((2 * j + 2 : ℕ) : ℝ) ^ 9 := by
  obtain ⟨K, hK⟩ := odd_angle_all_orders 9
  refine ⟨K, fun j hj => ?_⟩
  have h := hK j hj
  rw [sum_congr rfl fun i hi => by
    rw [angR_dC_explicit (Nat.lt_succ_iff.1 (mem_range.1 hi))]] at h
  exact h

/-- Even orders with the nine explicit coefficients `B_0, …, B_8` and remainder `O(x ^ (-9))`;
`π` is kept symbolic and the rational numbers are those of `evenAngTab`. -/
theorem even_angle_eighth_order : ∃ K : ℝ, ∀ m : ℕ, 2 ≤ m →
    |(π - virtualApexAngle m) - 2 * √(864 / (π * ((2 * m + 1 : ℕ) : ℝ))) *
        ∑ i ∈ range 9, (∑ k ∈ range (i + 1), (evenAngTab i k : ℝ) * (864 / π) ^ k) /
          ((2 * m + 1 : ℕ) : ℝ) ^ i| ≤
      K * (2 * √(864 / (π * ((2 * m + 1 : ℕ) : ℝ)))) / ((2 * m + 1 : ℕ) : ℝ) ^ 9 := by
  obtain ⟨K, hK⟩ := even_angle_all_orders 9
  refine ⟨K, fun m hm => ?_⟩
  have h := hK m hm
  rw [sum_congr rfl fun i hi => by
    rw [angR_eC_explicit (Nat.lt_succ_iff.1 (mem_range.1 hi))]] at h
  exact h

end PrivateApex
