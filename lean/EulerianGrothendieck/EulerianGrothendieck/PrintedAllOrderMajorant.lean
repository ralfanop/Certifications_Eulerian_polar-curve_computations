import EulerianGrothendieck.BernoulliCumulantIdentification
import EulerianGrothendieck.UniformRatioBounds
import EulerianGrothendieck.UniformNormAsymptotics
import EulerianGrothendieck.SummationRemainder
import EulerianGrothendieck.GeometricSummability
import EulerianGrothendieck.UniformVacuumAsymptotics
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Task G2: the printed all-index majorants and the printed constant `C^{(N)}_{t,R}`

`g_r(k)` is the coefficient of `h^r` in the exact moment polynomial
(`(uniformRatioPolynomial k).coeff r`, so that `R_{k,M} = ∑_r g_r(k) M^{-r}`), and
`q_r(k) = ∑_{j ≤ r} g_j(k) g_{r-j}(k)` (`(uniformSquaredPolynomial k).coeff r`).

* `standardUniformCumulant_sharp_bound`: `|κ_j| ≤ (1/2)(1/3)^j`, from the Bernoulli
  identification and Euler's `ζ(2m) ≤ π²/6`;
* `uniformRatio_sharp_coefficient_bound`: `|g_r(k)| ≤ e (8k²)^r`  (eg:eq:majorant);
* `uniformSquared_sharp_coefficient_bound`: `|q_r(k)| ≤ (r+1) e² (8k²)^r` (eg:eq:majorant-q);
* `printed_all_order_norm_remainder`: for `0 < t < 1`, `R ≥ 0`, `M ≥ 4096`,
  `|N - ∑_{r ≤ R} A_r(t) M^{-r}| ≤ C^{(N)}_{t,R} M^{-R-1}` with exactly
  `C^{(N)}_{t,R} = ∑_{k ≥ 1} t^{2k}[(2R+6)e² 8^{R+1} k^{2R+2} + k^{3(R+1)}(1 + e² ∑_{r ≤ R}(r+1)8^r k^{2r})]`. -/

noncomputable section
open scoped BigOperators Nat Real
open Polynomial Finset
namespace EulerianGrothendieck

/-- `|2^{2m-1} π^{2m} B_{2m}/(2m)!| = ζ(2m) ≤ π²/6` for `m ≥ 1`. -/
theorem bernoulli_zeta_bound (m : ℕ) (hm : m ≠ 0) :
    |(2:ℝ) ^ (2*m-1) * π ^ (2*m) * (_root_.bernoulli (2*m) : ℝ) / ((2*m) ! : ℝ)| ≤ π ^ 2 / 6 := by
  have h := hasSum_zeta_nat hm
  have hle : ((-1:ℝ) ^ (m+1) * 2 ^ (2*m-1) * π ^ (2*m) * _root_.bernoulli (2*m) / (2*m)!) ≤ π ^ 2 / 6 := by
    refine hasSum_le (fun n => ?_) h hasSum_zeta_two
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, zero_pow (show 2*m ≠ 0 by omega), zero_pow two_ne_zero, le_refl]
    · have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ h1 (by omega)
  have hge : 0 ≤ ((-1:ℝ) ^ (m+1) * 2 ^ (2*m-1) * π ^ (2*m) * _root_.bernoulli (2*m) / (2*m)!) :=
    hasSum_le (fun n => by show (0:ℝ) ≤ 1 / (n:ℝ) ^ (2*m); positivity) hasSum_zero h
  have hsign : |(-1:ℝ) ^ (m+1)| = 1 := by simp
  have hval : (-1:ℝ) ^ (m+1) * 2 ^ (2*m-1) * π ^ (2*m) * (_root_.bernoulli (2*m) : ℝ) / ((2*m) ! : ℝ) =
      (-1:ℝ) ^ (m+1) * ((2:ℝ) ^ (2*m-1) * π ^ (2*m) * (_root_.bernoulli (2*m) : ℝ) / ((2*m) ! : ℝ)) := by
    ring
  calc |(2:ℝ) ^ (2*m-1) * π ^ (2*m) * (_root_.bernoulli (2*m) : ℝ) / ((2*m) ! : ℝ)|
      = |(-1:ℝ) ^ (m+1)| * |(2:ℝ) ^ (2*m-1) * π ^ (2*m) * (_root_.bernoulli (2*m) : ℝ) / ((2*m) ! : ℝ)| := by
        rw [hsign, one_mul]
    _ = |(-1:ℝ) ^ (m+1) * ((2:ℝ) ^ (2*m-1) * π ^ (2*m) * (_root_.bernoulli (2*m) : ℝ) / ((2*m) ! : ℝ))| :=
        (abs_mul _ _).symm
    _ = (-1:ℝ) ^ (m+1) * ((2:ℝ) ^ (2*m-1) * π ^ (2*m) * (_root_.bernoulli (2*m) : ℝ) / ((2*m) ! : ℝ)) :=
        abs_of_nonneg (by rw [← hval]; exact hge)
    _ ≤ π ^ 2 / 6 := by rw [← hval]; exact hle

/-- **`|κ_j| ≤ (1/2)(1/3)^j`** for the standardised uniform cumulants. -/
theorem standardUniformCumulant_sharp_bound (j : ℕ) :
    |standardUniformCumulant j| ≤ (1/2) * (1/3:ℝ) ^ j := by
  rw [standardUniformCumulant_bernoulli]
  have hb := bernoulli_zeta_bound (j+1) (by omega)
  rw [show 2*(j+1) = 2*j+2 by ring, show 2*j+2-1 = 2*j+1 by omega] at hb
  have hpi : 0 < π := Real.pi_pos
  have hpi9 : 9 < π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hpow : 0 < π ^ (2*j+2) := by positivity
  have hfac : (0:ℝ) < ((2*j+2) ! : ℝ) := by positivity
  have hpow' : π ^ (2*j+2) ≠ 0 := hpow.ne'
  have hfac' : ((2*j+2) ! : ℝ) ≠ 0 := hfac.ne'
  have hexpr : (3:ℝ) ^ (j+1) * 2 ^ (2*j+1) * (_root_.bernoulli (2*j+2) : ℝ) / ((2*j+2) ! : ℝ) =
      (3:ℝ) ^ (j+1) / π ^ (2*j+2) *
        ((2:ℝ) ^ (2*j+1) * π ^ (2*j+2) * (_root_.bernoulli (2*j+2) : ℝ) / ((2*j+2) ! : ℝ)) := by
    field_simp <;> ring
  rw [hexpr, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 3 ^ (j+1) / π ^ (2*j+2))]
  calc (3:ℝ) ^ (j+1) / π ^ (2*j+2) *
        |(2:ℝ) ^ (2*j+1) * π ^ (2*j+2) * (_root_.bernoulli (2*j+2) : ℝ) / ((2*j+2) ! : ℝ)|
      ≤ (3:ℝ) ^ (j+1) / π ^ (2*j+2) * (π ^ 2 / 6) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (1/2) * (3 / π ^ 2) ^ j := by
        rw [show π ^ (2*j+2) = (π ^ 2) ^ j * π ^ 2 by ring, div_pow, pow_succ]
        field_simp <;> ring
    _ ≤ (1/2) * (1/3:ℝ) ^ j := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply pow_le_pow_left₀ (by positivity)
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

theorem ratioRecurrenceCoefficient_sharp_bound (n j : ℕ) :
    |ratioRecurrenceCoefficient n j| ≤ (2 * (n:ℝ) / 3) ^ j := by
  unfold ratioRecurrenceCoefficient
  have hf : (n.descFactorial j : ℝ) ≤ (n:ℝ) ^ j := by exact_mod_cast Nat.descFactorial_le_pow n j
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 ^ (j+1)),
    abs_of_nonneg (Nat.cast_nonneg _)]
  have hk := standardUniformCumulant_sharp_bound j
  calc (2:ℝ) ^ (j+1) * (n.descFactorial j : ℝ) * |standardUniformCumulant j|
      ≤ 2 ^ (j+1) * (n:ℝ) ^ j * ((1/2) * (1/3:ℝ) ^ j) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hf (by positivity)) hk (abs_nonneg _)
        positivity
    _ = (2 * (n:ℝ) / 3) ^ j := by
        rw [div_pow (2 * (n:ℝ)) 3 j, mul_pow (2:ℝ) (n:ℝ) j, div_pow (1:ℝ) 3 j, one_pow, pow_succ]
        ring

theorem coeff_recurrence_term (n r j : ℕ) :
    (C (ratioRecurrenceCoefficient n j) * X ^ j * uniformRatioPolynomial (n - j)).coeff r =
      if j ≤ r then ratioRecurrenceCoefficient n j * (uniformRatioPolynomial (n - j)).coeff (r - j)
      else 0 := by
  rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  split_ifs <;> simp

/-- **`|g_r(k)| ≤ e (8k²)^r`** for every `k` and `r` (eg:eq:majorant). -/
theorem uniformRatio_sharp_coefficient_bound (k r : ℕ) :
    |(uniformRatioPolynomial k).coeff r| ≤ Real.exp 1 * (8 * (k:ℝ) ^ 2) ^ r := by
  have he : (1:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ); linarith
  induction k using Nat.strong_induction_on generalizing r with
  | h k ih =>
    cases k with
    | zero =>
      rw [uniformRatioPolynomial_zero, Polynomial.coeff_one]
      split_ifs with h
      · subst h; simpa using he
      · rw [abs_zero]; positivity
    | succ n =>
      rw [uniformRatioPolynomial_recurrence, Polynomial.finset_sum_coeff]
      simp_rw [coeff_recurrence_term]
      rw [Finset.sum_range_succ', if_pos (Nat.zero_le r), Nat.sub_zero, Nat.sub_zero,
        ratioRecurrenceCoefficient_zero, one_mul]
      have h0 : |(uniformRatioPolynomial n).coeff r| ≤ Real.exp 1 * (8 * (n:ℝ) ^ 2) ^ r :=
        ih n (by omega) r
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        simp only [Finset.range_zero, Finset.sum_empty, zero_add]
        refine h0.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        apply pow_le_pow_left₀ (by positivity)
        push_cast; norm_num
      · have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
        have hn0 : (n:ℝ) ≠ 0 := by positivity
        obtain ⟨X0, hX0def⟩ : ∃ X0 : ℝ, X0 = 8 * (n:ℝ) ^ 2 := ⟨_, rfl⟩
        obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 1 / (12 * (n:ℝ)) := ⟨_, rfl⟩
        rw [← hX0def] at h0
        have hq0 : 0 ≤ q := by rw [hqdef]; positivity
        have hq1 : q ≤ 1/12 := by
          rw [hqdef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        have hX0pos : 0 < X0 := by rw [hX0def]; positivity
        -- termwise bound for the recurrence contributions
        have hterm : ∀ j ∈ range n, |(if j + 1 ≤ r then ratioRecurrenceCoefficient n (j+1) *
            (uniformRatioPolynomial (n - (j+1))).coeff (r - (j+1)) else 0)| ≤
            Real.exp 1 * X0 ^ r * q ^ (j+1) := by
          intro j hj
          have hjn : j + 1 ≤ n := Finset.mem_range.mp hj
          split_ifs with hjr
          · rw [abs_mul]
            have h1 := ratioRecurrenceCoefficient_sharp_bound n (j+1)
            have h2 := ih (n - (j+1)) (by omega) (r - (j+1))
            have h3 : (8 * ((n - (j+1) : ℕ) : ℝ) ^ 2) ^ (r - (j+1)) ≤ X0 ^ (r - (j+1)) := by
              apply pow_le_pow_left₀ (by positivity)
              have : ((n - (j+1) : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n (j+1)
              rw [hX0def]; nlinarith [Nat.cast_nonneg (α := ℝ) (n - (j+1))]
            have hX0 : X0 ^ r = X0 ^ (r - (j+1)) * X0 ^ (j+1) := by
              rw [← pow_add]; congr 1; omega
            have hq : (2 * (n:ℝ) / 3) ^ (j+1) = X0 ^ (j+1) * q ^ (j+1) := by
              rw [← mul_pow]; congr 1; rw [hX0def, hqdef]; field_simp <;> ring
            calc |ratioRecurrenceCoefficient n (j+1)| *
                  |(uniformRatioPolynomial (n - (j+1))).coeff (r - (j+1))|
                ≤ (2 * (n:ℝ) / 3) ^ (j+1) * (Real.exp 1 * X0 ^ (r - (j+1))) :=
                  mul_le_mul h1 (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
                    (abs_nonneg _) (by positivity)
              _ = Real.exp 1 * X0 ^ r * q ^ (j+1) := by rw [hX0, hq]; ring
          · rw [abs_zero]; positivity
        have hgeom : ∑ j ∈ range n, q ^ (j+1) ≤ q / (1 - q) :=
          finite_geometric_positive_tail_bound q n hq0 (by linarith)
        have hsum := Finset.sum_le_sum hterm
        rw [← Finset.mul_sum] at hsum
        have htri := Finset.abs_sum_le_sum_abs (fun j => if j + 1 ≤ r then
          ratioRecurrenceCoefficient n (j+1) *
            (uniformRatioPolynomial (n - (j+1))).coeff (r - (j+1)) else 0) (range n)
        rcases Nat.eq_zero_or_pos r with hr0 | hrpos
        · subst hr0
          have hz : ∀ j ∈ range n, (if j + 1 ≤ 0 then ratioRecurrenceCoefficient n (j+1) *
              (uniformRatioPolynomial (n - (j+1))).coeff (0 - (j+1)) else (0:ℝ)) = 0 :=
            fun j _ => by simp
          rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, zero_add]
          simpa using h0
        · have hgrow : X0 ^ r * (1 + q / (1 - q)) ≤ (8 * ((n+1:ℕ):ℝ) ^ 2) ^ r := by
            have hratio : (8 * ((n+1:ℕ):ℝ) ^ 2) = X0 * (1 + 1/(n:ℝ)) ^ 2 := by
              rw [hX0def]; push_cast; field_simp <;> ring
            rw [hratio, mul_pow, ← pow_mul]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have hb := one_add_mul_le_pow (show (-2:ℝ) ≤ 1/(n:ℝ) by
              have : (0:ℝ) ≤ 1/(n:ℝ) := by positivity
              linarith) (2 * r)
            push_cast at hb
            have ht0 : 0 < 1/(n:ℝ) := by positivity
            have ht1 : 1/(n:ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hn1
            have hqt : q = 1/(n:ℝ) / 12 := by rw [hqdef]; ring
            have hqq : q / (1 - q) ≤ 1/(n:ℝ) := by
              rw [div_le_iff₀ (by linarith), hqt]
              nlinarith [mul_nonneg ht0.le (show (0:ℝ) ≤ 11 - 1/(n:ℝ) by linarith)]
            have hr1 : (1:ℝ) ≤ 2 * r := by
              have : (1:ℝ) ≤ r := by exact_mod_cast hrpos
              linarith
            have hrn : 1/(n:ℝ) ≤ 2 * (r:ℝ) * (1/(n:ℝ)) := by
              nlinarith [mul_nonneg ht0.le (show (0:ℝ) ≤ 2 * r - 1 by linarith)]
            linarith
          calc |∑ j ∈ range n, (if j + 1 ≤ r then ratioRecurrenceCoefficient n (j+1) *
                (uniformRatioPolynomial (n - (j+1))).coeff (r - (j+1)) else 0) +
                (uniformRatioPolynomial n).coeff r|
              ≤ ∑ j ∈ range n, |(if j + 1 ≤ r then ratioRecurrenceCoefficient n (j+1) *
                (uniformRatioPolynomial (n - (j+1))).coeff (r - (j+1)) else 0)| +
                |(uniformRatioPolynomial n).coeff r| :=
                (abs_add_le _ _).trans (add_le_add_right htri _)
            _ ≤ Real.exp 1 * X0 ^ r * (q / (1 - q)) + Real.exp 1 * X0 ^ r := by
                have := mul_le_mul_of_nonneg_left hgeom (by positivity : (0:ℝ) ≤ Real.exp 1 * X0 ^ r)
                linarith
            _ = Real.exp 1 * (X0 ^ r * (1 + q / (1 - q))) := by ring
            _ ≤ Real.exp 1 * (8 * ((n+1:ℕ):ℝ) ^ 2) ^ r :=
                mul_le_mul_of_nonneg_left hgrow (by positivity)

/-- **`|q_r(k)| ≤ (r+1) e² (8k²)^r`** (eg:eq:majorant-q). -/
theorem uniformSquared_sharp_coefficient_bound (k r : ℕ) :
    |(uniformSquaredPolynomial k).coeff r| ≤ Real.exp 1 ^ 2 * (r + 1) * (8 * (k:ℝ) ^ 2) ^ r := by
  unfold uniformSquaredPolynomial
  rw [pow_two, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (uniformRatioPolynomial k).coeff i * (uniformRatioPolynomial k).coeff j) r]
  calc |∑ i ∈ range (r+1), (uniformRatioPolynomial k).coeff i * (uniformRatioPolynomial k).coeff (r - i)|
      ≤ ∑ i ∈ range (r+1), |(uniformRatioPolynomial k).coeff i * (uniformRatioPolynomial k).coeff (r - i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range (r+1), Real.exp 1 ^ 2 * (8 * (k:ℝ) ^ 2) ^ r := by
        apply Finset.sum_le_sum
        intro i hi
        have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [abs_mul]
        calc |(uniformRatioPolynomial k).coeff i| * |(uniformRatioPolynomial k).coeff (r - i)|
            ≤ (Real.exp 1 * (8 * (k:ℝ) ^ 2) ^ i) * (Real.exp 1 * (8 * (k:ℝ) ^ 2) ^ (r - i)) :=
              mul_le_mul (uniformRatio_sharp_coefficient_bound k i)
                (uniformRatio_sharp_coefficient_bound k (r - i)) (abs_nonneg _) (by positivity)
          _ = Real.exp 1 ^ 2 * (8 * (k:ℝ) ^ 2) ^ r := by
              rw [show (8 * (k:ℝ) ^ 2) ^ r = (8 * (k:ℝ) ^ 2) ^ i * (8 * (k:ℝ) ^ 2) ^ (r - i) by
                rw [← pow_add]; congr 1; omega]
              ring
    _ = Real.exp 1 ^ 2 * (r + 1) * (8 * (k:ℝ) ^ 2) ^ r := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- The printed constant `C^{(N)}_{t,R}` of (eg:eq:CN). -/
def printedNormConstant (t : ℝ) (R : ℕ) : ℝ :=
  ∑' k : ℕ, (if k = 0 then 0 else t ^ (2*k) *
    ((2*R+6) * Real.exp 1 ^ 2 * 8 ^ (R+1) * (k:ℝ) ^ (2*R+2) +
      (k:ℝ) ^ (3*(R+1)) * (1 + Real.exp 1 ^ 2 *
        ∑ r ∈ range (R+1), (r+1) * 8 ^ r * (k:ℝ) ^ (2*r))))

def printedTerm (t : ℝ) (R k : ℕ) : ℝ :=
  if k = 0 then 0 else t ^ (2*k) *
    ((2*R+6) * Real.exp 1 ^ 2 * 8 ^ (R+1) * (k:ℝ) ^ (2*R+2) +
      (k:ℝ) ^ (3*(R+1)) * (1 + Real.exp 1 ^ 2 *
        ∑ r ∈ range (R+1), (r+1) * 8 ^ r * (k:ℝ) ^ (2*r)))

theorem printedNormConstant_eq (t : ℝ) (R : ℕ) :
    printedNormConstant t R = ∑' k, printedTerm t R k := rfl

theorem printedTerm_nonneg (t : ℝ) (R k : ℕ) : 0 ≤ printedTerm t R k := by
  unfold printedTerm
  split_ifs
  · exact le_rfl
  · have : 0 ≤ t ^ (2*k) := by rw [pow_mul]; positivity
    positivity

theorem printedTerm_summable (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (R : ℕ) :
    Summable (printedTerm t R) := by
  have hs0 : 0 < t ^ 2 := by positivity
  have hs1 : t ^ 2 < 1 := by nlinarith
  -- dominate by a finite combination of `(k+1)^d (t^2)^k`
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = 3*(R+1) + 2*R + 2 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2*R+6) * Real.exp 1 ^ 2 * 8 ^ (R+1) + (1 + Real.exp 1 ^ 2 *
      ∑ r ∈ range (R+1), ((r:ℝ)+1) * 8 ^ r) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hg := (shifted_power_geometric_summable (t^2) hs0 hs1 d).mul_left K
  refine Summable.of_nonneg_of_le (fun k => printedTerm_nonneg t R k) (fun k => ?_) hg
  unfold printedTerm
  split_ifs with hk
  · exact mul_nonneg hK0 (by positivity)
  · have hk1 : (1:ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have hkk : (k:ℝ) ≤ k + 1 := by linarith
    have hpow : ∀ a : ℕ, a ≤ d → (k:ℝ) ^ a ≤ ((k:ℝ) + 1) ^ d := by
      intro a ha
      calc (k:ℝ) ^ a ≤ (k:ℝ) ^ d := pow_le_pow_right₀ hk1 ha
        _ ≤ ((k:ℝ) + 1) ^ d := pow_le_pow_left₀ (by positivity) hkk d
    have hts : t ^ (2*k) = (t^2) ^ k := by rw [pow_mul]
    rw [hts]
    have h1 := hpow (2*R+2) (by omega)
    have h2 := hpow (3*(R+1)) (by omega)
    have hsum : ∑ r ∈ range (R+1), (r+1) * 8 ^ r * (k:ℝ) ^ (2*r) ≤
        (∑ r ∈ range (R+1), ((r:ℝ)+1) * 8 ^ r) * ((k:ℝ) ^ (2*R)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum; intro r hr
      have : (k:ℝ) ^ (2*r) ≤ (k:ℝ) ^ (2*R) :=
        pow_le_pow_right₀ hk1 (by have := Finset.mem_range.mp hr; omega)
      have : 0 ≤ ((r:ℝ)+1) * 8 ^ r := by positivity
      nlinarith
    have hkR : (k:ℝ) ^ (3*(R+1)) * (k:ℝ) ^ (2*R) ≤ ((k:ℝ) + 1) ^ d := by
      rw [← pow_add]; exact hpow _ (by omega)
    have hS0 : 0 ≤ ∑ r ∈ range (R+1), ((r:ℝ)+1) * 8 ^ r := Finset.sum_nonneg (fun r _ => by positivity)
    have hE : 0 ≤ Real.exp 1 ^ 2 := by positivity
    have hk0 : 0 ≤ (k:ℝ) ^ (3*(R+1)) := by positivity
    have hpk : 0 ≤ (t^2) ^ k := by positivity
    have hk2R : (1:ℝ) ≤ (k:ℝ) ^ (2*R) := one_le_pow₀ hk1
    have hinner : (2*R+6) * Real.exp 1 ^ 2 * 8 ^ (R+1) * (k:ℝ) ^ (2*R+2) +
        (k:ℝ) ^ (3*(R+1)) * (1 + Real.exp 1 ^ 2 * ∑ r ∈ range (R+1), (r+1) * 8 ^ r * (k:ℝ) ^ (2*r)) ≤
        K * ((k:ℝ) + 1) ^ d := by
      rw [hK]
      have hA : 0 ≤ (2*(R:ℝ)+6) * Real.exp 1 ^ 2 * 8 ^ (R+1) := by positivity
      have e1 : (2*R+6) * Real.exp 1 ^ 2 * 8 ^ (R+1) * (k:ℝ) ^ (2*R+2) ≤
          (2*R+6) * Real.exp 1 ^ 2 * 8 ^ (R+1) * ((k:ℝ) + 1) ^ d := mul_le_mul_of_nonneg_left h1 hA
      have e2 : (k:ℝ) ^ (3*(R+1)) * (1 + Real.exp 1 ^ 2 * ∑ r ∈ range (R+1), (r+1) * 8 ^ r * (k:ℝ) ^ (2*r)) ≤
          (1 + Real.exp 1 ^ 2 * ∑ r ∈ range (R+1), ((r:ℝ)+1) * 8 ^ r) * ((k:ℝ) + 1) ^ d := by
        have hA' : 1 + Real.exp 1 ^ 2 * ∑ r ∈ range (R+1), (r+1) * 8 ^ r * (k:ℝ) ^ (2*r) ≤
            (k:ℝ) ^ (2*R) * (1 + Real.exp 1 ^ 2 * ∑ r ∈ range (R+1), ((r:ℝ)+1) * 8 ^ r) := by
          have := mul_le_mul_of_nonneg_left hsum hE
          nlinarith [this, hk2R, mul_nonneg hE hS0]
        have : (k:ℝ) ^ (3*(R+1)) * (1 + Real.exp 1 ^ 2 * ∑ r ∈ range (R+1), (r+1) * 8 ^ r * (k:ℝ) ^ (2*r)) ≤
            (k:ℝ) ^ (3*(R+1)) * (k:ℝ) ^ (2*R) *
              (1 + Real.exp 1 ^ 2 * ∑ r ∈ range (R+1), ((r:ℝ)+1) * 8 ^ r) := by
          calc _ ≤ (k:ℝ) ^ (3*(R+1)) * ((k:ℝ) ^ (2*R) *
                (1 + Real.exp 1 ^ 2 * ∑ r ∈ range (R+1), ((r:ℝ)+1) * 8 ^ r)) :=
                mul_le_mul_of_nonneg_left hA' hk0
            _ = _ := by ring
        refine this.trans ?_
        rw [mul_comm ((1:ℝ) + _)]
        exact mul_le_mul_of_nonneg_right hkR (by linarith [mul_nonneg hE hS0])
      linarith [e1, e2]
    calc (t^2) ^ k * ((2*R+6) * Real.exp 1 ^ 2 * 8 ^ (R+1) * (k:ℝ) ^ (2*R+2) +
          (k:ℝ) ^ (3*(R+1)) * (1 + Real.exp 1 ^ 2 * ∑ r ∈ range (R+1), (r+1) * 8 ^ r * (k:ℝ) ^ (2*r)))
        ≤ (t^2) ^ k * (K * ((k:ℝ) + 1) ^ d) := mul_le_mul_of_nonneg_left hinner hpk
      _ = K * (((k:ℝ) + 1) ^ d * (t^2) ^ k) := by ring

set_option maxHeartbeats 1000000 in
/-- **Theorem (eg:eq:allnorm) with the printed constant (eg:eq:CN)**: for `0 < t < 1`,
`R ≥ 0` and `M ≥ 4096`, `|N - ∑_{r ≤ R} A_r(t) M^{-r}| ≤ C^{(N)}_{t,R} M^{-R-1}`. -/
theorem printed_all_order_norm_remainder (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (R M : ℕ)
    (hM : 4096 ≤ M) :
    |uniformNormSeries M t - ∑ r ∈ range (R+1), uniformNormCoefficient t r / (M:ℝ) ^ r| ≤
      printedNormConstant t R / (M:ℝ) ^ (R+1) := by
  have hM0 : M ≠ 0 := by omega
  have hMr : (4096:ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0:ℝ) < M := by linarith
  set h : ℝ := 1 / (M:ℝ)
  have hh : 0 ≤ h := by positivity
  have hh1 : h ≤ 1 := by simp only [h]; rw [div_le_one hMpos]; linarith
  set w := binomialWeight t
  set P := uniformSquaredPolynomial
  set E : ℕ → ℝ := fun k => (P k).eval h - ∑ r ∈ range (R+1), (P k).coeff r * h ^ r
  have hNs : Summable (fun k => w k * (P k).eval h) := by
    have := uniformNormSeries_summable M hM0 t ht0 ht1
    refine this.congr (fun k => ?_)
    simp only [w, P, h]; rw [uniformSquaredPolynomial_value M k hM0]
  have hAs : ∀ r, Summable (fun k => w k * (P k).coeff r) := fun r =>
    (uniformNormCoefficient_absolute_summability t ht0 ht1 r).of_abs
  have hN : uniformNormSeries M t = ∑' k, w k * (P k).eval h := by
    unfold uniformNormSeries
    apply tsum_congr; intro k
    simp only [w, P, h]; rw [uniformSquaredPolynomial_value M k hM0]
  have hA : ∑ r ∈ range (R+1), uniformNormCoefficient t r / (M:ℝ) ^ r =
      ∑' k, w k * ∑ r ∈ range (R+1), (P k).coeff r * h ^ r := by
    unfold uniformNormCoefficient
    simp_rw [Finset.mul_sum]
    rw [Summable.tsum_finsetSum (fun r _ => ((hAs r).mul_right (h ^ r)).congr (fun k => by ring))]
    apply Finset.sum_congr rfl; intro r _
    rw [div_eq_mul_inv, ← tsum_mul_right]
    apply tsum_congr; intro k
    simp only [h, one_div_pow, w, P]; ring
  have hAs' : Summable (fun k => w k * ∑ r ∈ range (R+1), (P k).coeff r * h ^ r) := by
    simp_rw [Finset.mul_sum]
    exact summable_sum (fun r _ => ((hAs r).mul_right (h ^ r)).congr (fun k => by ring))
  rw [hN, hA, ← hNs.tsum_sub hAs']
  have hpt : ∀ k, |w k * (P k).eval h - w k * ∑ r ∈ range (R+1), (P k).coeff r * h ^ r| ≤
      printedTerm t R k / (M:ℝ) ^ (R+1) := by
    intro k
    rw [← mul_sub, abs_mul, abs_of_nonneg (binomialWeight_nonneg t k)]
    have hw : w k ≤ t ^ (2*k) := by
      have := binomialWeight_le_geometric t k; rw [← pow_mul] at this; exact this
    unfold printedTerm
    split_ifs with hk
    · subst hk
      have : (P 0).eval h - ∑ r ∈ range (R+1), (P 0).coeff r * h ^ r = 0 := by
        simp only [P, uniformSquaredPolynomial, uniformRatioPolynomial_zero, one_pow,
          Polynomial.eval_one, Polynomial.coeff_one]
        rw [Finset.sum_eq_single 0 (fun r _ hr => by simp [hr]) (by simp)]
        simp
      rw [this]; simp
    · have hk1 : (1:ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      have hcoeff : ∀ r, |(P k).coeff r| ≤ Real.exp 1 ^ 2 * (r+1) * (8 * (k:ℝ) ^ 2) ^ r :=
        fun r => uniformSquared_sharp_coefficient_bound k r
      set T1 := (2*R+6) * Real.exp 1 ^ 2 * 8 ^ (R+1) * (k:ℝ) ^ (2*R+2)
      set T2 := (k:ℝ) ^ (3*(R+1)) * (1 + Real.exp 1 ^ 2 *
        ∑ r ∈ range (R+1), (r+1) * 8 ^ r * (k:ℝ) ^ (2*r))
      have hT1 : 0 ≤ T1 := by positivity
      have hT2 : 0 ≤ T2 := by positivity
      have hEk : |(P k).eval h - ∑ r ∈ range (R+1), (P k).coeff r * h ^ r| ≤
          (T1 + T2) / (M:ℝ) ^ (R+1) := by
        by_cases hsmall : (k:ℝ) ^ 3 ≤ M
        · have hg := polynomial_geometric_remainder (P k) (Real.exp 1 ^ 2) (8 * (k:ℝ) ^ 2) h R
            (by positivity) (by positivity) hh (small_index_scale M k hMr (by positivity) hsmall)
            hcoeff
          have : Real.exp 1 ^ 2 * (2*R+6) * (8 * (k:ℝ) ^ 2 * h) ^ (R+1) = T1 / (M:ℝ) ^ (R+1) := by
            simp only [T1, h]
            rw [show (8 * (k:ℝ) ^ 2 * (1 / (M:ℝ))) = 8 * (k:ℝ) ^ 2 / M by ring, div_pow, mul_pow,
              ← pow_mul]
            ring_nf
          rw [this] at hg
          calc _ ≤ T1 / (M:ℝ) ^ (R+1) := hg
            _ ≤ (T1 + T2) / (M:ℝ) ^ (R+1) := div_le_div_of_nonneg_right (by linarith) (by positivity)
        · push_neg at hsmall
          have hl := polynomial_large_remainder (P k) (Real.exp 1 ^ 2) (8 * (k:ℝ) ^ 2) h R
            (by positivity) (by positivity) hh hh1 (uniformSquaredPolynomial_value_bound M k hM0) hcoeff
          have hone : (1:ℝ) ≤ (k:ℝ) ^ (3*(R+1)) / (M:ℝ) ^ (R+1) := by
            rw [le_div_iff₀ (by positivity), one_mul, pow_mul]
            exact pow_le_pow_left₀ hMpos.le hsmall.le _
          have hsum_eq : 1 + ∑ r ∈ range (R+1), Real.exp 1 ^ 2 * (r+1) * (8 * (k:ℝ) ^ 2) ^ r =
              1 + Real.exp 1 ^ 2 * ∑ r ∈ range (R+1), (r+1) * 8 ^ r * (k:ℝ) ^ (2*r) := by
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro r _
            rw [mul_pow, ← pow_mul]; ring
          rw [hsum_eq] at hl
          have hpos : 0 ≤ 1 + Real.exp 1 ^ 2 * ∑ r ∈ range (R+1), (r+1) * 8 ^ r * (k:ℝ) ^ (2*r) := by
            positivity
          calc _ ≤ 1 + Real.exp 1 ^ 2 * ∑ r ∈ range (R+1), (r+1) * 8 ^ r * (k:ℝ) ^ (2*r) := hl
            _ ≤ (k:ℝ) ^ (3*(R+1)) / (M:ℝ) ^ (R+1) *
                (1 + Real.exp 1 ^ 2 * ∑ r ∈ range (R+1), (r+1) * 8 ^ r * (k:ℝ) ^ (2*r)) := by
                nlinarith
            _ = T2 / (M:ℝ) ^ (R+1) := by simp only [T2]; ring
            _ ≤ (T1 + T2) / (M:ℝ) ^ (R+1) := div_le_div_of_nonneg_right (by linarith) (by positivity)
      calc w k * |(P k).eval h - ∑ r ∈ range (R+1), (P k).coeff r * h ^ r|
          ≤ t ^ (2*k) * ((T1 + T2) / (M:ℝ) ^ (R+1)) :=
            mul_le_mul hw hEk (abs_nonneg _) (by rw [pow_mul]; positivity)
        _ = t ^ (2*k) * (T1 + T2) / (M:ℝ) ^ (R+1) := by ring
  have hsumB := (printedTerm_summable t ht0 ht1 R).div_const ((M:ℝ) ^ (R+1))
  calc |∑' k, (w k * (P k).eval h - w k * ∑ r ∈ range (R+1), (P k).coeff r * h ^ r)|
      ≤ ∑' k, |w k * (P k).eval h - w k * ∑ r ∈ range (R+1), (P k).coeff r * h ^ r| := by
        have hs := (hNs.sub hAs').abs
        have hn : Summable (fun k => ‖w k * (P k).eval h -
            w k * ∑ r ∈ range (R+1), (P k).coeff r * h ^ r‖) := by
          simpa only [Real.norm_eq_abs] using hs
        have := norm_tsum_le_tsum_norm hn
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' k, printedTerm t R k / (M:ℝ) ^ (R+1) :=
        Summable.tsum_le_tsum hpt (hNs.sub hAs').abs hsumB
    _ = printedNormConstant t R / (M:ℝ) ^ (R+1) := by rw [tsum_div_const, printedNormConstant_eq]

end EulerianGrothendieck
