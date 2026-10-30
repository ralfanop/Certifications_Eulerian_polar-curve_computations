import EulerianGrothendieck.Remainder
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped BigOperators
namespace EulerianGrothendieck

def coeffConv (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), a i * b (n-i)

theorem coeffConv_nonneg (a b : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (n : ℕ) :
    0 ≤ coeffConv a b n := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (hb (n-i)))

theorem coeffConv_mono (a b A B : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hA : ∀ i, a i ≤ A i) (hB : ∀ i, b i ≤ B i) (n : ℕ) :
    coeffConv a b n ≤ coeffConv A B n := by
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul (hA i) (hB (n-i)) (hb (n-i)) (le_trans (ha i) (hA i))

def coeffPower (a : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun n => if n=0 then 1 else 0
  | m+1 => coeffConv a (coeffPower a m)

theorem coeffPower_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (m n : ℕ) :
    0 ≤ coeffPower a m n := by
  induction m generalizing n with
  | zero => simp [coeffPower]; split_ifs <;> norm_num
  | succ m ih => exact coeffConv_nonneg a (coeffPower a m) ha ih n

theorem coeffPower_mono (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (h : ∀ n, a n ≤ b n) (m n : ℕ) :
    coeffPower a m n ≤ coeffPower b m n := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    exact coeffConv_mono a (coeffPower a m) b (coeffPower b m)
      ha (coeffPower_nonneg a ha m) h ih n

theorem coefficient_rescaling_mono (a b : ℕ → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (h : ∀ n, a n ≤ b n) (n : ℕ) :
    a n * c^n ≤ b n * c^n := mul_le_mul_of_nonneg_right (h n) (pow_nonneg hc n)

/-- The exact coefficient condition for a reciprocal series, at every positive degree. -/
theorem reciprocal_coefficient_rule (b d : ℕ → ℚ) (n : ℕ)
    (hb : b 0 = 1) :
    (∑ i ∈ Finset.range (n+2), b i*d (n+1-i)) = 0 ↔
    d (n+1) = -(∑ j ∈ Finset.range (n+1), b (j+1)*d (n-j)) := by
  rw [Finset.sum_range_succ']
  simp only [hb, one_mul, Nat.sub_zero, Nat.add_sub_add_right]
  constructor <;> intro h <;> linarith

theorem convolution_coefficient_bound (g : ℕ → ℝ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hg : ∀ j, |g j| ≤ A*B^j) (r : ℕ) :
    |coeffConv g g r| ≤ (r+1)*A^2*B^r := by
  calc
    |coeffConv g g r| ≤ ∑ j ∈ Finset.range (r+1), |g j*g (r-j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (r+1), A^2*B^r := by
      apply Finset.sum_le_sum
      intro j hj
      have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      calc
        |g j*g (r-j)| = |g j| * |g (r-j)| := abs_mul _ _
        _ ≤ (A*B^j)*(A*B^(r-j)) :=
          mul_le_mul (hg j) (hg (r-j)) (abs_nonneg _) (mul_nonneg hA (pow_nonneg hB j))
        _ = A^2*B^r := by
          rw [show (A*B^j)*(A*B^(r-j)) = A^2*(B^j*B^(r-j)) by ring,
            ← pow_add, Nat.add_sub_of_le hjr]
    _ = (r+1)*A^2*B^r := by simp; ring

theorem geometric_tail_factor_bound (R s : ℝ) (hR : 0 ≤ R)
    (hs : 0 ≤ s) (hs2 : s ≤ 1/2) :
    (R+2)/(1-s) + s/(1-s)^2 ≤ 2*R+6 := by
  have hd : 0 < 1-s := by linarith
  have hd2 : 0 < (1-s)^2 := sq_pos_of_pos hd
  have h1 : (R+2)/(1-s) ≤ 2*(R+2) := by
    apply (div_le_iff₀ hd).2
    nlinarith
  have h2 : s/(1-s)^2 ≤ 2 := by
    apply (div_le_iff₀ hd2).2
    nlinarith [sq_nonneg (s-1/2)]
  linarith

/-- Quantitative reciprocal transfer; B and D can be arbitrary finite expansions.
The actual probability/moment remainder is NOT assumed proved by this lemma. -/
theorem reciprocal_remainder_transfer (N B D C T S η h : ℝ) (r : ℕ)
    (hη : 0 < η) (hN : η ≤ N) (hh : 0 ≤ h)
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hNB : |N-B| ≤ C*h^r) (hBD : |1-B*D| ≤ T*h^r) (hD : |D| ≤ S) :
    |1/N-D| ≤ (T+C*S)/η*h^r := by
  have hN0 : 0 < N := lt_of_lt_of_le hη hN
  have hres : |1-N*D| ≤ (T+C*S)*h^r := by
    calc
      |1-N*D| = |(1-B*D)-(N-B)*D| := by congr 1; ring
      _ ≤ |1-B*D|+|(N-B)*D| := abs_sub _ _
      _ ≤ T*h^r+(C*h^r)*S := by
        rw [abs_mul]
        exact add_le_add hBD (mul_le_mul hNB hD (abs_nonneg _) (mul_nonneg hC (pow_nonneg hh r)))
      _ = (T+C*S)*h^r := by ring
  rw [show 1/N-D = (1-N*D)/N by field_simp <;> ring, abs_div,
    abs_of_pos hN0]
  apply (div_le_iff₀ hN0).2
  calc
    |1-N*D| ≤ (T+C*S)*h^r := hres
    _ = ((T+C*S)/η*h^r)*η := by field_simp <;> ring
    _ ≤ ((T+C*S)/η*h^r)*N := mul_le_mul_of_nonneg_left hN (by positivity)

theorem arcsin_disk_realpart_bound (x y : ℝ)
    (h : x^2+(y-1)^2 ≤ 1/4) :
    5/4+2*(y-1/2)^2 ≤ 1-x^2+y^2 := by nlinarith

theorem lipschitz_scale_square : (2/Real.sqrt 5)^2 = (4/5 : ℝ) := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
  norm_num

end EulerianGrothendieck
