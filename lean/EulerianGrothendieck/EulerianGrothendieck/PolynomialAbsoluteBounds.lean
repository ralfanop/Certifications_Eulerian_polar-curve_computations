import EulerianGrothendieck.SummationRemainder

/-! Elementary absolute-coefficient bounds for polynomials, expressed as finite
supported sums. No complex-analytic estimates are used. -/
noncomputable section
open scoped BigOperators
open Polynomial Finset
namespace EulerianGrothendieck

def polyAbsEval (p : ℝ[X]) (h : ℝ) : ℝ := ∑' r : ℕ, |p.coeff r| * h^r

theorem polyAbsEval_summable (p : ℝ[X]) (h : ℝ) :
    Summable (fun r : ℕ => |p.coeff r| * h^r) := by
  apply summable_of_ne_finset_zero (s := p.support)
  intro r hr
  rw [Polynomial.not_mem_support_iff.mp hr]
  simp

theorem polyAbsEval_nonneg (p : ℝ[X]) (h : ℝ) (hh : 0 ≤ h) :
    0 ≤ polyAbsEval p h := tsum_nonneg (fun r => mul_nonneg (abs_nonneg _) (pow_nonneg hh _))

theorem coeff_mul_pow_le_polyAbsEval (p : ℝ[X]) (h : ℝ) (hh : 0 ≤ h) (r : ℕ) :
    |p.coeff r| * h^r ≤ polyAbsEval p h :=
  (polyAbsEval_summable p h).le_tsum r (fun i hi => by positivity)

theorem polyAbsEval_C (a h : ℝ) : polyAbsEval (C a) h = |a| := by
  unfold polyAbsEval
  rw [tsum_eq_single 0]
  · simp
  · intro r hr
    simp [Polynomial.coeff_C, hr]

theorem polyAbsEval_one (h : ℝ) : polyAbsEval 1 h = 1 := by
  simpa using polyAbsEval_C 1 h

theorem polyAbsEval_C_mul (a : ℝ) (p : ℝ[X]) (h : ℝ) :
    polyAbsEval (C a*p) h = |a| * polyAbsEval p h := by
  unfold polyAbsEval
  simp only [Polynomial.coeff_C_mul, abs_mul, mul_assoc]
  exact (polyAbsEval_summable p h).tsum_mul_left |a|

theorem polyAbsEval_X_pow_mul (p : ℝ[X]) (j : ℕ) (h : ℝ) :
    polyAbsEval (X^j*p) h = h^j*polyAbsEval p h := by
  have hs := (polyAbsEval_summable (X^j*p) h).sum_add_tsum_nat_add j
  have hz : (∑ r ∈ range j, |(X^j*p).coeff r| * h^r) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [Polynomial.coeff_X_pow_mul', if_neg (by have := Finset.mem_range.mp hr; omega)]
    simp
  rw [hz, zero_add] at hs
  change (∑' r : ℕ, |(X^j*p).coeff r| * h^r) = _
  rw [← hs]
  simp only [Polynomial.coeff_X_pow_mul, pow_add]
  calc
    (∑' r : ℕ, |p.coeff r| * (h^r*h^j)) = ∑' r : ℕ, h^j*(|p.coeff r| * h^r) := by
      apply tsum_congr; intro r; ring
    _ = h^j*polyAbsEval p h := (polyAbsEval_summable p h).tsum_mul_left (h^j)

theorem polyAbsEval_sum_le {ι : Type*} (s : Finset ι) (P : ι → ℝ[X])
    (h : ℝ) (hh : 0 ≤ h) :
    polyAbsEval (∑ i ∈ s, P i) h ≤ ∑ i ∈ s, polyAbsEval (P i) h := by
  have hs : Summable (fun r : ℕ => ∑ i ∈ s, |(P i).coeff r| * h^r) :=
    summable_sum (fun i hi => polyAbsEval_summable (P i) h)
  calc
    _ ≤ ∑' r : ℕ, ∑ i ∈ s, |(P i).coeff r| * h^r := by
      apply Summable.tsum_le_tsum _ (polyAbsEval_summable _ h) hs
      intro r
      rw [Polynomial.finset_sum_coeff, ← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (pow_nonneg hh r)
    _ = ∑ i ∈ s, polyAbsEval (P i) h :=
      Summable.tsum_finsetSum (fun i hi => polyAbsEval_summable (P i) h)

theorem polyAbsEval_coeff_bound (p : ℝ[X]) (H : ℝ) (hH : 0 < H)
    (hp : polyAbsEval p (1/H) ≤ 2) (r : ℕ) : |p.coeff r| ≤ 2*H^r := by
  have h := (coeff_mul_pow_le_polyAbsEval p (1/H) (by positivity) r).trans hp
  rw [one_div_pow, mul_one_div] at h
  exact (div_le_iff₀ (pow_pos hH r)).1 h

end EulerianGrothendieck
