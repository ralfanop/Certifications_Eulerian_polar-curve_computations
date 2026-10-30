import EulerianGrothendieck.FiniteSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Quantitative finite-order remainders for polynomial families under a
geometric summation weight. The coefficient bounds are explicit hypotheses;
no asymptotic remainder is assumed. -/
noncomputable section
open scoped BigOperators
open Polynomial Finset
namespace EulerianGrothendieck

theorem polynomial_evaluation_hasSum (p : ℝ[X]) (h : ℝ) :
    HasSum (fun r : ℕ => p.coeff r*h^r) (p.eval h) := by
  rw [Polynomial.eval_eq_sum_range]
  apply hasSum_sum_of_ne_finset_zero
  intro r hr
  have hdeg : p.natDegree < r := by
    simp only [Finset.mem_range, not_lt] at hr
    omega
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, zero_mul]

theorem shifted_linear_geometric_hasSum (s : ℝ) (R : ℕ)
    (hs : |s| < 1) :
    HasSum (fun n : ℕ => (n+R+2:ℝ)*s^n)
      (s/(1-s)^2+(R+2:ℝ)/(1-s)) := by
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (show ‖s‖ < 1 from hs)
  have h2 := (hasSum_geometric_of_abs_lt_one hs).mul_left (R+2:ℝ)
  convert h1.add h2 using 1
  · ext n
    ring

theorem polynomial_geometric_remainder (p : ℝ[X]) (A B h : ℝ) (R : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h) (hsmall : B*h ≤ 1/2)
    (hcoeff : ∀ r, |p.coeff r| ≤ A*(r+1)*B^r) :
    |p.eval h - ∑ r ∈ range (R+1), p.coeff r*h^r| ≤
      A*(2*R+6)*(B*h)^(R+1) := by
  let s := B*h
  have hs0 : 0 ≤ s := mul_nonneg hB hh
  have hs1 : |s| < 1 := by rw [abs_of_nonneg hs0]; dsimp [s]; linarith
  have hsum := (polynomial_evaluation_hasSum p h).summable.sum_add_tsum_nat_add (R+1)
  rw [(polynomial_evaluation_hasSum p h).tsum_eq] at hsum
  have htail : p.eval h - ∑ r ∈ range (R+1), p.coeff r*h^r =
      ∑' n : ℕ, p.coeff (n+(R+1))*h^(n+(R+1)) := by linarith
  rw [htail]
  have hbound : ∀ n : ℕ,
      ‖p.coeff (n+(R+1))*h^(n+(R+1))‖ ≤
        (A*s^(R+1))*((n+R+2:ℝ)*s^n) := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hh _)]
    calc
      |p.coeff (n+(R+1))| * h^(n+(R+1)) ≤
          (A*((n+(R+1):ℕ)+1)*B^(n+(R+1)))*h^(n+(R+1)) :=
        mul_le_mul_of_nonneg_right (hcoeff _) (pow_nonneg hh _)
      _ = (A*s^(R+1))*((n+R+2:ℝ)*s^n) := by
        dsimp [s]
        push_cast
        rw [pow_add, mul_pow, mul_pow]
        ring
  have H := tsum_of_norm_bounded
    ((shifted_linear_geometric_hasSum s R hs1).mul_left (A*s^(R+1))) hbound
  rw [Real.norm_eq_abs] at H
  calc
    |∑' n : ℕ, p.coeff (n+(R+1))*h^(n+(R+1))| ≤
        (A*s^(R+1))*(s/(1-s)^2+(R+2:ℝ)/(1-s)) := H
    _ ≤ (A*s^(R+1))*(2*R+6) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA (pow_nonneg hs0 _))
      simpa [add_comm] using geometric_tail_factor_bound (R:ℝ) s (by positivity) hs0 hsmall
    _ = A*(2*R+6)*(B*h)^(R+1) := by dsimp [s]; ring

theorem polynomial_large_remainder (p : ℝ[X]) (A B h : ℝ) (R : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hp : |p.eval h| ≤ 1) (hcoeff : ∀ r, |p.coeff r| ≤ A*(r+1)*B^r) :
    |p.eval h - ∑ r ∈ range (R+1), p.coeff r*h^r| ≤
      1 + ∑ r ∈ range (R+1), A*(r+1)*B^r := by
  calc
    |p.eval h - ∑ r ∈ range (R+1), p.coeff r*h^r| ≤
        |p.eval h| + |∑ r ∈ range (R+1), p.coeff r*h^r| := abs_sub _ _
    _ ≤ 1 + ∑ r ∈ range (R+1), |p.coeff r*h^r| :=
      add_le_add hp (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 1 + ∑ r ∈ range (R+1), A*(r+1)*B^r := by
      apply add_le_add_left
      apply Finset.sum_le_sum
      intro r hr
      rw [abs_mul, abs_of_nonneg (pow_nonneg hh _)]
      exact (mul_le_mul_of_nonneg_right (hcoeff r) (pow_nonneg hh r)).trans
        (mul_le_of_le_one_right (by positivity) (pow_le_one₀ hh hh1))

theorem small_index_scale (M k : ℝ) (hM : 4096 ≤ M) (hk : 0 ≤ k)
    (hsmall : k^3 ≤ M) : 8*k^2*(1/M) ≤ 1/2 := by
  have hM0 : 0 < M := by linarith
  have h : 16*k^2 ≤ M := by
    by_cases h16 : k ≤ 16
    · nlinarith
    · have h16' : 16 ≤ k := le_of_lt (lt_of_not_ge h16)
      have := mul_le_mul_of_nonneg_right h16' (sq_nonneg k)
      nlinarith
  rw [mul_one_div]
  apply (div_le_iff₀ hM0).2
  linarith

/-- A bound valid on the entire interval [0,1], including indices for which
B*h is too large for the local geometric estimate. -/
def remainderMajorant (A B : ℝ) (R : ℕ) : ℝ :=
  A*(2*R+6)*B^(R+1) +
  (2*B)^(R+1)*(1+∑ r ∈ range (R+1), A*(r+1)*B^r)

theorem remainderMajorant_nonneg (A B : ℝ) (R : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ remainderMajorant A B R := by
  unfold remainderMajorant
  positivity

theorem polynomial_global_remainder (p : ℝ[X]) (A B h : ℝ) (R : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hp : |p.eval h| ≤ 1) (hcoeff : ∀ r, |p.coeff r| ≤ A*(r+1)*B^r) :
    |p.eval h - ∑ r ∈ range (R+1), p.coeff r*h^r| ≤
      remainderMajorant A B R * h^(R+1) := by
  have hc : 0 ≤ 1+∑ r ∈ range (R+1), A*(r+1)*B^r := by positivity
  by_cases hs : B*h ≤ 1/2
  · calc
      _ ≤ A*(2*R+6)*(B*h)^(R+1) :=
        polynomial_geometric_remainder p A B h R hA hB hh hs hcoeff
      _ = (A*(2*R+6)*B^(R+1))*h^(R+1) := by rw [mul_pow]; ring
      _ ≤ remainderMajorant A B R*h^(R+1) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hh _)
        unfold remainderMajorant
        have : 0 ≤ (2*B)^(R+1)*(1+∑ r ∈ range (R+1), A*(r+1)*B^r) := by positivity
        linarith
  · have hs' : 1 ≤ 2*B*h := by linarith
    have hpow : 1 ≤ (2*B*h)^(R+1) := one_le_pow₀ hs'
    calc
      _ ≤ 1+∑ r ∈ range (R+1), A*(r+1)*B^r :=
        polynomial_large_remainder p A B h R hA hB hh hh1 hp hcoeff
      _ ≤ (2*B*h)^(R+1)*(1+∑ r ∈ range (R+1), A*(r+1)*B^r) :=
        le_mul_of_one_le_left hc hpow
      _ = ((2*B)^(R+1)*(1+∑ r ∈ range (R+1), A*(r+1)*B^r))*h^(R+1) := by
        rw [mul_pow]; ring
      _ ≤ remainderMajorant A B R*h^(R+1) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hh _)
        unfold remainderMajorant
        have : 0 ≤ A*(2*R+6)*B^(R+1) := by positivity
        linarith

/-- Passing the quantitative remainder through an infinite weighted sum.
The assumptions contain coefficient majorants and summability, never the
asymptotic conclusion. -/
theorem weighted_polynomial_remainder (P : ℕ → ℝ[X]) (w B : ℕ → ℝ)
    (A h : ℝ) (R : ℕ) (hA : 0 ≤ A) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hw : ∀ k, 0 ≤ w k) (hB : ∀ k, 0 ≤ B k)
    (hvalues : ∀ k, |(P k).eval h| ≤ 1)
    (hcoeff : ∀ k r, |(P k).coeff r| ≤ A*(r+1)*(B k)^r)
    (hwSum : Summable w)
    (hcoeffSum : ∀ r, Summable (fun k => w k*((P k).coeff r)))
    (hmajorant : Summable (fun k => w k*remainderMajorant A (B k) R)) :
    |(∑' k, w k*(P k).eval h) -
      ∑ r ∈ range (R+1), (∑' k, w k*((P k).coeff r))*h^r| ≤
      (∑' k, w k*remainderMajorant A (B k) R)*h^(R+1) := by
  have hv : Summable (fun k => w k*(P k).eval h) :=
    hwSum.of_norm_bounded (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw k)]
      exact mul_le_of_le_one_right (hw k) (hvalues k))
  have ht : Summable (fun k => ∑ r ∈ range (R+1), w k*(P k).coeff r*h^r) := by
    apply summable_sum
    intro r hr
    exact (hcoeffSum r).mul_right (h^r)
  have heq : (∑' k, ∑ r ∈ range (R+1), w k*(P k).coeff r*h^r) =
      ∑ r ∈ range (R+1), (∑' k, w k*(P k).coeff r)*h^r := by
    rw [Summable.tsum_finsetSum (fun r hr => (hcoeffSum r).mul_right (h^r))]
    apply Finset.sum_congr rfl
    intro r hr
    exact (hcoeffSum r).tsum_mul_right (h^r)
  rw [← heq, ← hv.tsum_sub ht]
  have hb : ∀ k, ‖w k*(P k).eval h -
      ∑ r ∈ range (R+1), w k*(P k).coeff r*h^r‖ ≤
      (w k*remainderMajorant A (B k) R)*h^(R+1) := by
    intro k
    rw [show (∑ r ∈ range (R+1), w k*(P k).coeff r*h^r) =
      w k*∑ r ∈ range (R+1), (P k).coeff r*h^r by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r hr; ring]
    rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw k)]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left
      (polynomial_global_remainder (P k) A (B k) h R hA (hB k) hh hh1
        (hvalues k) (hcoeff k)) (hw k)
  simpa only [Real.norm_eq_abs] using
    tsum_of_norm_bounded (hmajorant.hasSum.mul_right (h^(R+1))) hb

end EulerianGrothendieck
