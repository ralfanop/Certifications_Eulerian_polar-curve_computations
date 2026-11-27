import Mathlib

noncomputable section
open Finset
namespace M12RecurrenceAllOrder

/-- Literal Taylor coefficient of the bond at displacement m, equation (197).
The jets are indexed by coefficient number and derivative order. -/
def localBond (jet : ℕ → ℕ → ℝ) (q : ℕ) (m : ℤ) : ℝ :=
  ∑ k ∈ range (q+1), (m:ℝ)^(q-k) / (Nat.factorial (q-k):ℝ) * jet k (q-k)

theorem localBond_zero (jet : ℕ → ℕ → ℝ) (m : ℤ) :
    localBond jet 0 m = jet 0 0 := by simp [localBond]

theorem localBond_top (jet : ℕ → ℕ → ℝ) (q : ℕ) (m : ℤ) :
    localBond jet (q+1) m =
      (∑ k ∈ range (q+1), (m:ℝ)^(q+1-k) /
        (Nat.factorial (q+1-k):ℝ) * jet k (q+1-k)) + jet (q+1) 0 := by
  rw [localBond,Finset.sum_range_succ]
  simp

/-- Noncommutative coefficient recursion (198); finite sums only.
This does not assert the formal unbounded Taylor arrays are bounded operators. -/
def resolventCoeff {R : Type*} [Ring R] (R0 : R) (L : ℕ → R) : ℕ → R
  | 0 => R0
  | n+1 => R0 * ∑ k : Fin (n+1), L (k.val+1) * resolventCoeff R0 L (n-k.val)
termination_by n => n
decreasing_by omega

theorem resolventCoeff_zero {R : Type*} [Ring R] (R0 : R) (L : ℕ → R) :
    resolventCoeff R0 L 0 = R0 := by rw [resolventCoeff]

theorem resolventCoeff_succ {R : Type*} [Ring R] (R0 : R) (L : ℕ → R) (n : ℕ) :
    resolventCoeff R0 L (n+1) =
      R0 * ∑ k : Fin (n+1), L (k.val+1) * resolventCoeff R0 L (n-k.val) := by
  rw [resolventCoeff]

/-- Exact finite iterated resolvent identity, retaining the full remainder
at arbitrary truncation N. Valid for noncommuting factors. -/
theorem iterated_resolvent {R : Type*} [Ring R] (R0 X R1 : R)
    (h : R1 = R0 + X*R1) (N : ℕ) :
    R1 = (∑ n ∈ range N, X^n * R0) + X^N*R1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    calc
      R1 = (∑ n ∈ range N, X^n * R0) + X^N*R1 := ih
      _ = (∑ n ∈ range N, X^n * R0) + X^N*(R0+X*R1) := by rw [← h]
      _ = (∑ n ∈ range (N+1), X^n * R0) + X^(N+1)*R1 := by
        rw [Finset.sum_range_succ,pow_succ,mul_add,mul_assoc (X^N) X R1]
        abel

/-- Coefficient equation (200): cancellation and uniqueness of the new
coefficient once the slope of the frozen multiplier is identified. -/
def nextBond (b0 Ghat slope : ℝ) (b G : ℕ → ℝ) (q : ℕ) : ℝ :=
  -(b0*Ghat + ∑ k ∈ range (q-1), b (k+1)*G (q-(k+1))) / (2*slope)

theorem nextBond_cancel (b0 Ghat slope : ℝ) (b G : ℕ → ℝ) (q : ℕ)
    (hs : slope ≠ 0) :
    2*slope*nextBond b0 Ghat slope b G q +
      (b0*Ghat + ∑ k ∈ range (q-1), b (k+1)*G (q-(k+1))) = 0 := by
  unfold nextBond
  field_simp
  ring

theorem nextBond_unique (b0 Ghat slope : ℝ) (b G : ℕ → ℝ) (q : ℕ)
    (hs : slope ≠ 0) (x : ℝ)
    (hx : 2*slope*x + (b0*Ghat + ∑ k ∈ range (q-1), b (k+1)*G (q-(k+1))) = 0) :
    x = nextBond b0 Ghat slope b G q := by
  have h := nextBond_cancel b0 Ghat slope b G q hs
  have he : (2*slope)*(x-nextBond b0 Ghat slope b G q) = 0 := by linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) hs))

/-- Uniform coercive transfer at arbitrary order N from the weighted
energy estimate, with no fixed-order specialization. -/
theorem order_transfer (M μ C d : ℝ) (hM : 0 < M) (hμ : 0 < μ) (hC : 0 ≤ C)
    (N : ℕ) (henergy : d^2 ≤ 4/μ^2 * C^2/M^(2*N)) :
    |d| ≤ 2*C/μ/M^N := by
  have hh : (2*C/μ/M^N)^2 = 4/μ^2*C^2/M^(2*N) := by
    rw [pow_mul]
    ring
  have hp : 0 ≤ 2*C/μ/M^N := by positivity
  have hsq : |d|^2 ≤ (2*C/μ/M^N)^2 := by rw [sq_abs,hh]; exact henergy
  nlinarith [abs_nonneg d]

end M12RecurrenceAllOrder

#print axioms M12RecurrenceAllOrder.localBond_zero
#print axioms M12RecurrenceAllOrder.localBond_top
#print axioms M12RecurrenceAllOrder.resolventCoeff_zero
#print axioms M12RecurrenceAllOrder.resolventCoeff_succ
#print axioms M12RecurrenceAllOrder.iterated_resolvent
#print axioms M12RecurrenceAllOrder.nextBond_cancel
#print axioms M12RecurrenceAllOrder.nextBond_unique
#print axioms M12RecurrenceAllOrder.order_transfer
