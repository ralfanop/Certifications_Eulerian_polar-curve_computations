import Mathlib

/-!
M15 §6.5, continuation of analytic PR #372. Positive squarefree weights
indexed by n+1, actual infinite summability, a finite tail bound at s=2,
and finite matrix determinant/trace identities. No infinite operator
trace, Euler-product identity or Fredholm identification is assumed.
-/
namespace Manuscript15.SquarefreeDeterminant

noncomputable def squarefreeWeight (s : ℝ) (n : ℕ) : ℝ := by
  classical
  exact if Squarefree (n + 1) then 1 / ((n : ℝ) + 1) ^ s else 0

theorem weight_nonneg (s : ℝ) (n : ℕ) : 0 ≤ squarefreeWeight s n := by
  unfold squarefreeWeight
  split <;> positivity

theorem weight_le_pseries (s : ℝ) (n : ℕ) :
    squarefreeWeight s n ≤ 1 / ((n : ℝ) + 1) ^ s := by
  unfold squarefreeWeight
  split
  · exact le_rfl
  · positivity

theorem weight_summable (s : ℝ) (hs : 1 < s) :
    Summable (squarefreeWeight s) := by
  have hp : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ s) :=
    (Real.summable_one_div_nat_add_rpow 1 s).mpr hs
  have hlarge : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ s) := by
    convert hp using 1
    funext n
    rw [abs_of_nonneg (by positivity)]
  exact Summable.of_nonneg_of_le (weight_nonneg s) (weight_le_pseries s) hlarge

theorem spectral_moment_summable (s : ℝ) (m : ℕ) (hs : 1 < s)
    (hm : 1 ≤ m) : Summable (squarefreeWeight ((m : ℝ) * s)) := by
  have hm' : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  apply weight_summable
  nlinarith [mul_nonneg (sub_nonneg.mpr hm') (show 0 ≤ s by linarith)]

noncomputable def resolventWeight (s x : ℝ) (n : ℕ) : ℝ :=
  squarefreeWeight s n / (1 + x * squarefreeWeight s n)

theorem resolvent_nonneg (s x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ resolventWeight s x n := by
  unfold resolventWeight
  have h := weight_nonneg s n
  exact div_nonneg h (by positivity)

theorem resolvent_le_weight (s x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    resolventWeight s x n ≤ squarefreeWeight s n := by
  unfold resolventWeight
  have h := weight_nonneg s n
  have hd : 0 < 1 + x * squarefreeWeight s n := by positivity
  apply (div_le_iff₀ hd).2
  nlinarith [mul_nonneg hx (sq_nonneg (squarefreeWeight s n))]

theorem resolvent_summable (s x : ℝ) (hs : 1 < s) (hx : 0 ≤ x) :
    Summable (resolventWeight s x) :=
  Summable.of_nonneg_of_le (resolvent_nonneg s x hx)
    (resolvent_le_weight s x hx) (weight_summable s hs)

theorem inverse_square_le_telescope (a : ℝ) (ha : 0 < a) :
    1 / (a + 1) ^ 2 ≤ 1 / a - 1 / (a + 1) := by
  have ha1 : 0 < a + 1 := by linarith
  rw [show 1 / a - 1 / (a + 1) = 1 / (a * (a + 1)) by
    field_simp <;> ring]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

theorem weight_two_le_telescope (n : ℕ) (hn : 1 ≤ n) :
    squarefreeWeight 2 n ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
  have hn' : 0 < (n : ℝ) := by
    have h : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  calc
    squarefreeWeight 2 n ≤ 1 / ((n : ℝ) + 1) ^ (2 : ℝ) :=
      weight_le_pseries 2 n
    _ = 1 / ((n : ℝ) + 1) ^ (2 : ℕ) := by rw [Real.rpow_two]
    _ ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := inverse_square_le_telescope _ hn'

theorem finite_tail_two (N k : ℕ) (hN : 1 ≤ N) :
    (∑ i ∈ Finset.range k, squarefreeWeight 2 (N + i)) ≤
      1 / (N : ℝ) - 1 / ((N : ℝ) + (k : ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have hk : 1 ≤ N + k := by omega
    have hstep := weight_two_le_telescope (N + k) hk
    rw [Nat.cast_add] at hstep
    rw [← add_assoc]
    linarith

/-- Finite determinant of I+zT, for an actual diagonal matrix. -/
theorem finite_diagonal_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (z : ℂ) :
    Matrix.det (1 + z • Matrix.diagonal a) = ∏ i, (1 + z * a i) := by
  rw [show (1 + z • Matrix.diagonal a : Matrix ι ι ℂ) =
      Matrix.diagonal (fun i => 1 + z * a i) by
    ext i j
    by_cases h : i = j
    · subst j
      simp [Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul]
    · simp [Matrix.one_apply, Matrix.diagonal_apply, h, smul_eq_mul]]
  exact Matrix.det_diagonal _

theorem finite_diagonal_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) :
    Matrix.trace (Matrix.diagonal a) = ∑ i, a i := by
  simp [Matrix.trace]

#print axioms Manuscript15.SquarefreeDeterminant.weight_nonneg
#print axioms Manuscript15.SquarefreeDeterminant.weight_le_pseries
#print axioms Manuscript15.SquarefreeDeterminant.weight_summable
#print axioms Manuscript15.SquarefreeDeterminant.spectral_moment_summable
#print axioms Manuscript15.SquarefreeDeterminant.resolvent_nonneg
#print axioms Manuscript15.SquarefreeDeterminant.resolvent_le_weight
#print axioms Manuscript15.SquarefreeDeterminant.resolvent_summable
#print axioms Manuscript15.SquarefreeDeterminant.inverse_square_le_telescope
#print axioms Manuscript15.SquarefreeDeterminant.weight_two_le_telescope
#print axioms Manuscript15.SquarefreeDeterminant.finite_tail_two
#print axioms Manuscript15.SquarefreeDeterminant.finite_diagonal_det
#print axioms Manuscript15.SquarefreeDeterminant.finite_diagonal_trace
end Manuscript15.SquarefreeDeterminant
