/-
# Elementary identities of Corollary 3.3, Lemma 3.14 and §3.11 (V478)

* Cor. 3.3 / Eq. (21): `∑_{n>N} 1/(n² - 1/4) = 2/(2N+1)` and the resulting strict bound
  `∑_{n>N} |A_n| < (2/π)³/(2N+1)` from the strict termwise bound of Eq. (9).
* Lemma 3.14 (proof): `Jᵀ J = I + 𝟙𝟙ᵀ` and `det(I + 𝟙𝟙ᵀ) = n + 1` (area factor `√(n+1)`).
* §3.11, after Eq. (79): exact homothety of the Gaussian leading profiles.
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Real.Pi.Bounds

open Real Finset
open scoped Matrix

namespace EulerianCert.Combinatorics

/-! ### Telescoping sum and the explicit truncation bound -/

lemma partial_sum (N M : ℕ) :
    ∑ n ∈ range M, (1 / (((n + N + 1 : ℕ) : ℝ) ^ 2 - 1 / 4)) =
      1 / ((N : ℝ) + 1 / 2) - 1 / ((N : ℝ) + M + 1 / 2) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih]
    push_cast
    have h1 : (0 : ℝ) < (N : ℝ) + M + 1 / 2 := by positivity
    have h2 : (0 : ℝ) < (N : ℝ) + M + 3 / 2 := by positivity
    have h3 : ((M : ℝ) + N + 1) ^ 2 - 1 / 4 = ((N : ℝ) + M + 1 / 2) * ((N : ℝ) + M + 3 / 2) := by
      ring
    rw [h3]
    field_simp
    ring

theorem hasSum_telescope (N : ℕ) :
    HasSum (fun n : ℕ => 1 / (((n + N + 1 : ℕ) : ℝ) ^ 2 - 1 / 4)) ((2 : ℝ) / (2 * N + 1)) := by
  have hpos : ∀ n : ℕ, 0 ≤ 1 / (((n + N + 1 : ℕ) : ℝ) ^ 2 - 1 / 4) := by
    intro n
    apply div_nonneg zero_le_one
    have : (1 : ℝ) ≤ ((n + N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    nlinarith
  rw [hasSum_iff_tendsto_nat_of_nonneg hpos]
  simp_rw [partial_sum]
  have e : (2 : ℝ) / (2 * N + 1) = 1 / ((N : ℝ) + 1 / 2) - 0 := by
    field_simp; ring
  rw [e]
  apply Filter.Tendsto.sub tendsto_const_nhds
  have : Filter.Tendsto (fun M : ℕ => (N : ℝ) + M + 1 / 2) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_right
    exact Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  exact Filter.Tendsto.congr (fun M => by simp only [Pi.inv_apply, one_div]) this.inv_tendsto_atTop

/-- Eq. (21): if `0 ≤ |A_{n}| ≤ 4/(π³(n² - 1/4))` for every `n > N`, then the tail is at most
`(2/π)³/(2N+1)`. -/
theorem tail_bound (N : ℕ) (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n)
    (ha : ∀ n, a n ≤ 4 / π ^ 3 * (1 / (((n + N + 1 : ℕ) : ℝ) ^ 2 - 1 / 4))) :
    ∑' n, a n ≤ (2 / π) ^ 3 / (2 * N + 1) := by
  have hS := (hasSum_telescope N).mul_left (4 / π ^ 3)
  have hsa : Summable a := Summable.of_nonneg_of_le ha0 ha hS.summable
  calc ∑' n, a n ≤ ∑' n, 4 / π ^ 3 * (1 / (((n + N + 1 : ℕ) : ℝ) ^ 2 - 1 / 4)) :=
        hsa.tsum_le_tsum ha hS.summable
    _ = 4 / π ^ 3 * (2 / (2 * N + 1)) := hS.tsum_eq
    _ = (2 / π) ^ 3 / (2 * N + 1) := by ring

/-- Eq. (21), strict form: with the strict termwise bound the tail is `< (2/π)³/(2N+1)`. -/
theorem tail_bound_strict (N : ℕ) (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n)
    (ha : ∀ n, a n < 4 / π ^ 3 * (1 / (((n + N + 1 : ℕ) : ℝ) ^ 2 - 1 / 4))) :
    ∑' n, a n < (2 / π) ^ 3 / (2 * N + 1) := by
  have hS := (hasSum_telescope N).mul_left (4 / π ^ 3)
  calc ∑' n, a n < ∑' n, 4 / π ^ 3 * (1 / (((n + N + 1 : ℕ) : ℝ) ^ 2 - 1 / 4)) :=
        Summable.tsum_lt_tsum_of_nonneg (i := 0) ha0 (fun n => (ha n).le) (ha 0) hS.summable
    _ = 4 / π ^ 3 * (2 / (2 * N + 1)) := hS.tsum_eq
    _ = (2 / π) ^ 3 / (2 * N + 1) := by ring

/-! ### Lemma 3.14 (cube slabs and sections): the area factor -/

/-- Derivative of the affine injection `T_k(x) = (k - ∑ x_j, x)`. -/
def J (n : ℕ) : Matrix (Fin (n + 1)) (Fin n) ℝ :=
  Matrix.of fun i j => Fin.cases (-1) (fun i' => if i' = j then 1 else 0) i

theorem JtJ (n : ℕ) : (J n)ᵀ * J n = 1 + Matrix.of (fun _ _ => (1 : ℝ)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.of_apply, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, Matrix.add_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, eq_comm]

theorem det_JtJ (n : ℕ) : ((J n)ᵀ * J n).det = n + 1 := by
  rw [JtJ]
  have := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit)
    (fun _ : Fin n => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ))
  have e : Matrix.replicateCol Unit (fun _ : Fin n => (1 : ℝ)) *
      Matrix.replicateRow Unit (fun _ : Fin n => (1 : ℝ)) = Matrix.of (fun _ _ => (1 : ℝ)) := by
    ext i j; simp [Matrix.mul_apply]
  rw [e] at this
  rw [this]
  simp [dotProduct]
  ring

/-! ### Gaussian homothety (§3.11, after Eq. (79)) -/

noncomputable def G (D x : ℝ) : ℝ := Real.sqrt (6 / (π * D)) * Real.exp (-6 * D * (x - 1 / 2) ^ 2)

theorem gaussian_homothety (D D' x : ℝ) (hD : 0 < D) (hD' : 0 < D') :
    G D' (1 / 2 + Real.sqrt (D / D') * (x - 1 / 2)) = Real.sqrt (D / D') * G D x := by
  unfold G
  have hl : Real.sqrt (D / D') ^ 2 = D / D' := Real.sq_sqrt (by positivity)
  have harg : -6 * D' * (1 / 2 + Real.sqrt (D / D') * (x - 1 / 2) - 1 / 2) ^ 2 =
      -6 * D * (x - 1 / 2) ^ 2 := by
    have : (1 / 2 + Real.sqrt (D / D') * (x - 1 / 2) - 1 / 2) ^ 2 =
        Real.sqrt (D / D') ^ 2 * (x - 1 / 2) ^ 2 := by ring
    rw [this, hl]; field_simp
  rw [harg, ← mul_assoc]
  congr 1
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

end EulerianCert.Combinatorics
