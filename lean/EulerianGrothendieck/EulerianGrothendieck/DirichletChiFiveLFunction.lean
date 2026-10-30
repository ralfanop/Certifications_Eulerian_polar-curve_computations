import EulerianGrothendieck.DirichletChiFive
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.PSeries

/-! # Task E, part 1b: `L(1, χ₅)` as Mathlib's `DirichletCharacter.LFunction`

`DirichletChiFive.lean` proves that the partial sums of `∑ χ₅(n)/n` converge to
`(2/√5) log φ` (Mathar, Table 22, `m = 5, r = 3, s = 1`; OEIS A086466).  Here the same value is
identified with Mathlib's analytically continued L-function `DirichletCharacter.LFunction χ₅ 1`,
where `χ₅ : DirichletCharacter ℂ 5` is the quadratic character of `ZMod 5`.

The argument is Abel's theorem for Dirichlet series, in a form that needs no measure theory:

* with `S_i = ∑_{m ≤ i} χ₅(m)` (so `|S_i| ≤ 1`), summation by parts gives for every `σ ≥ 1`
  `∑_{i ≤ n} i^{-σ} χ₅(i) = n^{-σ} S_n + ∑_{i < n} (i^{-σ} - (i+1)^{-σ}) S_i`
  (`abel_partial`);
* the transformed series `A(σ) = ∑_i (i^{-σ} - (i+1)^{-σ}) S_i` is dominated by `8/(i+1)²`
  uniformly for `1 ≤ σ ≤ 2` (mean value theorem, `weight_diff_le`, `term_bound`), hence
  `A(σ) → A(1)` as `σ → 1⁺` (dominated convergence for series, `abelSeries_tendsto_one`);
* `A(1)` is the limit of the partial sums, i.e. `(2/√5) log φ` (`abelSeries_one`), and for
  `σ > 1` Mathlib's `LSeries` equals `A(σ)` (`LSeries_chiFive_eq`);
* `LFunction χ₅ σ = LSeries χ₅ σ` for `σ > 1` (`LFunction_eq_LSeries`) and `LFunction χ₅` is
  continuous at `1` because `χ₅ ≠ 1` (`differentiable_LFunction`), so the two limits agree.

Main result: `LFunction_chiFive_one : LFunction χ₅ 1 = (2/√5) log φ` (unconditional). -/

noncomputable section
open scoped BigOperators
open Finset Filter Topology

namespace EulerianGrothendieck.Dirichlet

/-- `χ₅` as a `ℂ`-valued Dirichlet character modulo `5`. -/
def chiFiveChar : DirichletCharacter ℂ 5 :=
  (quadraticChar (ZMod 5)).ringHomComp (Int.castRingHom ℂ)

theorem chiFiveChar_apply (n : ℕ) : chiFiveChar (n : ZMod 5) = ((chiFive n : ℝ) : ℂ) := by
  simp only [chiFiveChar, MulChar.ringHomComp_apply, chiFive, eq_intCast, Complex.ofReal_intCast]

theorem chiFiveChar_zero : chiFiveChar ((0 : ℕ) : ZMod 5) = 0 := by
  rw [chiFiveChar_apply, chiFive_zero]; simp

theorem chiFiveChar_ne_one : chiFiveChar ≠ 1 := by
  intro h
  have h2 : chiFiveChar ((2 : ℕ) : ZMod 5) = (1 : DirichletCharacter ℂ 5) ((2 : ℕ) : ZMod 5) := by
    rw [h]
  rw [chiFiveChar_apply, chiFive_two,
    MulChar.one_apply (isUnit_of_mul_eq_one _ ((3 : ℕ) : ZMod 5) (by decide))] at h2
  norm_num at h2

/-! ### Partial sums of `χ₅` -/

/-- `S n = ∑_{m ≤ n} χ₅(m)`. -/
def chiPartial (n : ℕ) : ℝ := ∑ m ∈ range (n + 1), chiFive m

theorem chiPartial_zero : chiPartial 0 = 0 := by
  simp [chiPartial, chiFive_zero]

theorem chiFive_block_sum (m : ℕ) : ∑ x ∈ range 5, chiFive (m + x) = 0 := by
  have h : ∀ x, chiFive (m + x) = chiFive ((m % 5 + x) % 5) := by
    intro x
    rw [chiFive_mod]
    congr 1
    omega
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h]
  have hm : m % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize m % 5 = r at hm ⊢
  interval_cases r <;>
    norm_num [chiFive_zero, chiFive_one, chiFive_two, chiFive_three, chiFive_four]

theorem chiPartial_add_five (n : ℕ) : chiPartial (n + 5) = chiPartial n := by
  unfold chiPartial
  rw [show n + 5 + 1 = (n + 1) + 5 by ring, Finset.sum_range_add, chiFive_block_sum, add_zero]

theorem chiPartial_mod (n : ℕ) : chiPartial n = chiPartial (n % 5) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 5 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · have hn : n = (n - 5) + 5 := by omega
      rw [hn, chiPartial_add_five, ih (n - 5) (by omega)]
      congr 1
      omega

theorem chiPartial_abs_le (n : ℕ) : |chiPartial n| ≤ 1 := by
  rw [chiPartial_mod]
  have h : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize n % 5 = r at h ⊢
  interval_cases r <;>
    norm_num [chiPartial, Finset.sum_range_succ, chiFive_zero, chiFive_one, chiFive_two,
      chiFive_three, chiFive_four]

/-! ### Summation by parts -/

theorem abel_partial (σ : ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), (i : ℝ) ^ (-σ) * chiFive i =
      (n : ℝ) ^ (-σ) * chiPartial n +
        ∑ i ∈ range n, ((i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)) * chiPartial i := by
  have h := Finset.sum_range_by_parts (fun i : ℕ => (i : ℝ) ^ (-σ)) chiFive (n + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at h
  rw [h]
  unfold chiPartial
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-! ### The dominating bound -/

theorem summable_bound : Summable (fun i : ℕ => 8 / ((i : ℝ) + 1) ^ 2) := by
  have h0 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have h1 : Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) := by
    refine ((summable_nat_add_iff 1).mpr h0).congr (fun i => ?_)
    push_cast
    ring
  refine (h1.mul_left 8).congr (fun i => ?_)
  ring

/-- Mean value theorem: `i^{-σ} - (i+1)^{-σ} ≤ σ i^{-σ-1} ≤ 2/i²` for `1 ≤ σ ≤ 2`, `i ≥ 1`. -/
theorem weight_diff_le {σ : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) {i : ℕ} (hi : 1 ≤ i) :
    (i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ) ≤ 2 / (i : ℝ) ^ 2 := by
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hi0 : (0 : ℝ) < i := by linarith
  have hderiv : ∀ x ∈ Set.Icc (i : ℝ) ((i : ℝ) + 1),
      HasDerivWithinAt (fun x : ℝ => x ^ (-σ)) (-σ * x ^ (-σ - 1))
        (Set.Icc (i : ℝ) ((i : ℝ) + 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    exact (Real.hasDerivAt_rpow_const (Or.inl hx0)).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Icc (i : ℝ) ((i : ℝ) + 1),
      ‖-σ * x ^ (-σ - 1)‖ ≤ σ * (i : ℝ) ^ (-σ - 1) := by
    intro x hx
    rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < σ),
      abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1]) _)]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact Real.rpow_le_rpow_of_exponent_nonpos hi0 hx.1 (by linarith)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Icc _ _)
    (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, add_sub_cancel_left, abs_one, mul_one] at hmvt
  have h1 : (i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ) ≤ σ * (i : ℝ) ^ (-σ - 1) := by
    calc (i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)
        ≤ |(i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)| := le_abs_self _
      _ = |((i : ℝ) + 1) ^ (-σ) - (i : ℝ) ^ (-σ)| := abs_sub_comm _ _
      _ ≤ σ * (i : ℝ) ^ (-σ - 1) := hmvt
  have h2 : (i : ℝ) ^ (-σ - 1) ≤ (i : ℝ) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hi' (by linarith)
  have h3 : (i : ℝ) ^ (-(2 : ℝ)) = 1 / (i : ℝ) ^ 2 := by
    rw [Real.rpow_neg hi0.le, Real.rpow_two, one_div]
  calc (i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ) ≤ σ * (i : ℝ) ^ (-σ - 1) := h1
    _ ≤ 2 * (1 / (i : ℝ) ^ 2) := by
        rw [← h3]
        exact mul_le_mul hσ2 h2 (Real.rpow_nonneg hi0.le _) (by norm_num)
    _ = 2 / (i : ℝ) ^ 2 := by ring

theorem term_bound {σ : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (i : ℕ) :
    ‖((i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)) * chiPartial i‖ ≤ 8 / ((i : ℝ) + 1) ^ 2 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [chiPartial_zero, mul_zero, norm_zero]
    positivity
  · have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
    have hi0 : (0 : ℝ) < i := by linarith
    have hnn : 0 ≤ (i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ) := by
      have := Real.rpow_le_rpow_of_exponent_nonpos hi0 (by linarith : (i : ℝ) ≤ (i : ℝ) + 1)
        (by linarith : -σ ≤ 0)
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    calc ((i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)) * |chiPartial i|
        ≤ (2 / (i : ℝ) ^ 2) * 1 :=
          mul_le_mul (weight_diff_le hσ1 hσ2 hi) (chiPartial_abs_le i) (abs_nonneg _)
            (by positivity)
      _ ≤ 8 / ((i : ℝ) + 1) ^ 2 := by
          rw [mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith

/-! ### The Abel-transformed series -/

/-- `A(σ) = ∑_i (i^{-σ} - (i+1)^{-σ}) S_i`. -/
def abelSeries (σ : ℝ) : ℝ := ∑' i : ℕ, ((i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)) * chiPartial i

theorem abelSeries_hasSum {σ : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) :
    HasSum (fun i : ℕ => ((i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)) * chiPartial i)
      (abelSeries σ) :=
  (Summable.of_norm_bounded summable_bound (term_bound hσ1 hσ2)).hasSum

theorem partial_tendsto_abelSeries {σ : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) :
    Tendsto (fun n : ℕ => ∑ i ∈ range n, (i : ℝ) ^ (-σ) * chiFive i) atTop
      (𝓝 (abelSeries σ)) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-σ) * chiPartial n) atTop (𝓝 0) := by
    have hw : Tendsto (fun n : ℕ => (n : ℝ) ^ (-σ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    refine squeeze_zero_norm (fun n => ?_) hw
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg n) _) (chiPartial_abs_le n)
  have h2 := (abelSeries_hasSum hσ1 hσ2).tendsto_sum_nat
  have h3 : Tendsto (fun n : ℕ => ∑ i ∈ range (n + 1), (i : ℝ) ^ (-σ) * chiFive i) atTop
      (𝓝 (abelSeries σ)) := by
    have := h1.add h2
    rw [zero_add] at this
    exact this.congr (fun n => (abel_partial σ n).symm)
  exact (tendsto_add_atTop_iff_nat 1).mp h3

/-- At `σ = 1` the transformed series is the limit of the partial sums of `∑ χ₅(n)/n`. -/
theorem abelSeries_one : abelSeries 1 = 2 / Real.sqrt 5 * Real.log phi := by
  have h := partial_tendsto_abelSeries (le_refl (1 : ℝ)) (by norm_num)
  have h' : Tendsto partialSum atTop (𝓝 (abelSeries 1)) := by
    refine h.congr (fun n => ?_)
    unfold partialSum
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.rpow_neg_one]
    ring
  exact tendsto_nhds_unique h' dirichlet_chiFive_tendsto

/-! ### Identification with `LSeries` for `σ > 1` -/

theorem term_eq (σ : ℝ) (n : ℕ) :
    LSeries.term (fun m : ℕ => chiFiveChar m) (σ : ℂ) n =
      (((n : ℝ) ^ (-σ) * chiFive n : ℝ) : ℂ) := by
  rw [LSeries.term_def₀ (f := fun m : ℕ => chiFiveChar m) chiFiveChar_zero]
  show chiFiveChar (n : ZMod 5) * (n : ℂ) ^ (-(σ : ℂ)) = _
  rw [chiFiveChar_apply, Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  ring

theorem LSeries_chiFive_eq {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    LSeries (fun m : ℕ => chiFiveChar m) (σ : ℂ) = (abelSeries σ : ℂ) := by
  have hS : LSeriesSummable (fun m : ℕ => chiFiveChar m) (σ : ℂ) := by
    refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) (by simpa using hσ)
    show ‖chiFiveChar (n : ZMod 5)‖ ≤ 1
    rw [chiFiveChar_apply, Complex.norm_real, Real.norm_eq_abs]
    exact chiFive_abs_le n
  have h1 : Tendsto (fun n : ℕ => ∑ i ∈ range n, LSeries.term (fun m : ℕ => chiFiveChar m) (σ : ℂ) i)
      atTop (𝓝 (LSeries (fun m : ℕ => chiFiveChar m) (σ : ℂ))) :=
    hS.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun n : ℕ => ∑ i ∈ range n, LSeries.term (fun m : ℕ => chiFiveChar m) (σ : ℂ) i)
      atTop (𝓝 (abelSeries σ : ℂ)) := by
    have := (Complex.continuous_ofReal.tendsto _).comp (partial_tendsto_abelSeries hσ.le hσ2)
    refine this.congr (fun n => ?_)
    simp only [Function.comp_apply, Complex.ofReal_sum, term_eq]
  exact tendsto_nhds_unique h1 h2

/-! ### The limit `σ → 1⁺` on both sides -/

theorem LFunction_tendsto :
    Tendsto (fun σ : ℝ => DirichletCharacter.LFunction chiFiveChar (σ : ℂ)) (𝓝[>] (1 : ℝ))
      (𝓝 (DirichletCharacter.LFunction chiFiveChar 1)) := by
  have hc : Continuous (DirichletCharacter.LFunction chiFiveChar) :=
    (DirichletCharacter.differentiable_LFunction chiFiveChar_ne_one).continuous
  have h1 : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    have := Complex.continuous_ofReal.tendsto (1 : ℝ)
    rw [Complex.ofReal_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact (hc.tendsto 1).comp h1

theorem abelSeries_tendsto_one : Tendsto abelSeries (𝓝[>] (1 : ℝ)) (𝓝 (abelSeries 1)) := by
  unfold abelSeries
  refine tendsto_tsum_of_dominated_convergence summable_bound (fun i => ?_) ?_
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [chiPartial_zero, mul_zero]
      exact tendsto_const_nhds
    · have hi0 : (i : ℝ) ≠ 0 := by positivity
      have hi1 : (i : ℝ) + 1 ≠ 0 := by positivity
      have hc : Continuous (fun σ : ℝ => ((i : ℝ) ^ (-σ) - ((i : ℝ) + 1) ^ (-σ)) * chiPartial i) := by
        apply Continuous.mul _ continuous_const
        apply Continuous.sub
        · exact continuous_const.rpow continuous_neg (fun x => Or.inl hi0)
        · exact continuous_const.rpow continuous_neg (fun x => Or.inl hi1)
      exact (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with σ hσ i
    exact term_bound hσ.1.le hσ.2 i

/-- **`L(1, χ₅) = (2/√5) log φ`** for Mathlib's analytically continued Dirichlet L-function
(Mathar, Table 22; OEIS A086466). -/
theorem LFunction_chiFive_one :
    DirichletCharacter.LFunction chiFiveChar 1 = ((2 / Real.sqrt 5 * Real.log phi : ℝ) : ℂ) := by
  have hA : Tendsto (fun σ : ℝ => DirichletCharacter.LFunction chiFiveChar (σ : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 ((abelSeries 1 : ℝ) : ℂ)) := by
    have h := (Complex.continuous_ofReal.tendsto _).comp abelSeries_tendsto_one
    refine h.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with σ hσ
    simp only [Function.comp_apply]
    rw [DirichletCharacter.LFunction_eq_LSeries chiFiveChar (by simpa using hσ.1),
      LSeries_chiFive_eq hσ.1 hσ.2]
  rw [← abelSeries_one]
  exact tendsto_nhds_unique LFunction_tendsto hA

/-- The same value in the form of Mathar's Table 22: `2 log((1+√5)/2)/√5`. -/
theorem LFunction_chiFive_one' :
    DirichletCharacter.LFunction chiFiveChar 1 =
      ((2 * Real.log ((1 + Real.sqrt 5) / 2) / Real.sqrt 5 : ℝ) : ℂ) := by
  rw [LFunction_chiFive_one]
  congr 1
  unfold phi
  ring

/-- `LFunction χ₅ 1` coincides with the limit of the partial sums `LOneChiFive`. -/
theorem LFunction_chiFive_one_eq_LOneChiFive :
    DirichletCharacter.LFunction chiFiveChar 1 = (LOneChiFive : ℂ) := by
  rw [LFunction_chiFive_one, LOneChiFive_eq]

end EulerianGrothendieck.Dirichlet
