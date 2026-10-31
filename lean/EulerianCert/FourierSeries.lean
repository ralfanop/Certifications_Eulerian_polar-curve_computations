/-
# Proposition 3.1 (Fourier identification) and its consequences for `r_E` (V001)

* `fourier_series_rE`: for `θ ∈ [-π, π]`, `r_E θ = A₀/2 + ∑_{n ≥ 1} A_n cos(nθ)` (Eq. (5)); the
  proof lifts the periodic extension of `r_E` to `AddCircle (2π)`, computes its Fourier
  coefficients (`A_{|k|}/2`) and applies Mathlib's theorem on functions with summable Fourier
  coefficients (`has_pointwise_sum_fourier_series_of_summable`).
* `tendstoUniformly_partial_sums`: the cosine series converges uniformly on `ℝ` (M-test).
* The concrete forms, for `r_E`, of Corollary 3.3 (Eqs. (19)–(21)), Proposition 3.4 (Eq. (24)),
  Corollary 3.5 (Eq. (29), case `N = 1`), Corollary 3.8 (the bounds on `a_E`, `b_E` are now
  proved), Corollary 3.9 (Eq. (44)) and Corollary 3.11 (Eq. (57)), obtained from the abstract
  Lemma 3.2 of `SignCriterion` with `b = A₀/2`, `c_n = |A_{n+1}|`.
-/
import EulerianCert.FourierModes
import EulerianCert.SignCriterion
import EulerianCert.Combinatorics
import EulerianCert.Limacon
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Normed.Group.FunctionSeries

open Real Set Filter intervalIntegral Metric
open EulerianCert.FourierModes

noncomputable section

namespace EulerianCert.FourierSeries

/-! ### The periodic extension and its lift to the circle -/

/-- The `2π`-periodic even extension of `r_E`. -/
def ρ (θ : ℝ) : ℝ := rE (Real.arccos (Real.cos θ))

lemma ρ_eq {θ : ℝ} (hθ : θ ∈ Icc (-π) π) : ρ θ = rE θ := by
  rcases le_total 0 θ with h | h
  · rw [ρ, Real.arccos_cos h hθ.2]
  · rw [ρ, ← Real.cos_neg, Real.arccos_cos (by linarith) (by linarith [hθ.1]), rE_neg]

lemma ρ_periodic : Function.Periodic ρ (2 * π) := by
  intro θ; simp [ρ, Real.cos_add_two_pi]

lemma continuous_ρ : Continuous ρ :=
  continuous_rE.comp (Real.continuous_arccos.comp Real.continuous_cos)

instance : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- `r_E` as a continuous complex function on `AddCircle (2π)`. -/
def F : C(AddCircle (2 * π), ℂ) where
  toFun x := ((ρ_periodic.lift x : ℝ) : ℂ)
  continuous_toFun :=
    Complex.continuous_ofReal.comp (continuous_coinduced_dom.mpr continuous_ρ)

lemma F_coe (θ : ℝ) : F (θ : AddCircle (2 * π)) = (ρ θ : ℂ) := rfl

/-! ### Fourier coefficients -/

lemma integral_rE_sin (k : ℤ) : (∫ θ in (-π)..π, rE θ * Real.sin (k * θ)) = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -π) (b := π)
    (fun θ => rE θ * Real.sin (k * θ))
  simp only [neg_neg, rE_neg, mul_neg, Real.sin_neg] at h
  rw [intervalIntegral.integral_neg] at h
  linarith

lemma integral_rE_cos_int (k : ℤ) :
    (∫ θ in (-π)..π, rE θ * Real.cos (k * θ)) = π * A k.natAbs := by
  have hc : ∀ θ : ℝ, Real.cos (k * θ) = Real.cos ((k.natAbs : ℕ) * θ) := by
    intro θ
    have e : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [e]
    rcases abs_choice (k : ℝ) with h | h <;> rw [h]
    simp [neg_mul, Real.cos_neg]
  simp_rw [hc]
  rw [A]
  field_simp

lemma fourierCoeff_F (k : ℤ) : fourierCoeff F k = ((A k.natAbs / 2 : ℝ) : ℂ) := by
  rw [fourierCoeff_eq_intervalIntegral F k (-π)]
  have hb : -π + 2 * π = π := by ring
  rw [hb]
  have hint : ∀ θ ∈ uIcc (-π) π,
      (fourier (-k) (θ : AddCircle (2 * π)) • F θ) =
        ((rE θ * Real.cos (k * θ) : ℝ) : ℂ) - Complex.I * ((rE θ * Real.sin (k * θ) : ℝ) : ℂ) := by
    intro θ hθ
    rw [uIcc_of_le (by linarith [pi_pos])] at hθ
    rw [fourier_coe_apply, F_coe, ρ_eq hθ, smul_eq_mul]
    have : 2 * (π : ℂ) * Complex.I * ((-k : ℤ) : ℂ) * (θ : ℂ) / ((2 * π : ℝ) : ℂ) =
        (-((k * θ : ℝ) : ℂ)) * Complex.I := by
      have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
      push_cast
      field_simp
    rw [this, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    push_cast
    ring
  rw [intervalIntegral.integral_congr hint]
  have hc1 : Continuous (fun θ : ℝ => ((rE θ * Real.cos (k * θ) : ℝ) : ℂ)) := by
    have := continuous_rE; fun_prop
  have hc2 : Continuous (fun θ : ℝ => Complex.I * ((rE θ * Real.sin (k * θ) : ℝ) : ℂ)) := by
    have := continuous_rE; fun_prop
  rw [intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, integral_rE_sin, integral_rE_cos_int]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  rw [Complex.ofReal_zero, mul_zero, sub_zero, Complex.real_smul]
  push_cast
  field_simp

lemma summable_A : Summable A := summable_abs_A.of_abs

lemma summable_fourierCoeff_F : Summable (fourierCoeff F) := by
  have h : Summable (fun n : ℕ => ((A n / 2 : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr (summable_A.div_const 2)
  apply Summable.of_nat_of_neg
  · simpa [fourierCoeff_F] using h
  · simpa [fourierCoeff_F] using h

/-! ### Proposition 3.1: the cosine series of `r_E` -/

/-- Eq. (5) with `A₀` included: `∑_{n ≥ 0} A_n cos(nθ) = r_E θ + A₀/2` on `[-π, π]`. -/
lemma hasSum_cos_series {θ : ℝ} (hθ : θ ∈ Icc (-π) π) :
    HasSum (fun n : ℕ => A n * Real.cos (n * θ)) (rE θ + A 0 / 2) := by
  have h := has_pointwise_sum_fourier_series_of_summable summable_fourierCoeff_F
    (θ : AddCircle (2 * π))
  have h2 := h.nat_add_neg
  rw [F_coe, ρ_eq hθ] at h2
  have hterm : ∀ n : ℕ, (fourierCoeff F n • fourier (n : ℤ) (θ : AddCircle (2 * π)) +
      fourierCoeff F (-(n : ℤ)) • fourier (-(n : ℤ)) (θ : AddCircle (2 * π))) =
      ((A n * Real.cos (n * θ) : ℝ) : ℂ) := by
    intro n
    rw [fourierCoeff_F, fourierCoeff_F, fourier_coe_apply, fourier_coe_apply]
    simp only [Int.natAbs_neg, Int.natAbs_natCast, smul_eq_mul]
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
    have e1 : 2 * (π : ℂ) * Complex.I * ((n : ℤ) : ℂ) * (θ : ℂ) / ((2 * π : ℝ) : ℂ) =
        ((n * θ : ℝ) : ℂ) * Complex.I := by push_cast; field_simp
    have e2 : 2 * (π : ℂ) * Complex.I * ((-(n : ℤ) : ℤ) : ℂ) * (θ : ℂ) / ((2 * π : ℝ) : ℂ) =
        (-((n * θ : ℝ) : ℂ)) * Complex.I := by push_cast; field_simp
    rw [e1, e2, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    push_cast
    ring
  simp_rw [hterm] at h2
  have h0 : fourierCoeff F 0 • fourier (0 : ℤ) (θ : AddCircle (2 * π)) = ((A 0 / 2 : ℝ) : ℂ) := by
    rw [fourierCoeff_F]; simp
  rw [h0] at h2
  have h3 : HasSum (fun n : ℕ => ((A n * Real.cos (n * θ) : ℝ) : ℂ)) ((rE θ + A 0 / 2 : ℝ) : ℂ) := by
    push_cast at h2 ⊢; exact h2
  exact Complex.hasSum_ofReal.mp h3

/-- **Proposition 3.1, Eq. (5)**: `r_E θ = A₀/2 + ∑_{n ≥ 1} A_n cos(nθ)` for `θ ∈ [-π, π]`. -/
theorem fourier_series_rE {θ : ℝ} (hθ : θ ∈ Icc (-π) π) :
    HasSum (fun n : ℕ => A (n + 1) * Real.cos ((n + 1 : ℕ) * θ)) (rE θ - A 0 / 2) := by
  have h := hasSum_cos_series hθ
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, Real.cos_zero,
    mul_one] at h
  convert h using 1
  ring

/-- **Proposition 3.1**: absolute and uniform convergence of the cosine series (M-test). -/
theorem tendstoUniformly_partial_sums :
    TendstoUniformly (fun N θ => ∑ n ∈ Finset.range N, A n * Real.cos (n * θ))
      (fun θ => ∑' n, A n * Real.cos (n * θ)) atTop := by
  refine tendstoUniformly_tsum_nat summable_abs_A (fun n θ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-! ### The data of Lemma 3.2 for `r_E` -/

/-- `b = A₀/2`, `c_n = |A_{n+1}|` (mode `n + 1`). -/
def bE : ℝ := A 0 / 2
def cE (n : ℕ) : ℝ := |A (n + 1)|

lemma A_succ_eq (n : ℕ) : A (n + 1) = (-1 : ℝ) ^ n * cE n := by
  have h := (A_sign (n + 1) (by omega)).1
  rw [cE]
  conv_lhs => rw [h]
  rw [pow_succ, pow_succ]; ring

lemma cE_nonneg (n : ℕ) : 0 ≤ cE n := abs_nonneg _
lemma cE_pos (n : ℕ) : 0 < cE n := (A_sign (n + 1) (by omega)).2
lemma summable_cE : Summable cE := (summable_nat_add_iff 1).mpr summable_abs_A

/-- On `[-π, π]`, `r_E` is the alternating profile of Lemma 3.2. -/
lemma prof_eq_rE {θ : ℝ} (hθ : θ ∈ Icc (-π) π) : prof bE cE θ = rE θ := by
  have h := (fourier_series_rE hθ).tsum_eq
  rw [prof, bE]
  have : (fun n : ℕ => (-1 : ℝ) ^ n * cE n * Real.cos ((n + 1 : ℝ) * θ)) =
      (fun n : ℕ => A (n + 1) * Real.cos ((n + 1 : ℕ) * θ)) := by
    ext n; rw [A_succ_eq]; push_cast; ring
  rw [this, h]; ring

lemma pi_mem' : π ∈ Icc (-π) π := ⟨by linarith [pi_pos], le_rfl⟩

lemma tsum_cE : ∑' n, cE n = bE - 2 / π := by
  have h1 := prof_eq_rE pi_mem'
  rw [prof_pi, rE_pi] at h1
  linarith

lemma tsum_cE_lt : ∑' n, cE n < bE := by
  rw [tsum_cE]; linarith [show (0 : ℝ) < 2 / π by positivity]

lemma polarCurve_rE : polarCurve rE = polarCurve (prof bE cE) := by
  unfold polarCurve
  apply Set.image_congr
  intro θ hθ
  rw [prof_eq_rE hθ]

/-! ### Corollary 3.3, Proposition 3.4, Corollary 3.9 for `r_E` -/

/-- The cosine truncation `S_N θ = A₀/2 + ∑_{n=1}^{N} A_n cos(nθ)` (Eq. (18)). -/
def S (N : ℕ) (θ : ℝ) : ℝ := A 0 / 2 + ∑ n ∈ Finset.range N, A (n + 1) * Real.cos ((n + 1 : ℕ) * θ)

/-- The tail `E_N = ∑_{n > N} |A_n|` (Eq. (23)). -/
def EN (N : ℕ) : ℝ := ∑' n, cE (n + N)

lemma S_eq_prof (N : ℕ) (θ : ℝ) : S N θ = prof bE (trunc cE N) θ := by
  rw [prof_trunc, S, bE]
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [A_succ_eq]; push_cast; ring

lemma polarCurve_S (N : ℕ) : polarCurve (S N) = polarCurve (prof bE (trunc cE N)) := by
  unfold polarCurve
  apply Set.image_congr
  intro θ _
  rw [S_eq_prof]

lemma EN_pos (N : ℕ) : 0 < EN N := by
  have hs : Summable (fun n => cE (n + N)) := (summable_nat_add_iff N).mpr summable_cE
  exact hs.tsum_pos (fun n => cE_nonneg _) 0 (cE_pos _)

/-- **Corollary 3.3, Eqs. (19)–(20)** and **Corollary 3.9, Eq. (44)**: for every `N`, the sharp
uniform error of `S_N` on `[-π, π]` and the Hausdorff distance between the polar curves both
equal `E_N = ∑_{n > N} |A_n| = S_N(π) − 2/π`, attained at `θ = π`. -/
theorem sharp_truncation (N : ℕ) :
    IsGreatest ((fun θ => |rE θ - S N θ|) '' Icc (-π) π) (EN N) ∧
    S N π - 2 / π = EN N ∧
    hausdorffDist (polarCurve rE) (polarCurve (S N)) = EN N := by
  obtain ⟨-, hpc, -, hpd, hgr, hH⟩ :=
    sign_criterion cE_nonneg summable_cE tsum_cE_lt N
  refine ⟨⟨⟨π, pi_mem', ?_⟩, ?_⟩, ?_, ?_⟩
  · have := hgr.1
    obtain ⟨θ0, hθ0⟩ := this
    -- the maximum is attained at π (Lemma 3.2)
    simp only
    rw [prof_eq_rE pi_mem'] at hpc
    rw [S_eq_prof, ← prof_eq_rE pi_mem', prof_pi]
    rw [hpd, EN]
    rw [abs_sub_comm, abs_of_nonneg] <;> · have := tsum_cE; have := EN_pos N; unfold EN at this; linarith
  · rintro _ ⟨θ, hθ, rfl⟩
    have := hgr.2 ⟨θ, rfl⟩
    simp only at this ⊢
    rw [← prof_eq_rE hθ, S_eq_prof]
    exact this
  · rw [S_eq_prof, hpd, tsum_cE, EN]; ring
  · rw [polarCurve_rE, polarCurve_S]; exact hH

/-- **Corollary 3.3, Eq. (21)**: `E_N < (2/π)³/(2N+1)`. -/
theorem EN_lt (N : ℕ) : EN N < (2 / π) ^ 3 / (2 * N + 1) := by
  apply Combinatorics.tail_bound_strict N (fun n => cE (n + N)) (fun n => cE_nonneg _)
  intro n
  have h := (abs_A_bounds (n + N + 1) (by omega)).2
  rw [cE]
  have e : n + N + 1 = (n + N) + 1 := rfl
  calc |A (n + N + 1)| < 4 / (π ^ 3 * (((n + N + 1 : ℕ) : ℝ) ^ 2 - 1 / 4)) := h
    _ = 4 / π ^ 3 * (1 / (((n + N + 1 : ℕ) : ℝ) ^ 2 - 1 / 4)) := by
        rw [div_mul_div_comm, mul_one]

/-- **Proposition 3.4, Eq. (24)**: `S_N(θ) ≥ S_N(π) = 2/π + E_N > 2/π`. -/
theorem S_min (N : ℕ) (θ : ℝ) : S N π ≤ S N θ ∧ S N π = 2 / π + EN N ∧ 2 / π < S N π := by
  obtain ⟨-, -, hmin, -⟩ := sign_criterion cE_nonneg summable_cE tsum_cE_lt N
  have h2 := (sharp_truncation N).2.1
  refine ⟨?_, by linarith, by linarith [EN_pos N]⟩
  rw [S_eq_prof, S_eq_prof]; exact hmin θ

/-- **Corollary 3.11 (coefficient damping), Eq. (57)** for `r_E`. -/
theorem damping_rE (N : ℕ) (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) :
    let d : ℕ → ℝ := fun n => if n < N then w n * cE n else 0
    IsGreatest ((fun θ => |rE θ - prof bE d θ|) '' Icc (-π) π)
        (∑ n ∈ Finset.range N, (1 - w n) * cE n + ∑' n, cE (n + N)) ∧
    hausdorffDist (polarCurve rE) (polarCurve (prof bE d)) =
        ∑ n ∈ Finset.range N, (1 - w n) * cE n + ∑' n, cE (n + N) := by
  intro d
  obtain ⟨hgr, hH⟩ := damping cE_nonneg summable_cE tsum_cE_lt N w hw0 hw1
  refine ⟨⟨⟨π, pi_mem', ?_⟩, ?_⟩, by rw [polarCurve_rE]; exact hH⟩
  · -- attained at π: Lemma 3.2 gives the value at π
    have Hd : Hyp bE cE d :=
      ⟨fun n => by simp only [d]; split_ifs <;> simp [mul_nonneg (hw0 n) (cE_nonneg n)],
       fun n => by
         simp only [d]; split_ifs
         · exact mul_le_of_le_one_left (cE_nonneg n) (hw1 n)
         · exact cE_nonneg n, summable_cE, tsum_cE_lt⟩
    obtain ⟨⟨θ0, hθ0⟩, -⟩ := hgr
    have hpi := Hd.abs_sub_pi
    simp only
    rw [← prof_eq_rE pi_mem', hpi]
    have hE : ∑' n, (cE n - d n) = ∑ n ∈ Finset.range N, (1 - w n) * cE n + ∑' n, cE (n + N) := by
      rw [← Hd.summable_diff.sum_add_tsum_nat_add N]
      congr 1
      · refine Finset.sum_congr rfl (fun n hn => ?_)
        simp only [d, ite_eq_left (Finset.mem_range.1 hn)]; ring
      · congr 1; ext n; simp only [d]; rw [ite_eq_right (by omega)]; ring
    exact hE
  · rintro _ ⟨θ, hθ, rfl⟩
    have := hgr.2 ⟨θ, rfl⟩
    simp only at this ⊢
    rw [← prof_eq_rE hθ]
    exact this

/-! ### Corollary 3.5 (sharp error, `N = 1`) and Corollary 3.8 (hypotheses discharged) -/

def aE : ℝ := A 1

/-- **Corollary 3.5, Eq. (29)**: `‖r_E − (b_E + a_E cos)‖_∞ = b_E − a_E − 2/π`, attained at `π`,
and it equals the Hausdorff distance between the curves. -/
theorem projection_error :
    IsGreatest ((fun θ => |rE θ - (bE + aE * Real.cos θ)| ) '' Icc (-π) π) (bE - aE - 2 / π) ∧
    hausdorffDist (polarCurve rE) (polarCurve (fun θ => bE + aE * Real.cos θ)) = bE - aE - 2 / π := by
  have hS : ∀ θ, S 1 θ = bE + aE * Real.cos θ := by
    intro θ; simp [S, bE, aE]
  have hval : EN 1 = bE - aE - 2 / π := by
    have := (sharp_truncation 1).2.1
    rw [hS] at this
    rw [← this, Real.cos_pi]; ring
  obtain ⟨h1, -, h3⟩ := sharp_truncation 1
  simp_rw [hS] at h1 h3
  have e : (fun θ => bE + aE * Real.cos θ) = S 1 := by ext θ; rw [hS]
  rw [← hval]
  refine ⟨h1, ?_⟩
  rw [e]; exact h3

lemma aE_pos : 0 < aE := by
  have := A_sign 1 le_rfl
  have h := this.1
  rw [show ((-1 : ℝ)) ^ (1 + 1) = 1 by norm_num, one_mul] at h
  rw [aE, h]; exact this.2

lemma aE_lt : aE < 16 / (3 * π ^ 3) := by
  have h := (abs_A_bounds 1 le_rfl).2
  have : |A 1| = A 1 := abs_of_pos aE_pos
  rw [aE, ← this]
  calc |A 1| < 4 / (π ^ 3 * ((1 : ℕ) ^ 2 - 1 / 4 : ℝ)) := by exact_mod_cast h
    _ = 16 / (3 * π ^ 3) := by push_cast; field_simp; norm_num

lemma bE_gt : 2 / π < bE := by
  have h := S_min 1 0
  have hS : S 1 π = bE - aE := by simp [S, bE, aE, Real.cos_pi]; ring
  linarith [aE_pos, h.2.2]

/-- **Corollary 3.8** with all hypotheses proved: `b_E > 2 a_E > 0`. -/
theorem convexity_rE : 2 * aE < bE ∧ 0 < 2 * aE :=
  Limacon.convexity_chain aE bE aE_pos aE_lt bE_gt

end EulerianCert.FourierSeries
