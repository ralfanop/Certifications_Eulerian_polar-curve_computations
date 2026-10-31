/-
# V001 Proposition 3.10: logarithmic growth of the total absolute curvature of the truncations

`S_N = A_0/2 + ∑_{n=1}^N A_n cos(nθ)` (module `FourierSeries`), `γ_N(θ) = S_N(θ) e^{iθ}`.
With `S_N'`, `S_N''` written out as trigonometric polynomials, the polar curvature density is
  `k_N = (S_N² + 2 S_N'² − S_N S_N'') / (S_N² + S_N'²)`,
i.e. `κ_N^s ds_N = k_N dθ` (proved here from `Im(conj γ' γ'')/|γ'|²`), and
`TC(Γ_N) = ∫_{−π}^{π} |k_N|`.  Proved here:
* Eq. (53): `S_N'' = (c/2)(D_N(θ − π) − 1) + R_N`, `c = 4/π³`, `sup_N ‖R_N‖_∞ < ∞`;
  `S_N' = c ∑ sin(n(θ − π))/n + (bounded)`, and `sup_N ‖S_N'‖_∞ < ∞`;
* Eq. (55): `w₀‖S_N''‖_{L¹} − 4π ≤ TC(Γ_N) ≤ w₁‖S_N''‖_{L¹} + 4π`;
* **Eq. (52)**: there are `C₁, C₂ > 0` with `C₁ log N ≤ TC(Γ_N) ≤ C₂ log N` for all large `N`;
* **non-convergence**: for none of the three sequences `dτ_N = k_N dθ`, `dμ_N = |k_N| dθ`,
  `dK_N = dT_N` (the derivative of the unit tangent `T_N = γ_N'/|γ_N'|`) do the integrals of every
  continuous function on the parameter circle `ℝ/2πℤ` converge — a fortiori none of them converges
  weak-* to a finite Radon measure.  The proof is the uniform boundedness principle
  (Mathlib's `banach_steinhaus` on the Banach space `C(ℝ/2πℤ, ℝ)`), as in the manuscript.
-/
import EulerianCert.FourierSeries
import EulerianCert.Lebesgue
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.ContinuousMap.Compact

open Real Finset intervalIntegral MeasureTheory Set Filter Topology
open EulerianCert.FourierModes EulerianCert.FourierSeries EulerianCert.Lebesgue

noncomputable section

namespace EulerianCert.CurvatureGrowth

/-! ### Derivatives of the truncations -/

/-- `S_N'`. -/
def S1 (N : ℕ) (θ : ℝ) : ℝ :=
  -∑ n ∈ range N, ((n + 1 : ℕ) : ℝ) * A (n + 1) * Real.sin ((n + 1 : ℕ) * θ)

/-- `S_N''`. -/
def S2 (N : ℕ) (θ : ℝ) : ℝ :=
  -∑ n ∈ range N, ((n + 1 : ℕ) : ℝ) ^ 2 * A (n + 1) * Real.cos ((n + 1 : ℕ) * θ)

lemma hasDerivAt_S (N : ℕ) (θ : ℝ) : HasDerivAt (S N) (S1 N θ) θ := by
  have h : ∀ n ∈ range N, HasDerivAt (fun θ => A (n + 1) * Real.cos ((n + 1 : ℕ) * θ))
      (-(((n + 1 : ℕ) : ℝ) * A (n + 1) * Real.sin ((n + 1 : ℕ) * θ))) θ := by
    intro n _
    have := (((hasDerivAt_id' θ).const_mul ((n + 1 : ℕ) : ℝ)).cos).const_mul (A (n + 1))
    convert this using 1; ring
  have := (HasDerivAt.fun_sum h).const_add (A 0 / 2)
  unfold S S1
  convert this using 1
  rw [Finset.sum_neg_distrib]

lemma hasDerivAt_S1 (N : ℕ) (θ : ℝ) : HasDerivAt (S1 N) (S2 N θ) θ := by
  have h : ∀ n ∈ range N, HasDerivAt
      (fun θ => ((n + 1 : ℕ) : ℝ) * A (n + 1) * Real.sin ((n + 1 : ℕ) * θ))
      (((n + 1 : ℕ) : ℝ) ^ 2 * A (n + 1) * Real.cos ((n + 1 : ℕ) * θ)) θ := by
    intro n _
    have := (((hasDerivAt_id' θ).const_mul ((n + 1 : ℕ) : ℝ)).sin).const_mul
      (((n + 1 : ℕ) : ℝ) * A (n + 1))
    convert this using 1; ring
  have := (HasDerivAt.fun_sum h).neg
  unfold S1 S2
  exact this

lemma continuous_S (N : ℕ) : Continuous (S N) :=
  continuous_iff_continuousAt.mpr (fun θ => (hasDerivAt_S N θ).continuousAt)

lemma continuous_S1 (N : ℕ) : Continuous (S1 N) :=
  continuous_iff_continuousAt.mpr (fun θ => (hasDerivAt_S1 N θ).continuousAt)

lemma continuous_S2 (N : ℕ) : Continuous (S2 N) := by
  unfold S2; fun_prop

lemma S_periodic (N : ℕ) : Function.Periodic (S N) (2 * π) := by
  intro θ; simp only [S, mul_add, cos_add_nat_mul_two_pi]

lemma S1_periodic (N : ℕ) : Function.Periodic (S1 N) (2 * π) := by
  intro θ; simp only [S1, mul_add, sin_add_nat_mul_two_pi]

lemma S2_periodic (N : ℕ) : Function.Periodic (S2 N) (2 * π) := by
  intro θ; simp only [S2, mul_add, cos_add_nat_mul_two_pi]

/-! ### Uniform bounds on `S_N` and `S_N'` -/

lemma S_gt (N : ℕ) (θ : ℝ) : 2 / π < S N θ := by
  obtain ⟨h1, -, h3⟩ := S_min N θ; linarith

lemma S_pos (N : ℕ) (θ : ℝ) : 0 < S N θ := lt_trans (by positivity) (S_gt N θ)

/-- The upper bound `M` of `S_N`. -/
def M : ℝ := |A 0| / 2 + ∑' n, cE n

lemma S_le (N : ℕ) (θ : ℝ) : S N θ ≤ M := by
  unfold S M
  have h1 : ∑ n ∈ range N, A (n + 1) * Real.cos ((n + 1 : ℕ) * θ) ≤ ∑ n ∈ range N, cE n := by
    apply Finset.sum_le_sum
    intro n _
    calc A (n + 1) * Real.cos ((n + 1 : ℕ) * θ) ≤ |A (n + 1) * Real.cos ((n + 1 : ℕ) * θ)| :=
          le_abs_self _
      _ = |A (n + 1)| * |Real.cos ((n + 1 : ℕ) * θ)| := abs_mul _ _
      _ ≤ |A (n + 1)| * 1 := mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg _)
      _ = cE n := by rw [mul_one]; rfl
  have h2 : ∑ n ∈ range N, cE n ≤ ∑' n, cE n :=
    summable_cE.sum_le_tsum _ (fun n _ => cE_nonneg n)
  have h3 : A 0 / 2 ≤ |A 0| / 2 := by linarith [le_abs_self (A 0)]
  linarith

/-- `c = 4/π³`, the leading constant of Eq. (10). -/
def κ0 : ℝ := 4 / π ^ 3

/-- The remainder of Eq. (10): `e_n = A_{n+1} − (−1)^n c/(n+1)²`. -/
def e (n : ℕ) : ℝ := A (n + 1) - (-1 : ℝ) ^ n * κ0 / ((n + 1 : ℕ) : ℝ) ^ 2

lemma abs_e (n : ℕ) : |e n| ≤ 4 / (3 * π ^ 3) * (1 / ((n + 1 : ℕ) : ℝ) ^ 4) := by
  have := A_asymptotic (n + 1) (by omega)
  convert this using 2
  unfold e κ0
  rw [show n + 1 + 1 = n + 2 by ring, pow_add, neg_one_sq, mul_one]
  have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- `T₂ = ∑ 1/(n+1)²`. -/
def T2 : ℝ := ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 2

lemma summable_inv_sq : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
  (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)

lemma partial_le_T2 (N : ℕ) : ∑ n ∈ range N, 1 / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ T2 :=
  summable_inv_sq.sum_le_tsum _ (fun n _ => by positivity)

/-- The uniform constant `ρ = (4/(3π³)) T₂` for both remainders. -/
def ρ : ℝ := 4 / (3 * π ^ 3) * T2

lemma ρ_nonneg : 0 ≤ ρ := by
  unfold ρ T2; exact mul_nonneg (by positivity) (tsum_nonneg (fun n => by positivity))

/-- The remainder `R_N` of Eq. (53). -/
def R2 (N : ℕ) (θ : ℝ) : ℝ :=
  -∑ n ∈ range N, ((n + 1 : ℕ) : ℝ) ^ 2 * e n * Real.cos ((n + 1 : ℕ) * θ)

/-- **Eq. (53)**: `S_N'' = (c/2)(D_N(θ − π) − 1) + R_N`. -/
theorem S2_dirichlet (N : ℕ) (θ : ℝ) : S2 N θ = κ0 / 2 * (D N (θ - π) - 1) + R2 N θ := by
  unfold S2 R2 D
  rw [show κ0 / 2 * (1 + 2 * ∑ n ∈ range N, Real.cos ((n + 1 : ℕ) * (θ - π)) - 1) =
    ∑ n ∈ range N, κ0 * Real.cos ((n + 1 : ℕ) * (θ - π)) by rw [← Finset.mul_sum]; ring]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [mul_sub, cos_sub_nat_mul_pi, pow_succ]
  unfold e
  have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- `sup_N ‖R_N‖_∞ ≤ ρ`. -/
lemma abs_R2 (N : ℕ) (θ : ℝ) : |R2 N θ| ≤ ρ := by
  unfold R2
  rw [abs_neg]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ n ∈ range N, |((n + 1 : ℕ) : ℝ) ^ 2 * e n * Real.cos ((n + 1 : ℕ) * θ)|
      ≤ ∑ n ∈ range N, 4 / (3 * π ^ 3) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro n _
        have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        rw [abs_mul, abs_mul, abs_pow, abs_of_pos hn]
        calc ((n + 1 : ℕ) : ℝ) ^ 2 * |e n| * |Real.cos ((n + 1 : ℕ) * θ)|
            ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * |e n| * 1 :=
              mul_le_mul_of_nonneg_left (abs_cos_le_one _) (by positivity)
          _ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * (4 / (3 * π ^ 3) * (1 / ((n + 1 : ℕ) : ℝ) ^ 4)) := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_left (abs_e n) (by positivity)
          _ = 4 / (3 * π ^ 3) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by field_simp
    _ = 4 / (3 * π ^ 3) * ∑ n ∈ range N, 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ρ := mul_le_mul_of_nonneg_left (partial_le_T2 N) (by positivity)

/-- The remainder of `S_N'`. -/
def R1 (N : ℕ) (θ : ℝ) : ℝ :=
  -∑ n ∈ range N, ((n + 1 : ℕ) : ℝ) * e n * Real.sin ((n + 1 : ℕ) * θ)

lemma σ_eq (N : ℕ) (x : ℝ) :
    σ N x = ∑ n ∈ range N, Real.sin ((n + 1 : ℕ) * x) / ((n + 1 : ℕ) : ℝ) := by
  rw [σ, Finset.sum_Ico_eq_sum_range]
  simp only [add_tsub_cancel_right]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [add_comm 1 n]

/-- `S_N' = c ∑ sin(n(θ − π))/n + R'_N`. -/
theorem S1_sine (N : ℕ) (θ : ℝ) : S1 N θ = κ0 * σ N (θ - π) + R1 N θ := by
  rw [σ_eq]
  unfold S1 R1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [mul_sub, sin_sub_nat_mul_pi, pow_succ]
  unfold e
  have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma abs_R1 (N : ℕ) (θ : ℝ) : |R1 N θ| ≤ ρ := by
  unfold R1
  rw [abs_neg]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ n ∈ range N, |((n + 1 : ℕ) : ℝ) * e n * Real.sin ((n + 1 : ℕ) * θ)|
      ≤ ∑ n ∈ range N, 4 / (3 * π ^ 3) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro n _
        have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
        have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        rw [abs_mul, abs_mul, abs_of_pos hn]
        calc ((n + 1 : ℕ) : ℝ) * |e n| * |Real.sin ((n + 1 : ℕ) * θ)|
            ≤ ((n + 1 : ℕ) : ℝ) * |e n| * 1 :=
              mul_le_mul_of_nonneg_left (abs_sin_le_one _) (by positivity)
          _ ≤ ((n + 1 : ℕ) : ℝ) * (4 / (3 * π ^ 3) * (1 / ((n + 1 : ℕ) : ℝ) ^ 4)) := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_left (abs_e n) (by positivity)
          _ = 4 / (3 * π ^ 3) * (1 / ((n + 1 : ℕ) : ℝ) ^ 3) := by field_simp
          _ ≤ 4 / (3 * π ^ 3) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply one_div_le_one_div_of_le (by positivity)
              exact pow_le_pow_right₀ hn1 (by norm_num)
    _ = 4 / (3 * π ^ 3) * ∑ n ∈ range N, 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ρ := mul_le_mul_of_nonneg_left (partial_le_T2 N) (by positivity)

/-- The uniform bound `B₁` of `S_N'`. -/
def B1 : ℝ := κ0 * (1 + π) + ρ

/-- `sup_N ‖S_N'‖_∞ < ∞`. -/
theorem abs_S1_le (N : ℕ) (θ : ℝ) : |S1 N θ| ≤ B1 := by
  rw [S1_sine]
  have hκ : 0 ≤ κ0 := by unfold κ0; positivity
  calc |κ0 * σ N (θ - π) + R1 N θ| ≤ |κ0 * σ N (θ - π)| + |R1 N θ| := abs_add_le _ _
    _ ≤ κ0 * (1 + π) + ρ := by
        rw [abs_mul, abs_of_nonneg hκ]
        exact add_le_add (mul_le_mul_of_nonneg_left (σ_bound N _) hκ) (abs_R1 N θ)

/-! ### The curvature density and the total absolute curvature -/

/-- The polar curvature density `k_N`, with `κ_N^s ds_N = k_N dθ`. -/
def k (N : ℕ) (θ : ℝ) : ℝ :=
  (S N θ ^ 2 + 2 * S1 N θ ^ 2 - S N θ * S2 N θ) / (S N θ ^ 2 + S1 N θ ^ 2)

/-- The total absolute curvature `TC(Γ_N) = ∫ |κ_N^s| ds_N`. -/
def TC (N : ℕ) : ℝ := ∫ θ in (-π)..π, |k N θ|

lemma den_pos (N : ℕ) (θ : ℝ) : 0 < S N θ ^ 2 + S1 N θ ^ 2 := by
  have := S_pos N θ; positivity

lemma continuous_k (N : ℕ) : Continuous (k N) := by
  unfold k
  have h0 := continuous_S N; have h1 := continuous_S1 N; have h2 := continuous_S2 N
  exact Continuous.div (by fun_prop) (by fun_prop) (fun θ => (den_pos N θ).ne')

lemma k_periodic (N : ℕ) : Function.Periodic (k N) (2 * π) := by
  intro θ; simp only [k, S_periodic N θ, S1_periodic N θ, S2_periodic N θ]

/-- The lower constant `w₀` of Eq. (54). -/
def w0 : ℝ := (2 / π) / (M ^ 2 + B1 ^ 2)

lemma M_pos : 0 < M := lt_of_lt_of_le (S_pos 0 0) (S_le 0 0)

lemma w0_pos : 0 < w0 := by unfold w0; have := M_pos; positivity

/-- Eqs. (54)–(55), pointwise: `w₀|S''| − 2 ≤ |k_N| ≤ 2 + (π/2)|S''|`. -/
lemma k_bounds (N : ℕ) (θ : ℝ) :
    w0 * |S2 N θ| - 2 ≤ |k N θ| ∧ |k N θ| ≤ 2 + π / 2 * |S2 N θ| := by
  set s := S N θ; set d := S1 N θ; set q := S2 N θ
  have hs : 2 / π < s := S_gt N θ
  have hs0 : 0 < s := S_pos N θ
  have hsM : s ≤ M := S_le N θ
  have hd : |d| ≤ B1 := abs_S1_le N θ
  set P := s ^ 2 + d ^ 2
  have hP : 0 < P := den_pos N θ
  have hk : k N θ = (s ^ 2 + 2 * d ^ 2) / P - s / P * q := by
    show (s ^ 2 + 2 * d ^ 2 - s * q) / P = _
    field_simp
  have hX0 : 0 ≤ (s ^ 2 + 2 * d ^ 2) / P := by positivity
  have hX : (s ^ 2 + 2 * d ^ 2) / P ≤ 2 := by
    rw [div_le_iff₀ hP]; nlinarith [sq_nonneg s]
  have hY : s / P ≤ π / 2 := by
    rw [div_le_iff₀ hP]
    have : 2 / π * (s / P) ≤ 1 := by
      rw [show 2 / π * (s / P) = (2 / π) * s / P by ring, div_le_one hP]
      have : 2 / π * s ≤ s * s := mul_le_mul_of_nonneg_right hs.le hs0.le
      nlinarith [sq_nonneg d]
    have hπ := pi_pos
    have h2 : s ≤ π / 2 * P := by
      have := this
      rw [show 2 / π * (s / P) = s / (π / 2 * P) by field_simp] at this
      rwa [div_le_one (by positivity)] at this
    linarith
  have hW : w0 ≤ s / P := by
    unfold w0
    have hd2 : d ^ 2 ≤ B1 ^ 2 := by
      have := sq_le_sq' (abs_le.mp hd).1 (abs_le.mp hd).2; simpa using this
    have hs2 : s ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hs0.le hsM 2
    have hMB : 0 < M ^ 2 + B1 ^ 2 := by have := M_pos; positivity
    rw [div_le_div_iff₀ hMB hP]
    calc 2 / π * P ≤ s * P := mul_le_mul_of_nonneg_right hs.le hP.le
      _ ≤ s * (M ^ 2 + B1 ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hs0.le
  have hYq : |s / P * q| = s / P * |q| := by rw [abs_mul, abs_of_pos (by positivity)]
  rw [hk]
  constructor
  · have := abs_sub_abs_le_abs_sub (s / P * q) ((s ^ 2 + 2 * d ^ 2) / P)
    rw [abs_sub_comm] at this
    rw [hYq, abs_of_nonneg hX0] at this
    nlinarith [mul_le_mul_of_nonneg_right hW (abs_nonneg q)]
  · calc |(s ^ 2 + 2 * d ^ 2) / P - s / P * q| ≤ |(s ^ 2 + 2 * d ^ 2) / P| + |s / P * q| :=
          abs_sub _ _
      _ ≤ 2 + π / 2 * |q| := by
          rw [hYq, abs_of_nonneg hX0]
          exact add_le_add hX (mul_le_mul_of_nonneg_right hY (abs_nonneg q))

/-- `‖S_N''‖_{L¹}`. -/
def I2 (N : ℕ) : ℝ := ∫ θ in (-π)..π, |S2 N θ|

lemma integral_D_shift (N : ℕ) : ∫ θ in (-π)..π, |D N (θ - π)| = L N := by
  rw [intervalIntegral.integral_comp_sub_right (fun x => |D N x|) π]
  have hper : Function.Periodic (fun x => |D N x|) (2 * π) := fun x => by
    simp only [D_periodic N x]
  have := hper.intervalIntegral_add_eq (-π - π) (-π)
  unfold L
  convert this using 2 <;> ring

/-- **Eq. (55)**: `w₀‖S_N''‖_{L¹} − 4π ≤ TC(Γ_N) ≤ (π/2)‖S_N''‖_{L¹} + 4π`. -/
theorem TC_bounds (N : ℕ) : w0 * I2 N - 4 * π ≤ TC N ∧ TC N ≤ π / 2 * I2 N + 4 * π := by
  have hi : ∀ a b, IntervalIntegrable (fun θ => |S2 N θ|) volume a b :=
    fun a b => (continuous_S2 N).abs.intervalIntegrable a b
  have hk : ∀ a b, IntervalIntegrable (fun θ => |k N θ|) volume a b :=
    fun a b => (continuous_k N).abs.intervalIntegrable a b
  have hpi : -π ≤ π := by linarith [pi_pos]
  constructor
  · calc w0 * I2 N - 4 * π = ∫ θ in (-π)..π, (w0 * |S2 N θ| - 2) := by
          rw [intervalIntegral.integral_sub ((hi _ _).const_mul _) intervalIntegrable_const,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
          unfold I2; ring
      _ ≤ TC N := intervalIntegral.integral_mono_on hpi
          (((hi _ _).const_mul _).sub intervalIntegrable_const) (hk _ _)
          (fun θ _ => (k_bounds N θ).1)
  · calc TC N ≤ ∫ θ in (-π)..π, (2 + π / 2 * |S2 N θ|) :=
          intervalIntegral.integral_mono_on hpi (hk _ _)
            (intervalIntegrable_const.add ((hi _ _).const_mul _)) (fun θ _ => (k_bounds N θ).2)
      _ = π / 2 * I2 N + 4 * π := by
          rw [intervalIntegral.integral_add intervalIntegrable_const ((hi _ _).const_mul _),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
          unfold I2; ring

/-- `‖S_N''‖_{L¹} ≍ L_N`: `(c/2)L_N − 2π(c/2 + ρ) ≤ ‖S_N''‖_{L¹} ≤ (c/2)L_N + 2π(c/2 + ρ)`. -/
theorem I2_bounds (N : ℕ) :
    κ0 / 2 * L N - 2 * π * (κ0 / 2 + ρ) ≤ I2 N ∧ I2 N ≤ κ0 / 2 * L N + 2 * π * (κ0 / 2 + ρ) := by
  have hκ : 0 ≤ κ0 := by unfold κ0; positivity
  have hD : ∀ a b, IntervalIntegrable (fun θ => |D N (θ - π)|) volume a b :=
    fun a b => ((continuous_D N).comp (continuous_id.sub continuous_const)).abs.intervalIntegrable a b
  have hi : ∀ a b, IntervalIntegrable (fun θ => |S2 N θ|) volume a b :=
    fun a b => (continuous_S2 N).abs.intervalIntegrable a b
  have hpi : -π ≤ π := by linarith [pi_pos]
  have hpt : ∀ θ, κ0 / 2 * |D N (θ - π)| - (κ0 / 2 + ρ) ≤ |S2 N θ| ∧
      |S2 N θ| ≤ κ0 / 2 * |D N (θ - π)| + (κ0 / 2 + ρ) := by
    intro θ
    rw [S2_dirichlet]
    have hR := abs_R2 N θ
    have e1 : κ0 / 2 * (D N (θ - π) - 1) + R2 N θ = κ0 / 2 * D N (θ - π) + (R2 N θ - κ0 / 2) := by
      ring
    have hc : |R2 N θ - κ0 / 2| ≤ κ0 / 2 + ρ := by
      calc |R2 N θ - κ0 / 2| ≤ |R2 N θ| + |κ0 / 2| := abs_sub _ _
        _ ≤ ρ + κ0 / 2 := by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ κ0 / 2)]; linarith
        _ = κ0 / 2 + ρ := by ring
    have hm : |κ0 / 2 * D N (θ - π)| = κ0 / 2 * |D N (θ - π)| := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ κ0 / 2)]
    rw [e1]
    constructor
    · have := abs_sub_abs_le_abs_sub (κ0 / 2 * D N (θ - π)) (-(R2 N θ - κ0 / 2))
      rw [sub_neg_eq_add, abs_neg, hm] at this; linarith
    · calc |κ0 / 2 * D N (θ - π) + (R2 N θ - κ0 / 2)|
          ≤ |κ0 / 2 * D N (θ - π)| + |R2 N θ - κ0 / 2| := abs_add_le _ _
        _ ≤ κ0 / 2 * |D N (θ - π)| + (κ0 / 2 + ρ) := by rw [hm]; linarith
  have hL := integral_D_shift N
  constructor
  · calc κ0 / 2 * L N - 2 * π * (κ0 / 2 + ρ) =
          ∫ θ in (-π)..π, (κ0 / 2 * |D N (θ - π)| - (κ0 / 2 + ρ)) := by
          rw [intervalIntegral.integral_sub ((hD _ _).const_mul _) intervalIntegrable_const,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul, hL]
          ring
      _ ≤ I2 N := intervalIntegral.integral_mono_on hpi
          (((hD _ _).const_mul _).sub intervalIntegrable_const) (hi _ _) (fun θ _ => (hpt θ).1)
  · calc I2 N ≤ ∫ θ in (-π)..π, (κ0 / 2 * |D N (θ - π)| + (κ0 / 2 + ρ)) :=
          intervalIntegral.integral_mono_on hpi (hi _ _)
            (((hD _ _).const_mul _).add intervalIntegrable_const) (fun θ _ => (hpt θ).2)
      _ = κ0 / 2 * L N + 2 * π * (κ0 / 2 + ρ) := by
          rw [intervalIntegral.integral_add ((hD _ _).const_mul _) intervalIntegrable_const,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul, hL]
          ring

/-- **Proposition 3.10, Eq. (52)**: `C₁ log N ≤ TC(Γ_N) ≤ C₂ log N` for all sufficiently large
`N`. -/
theorem curvature_growth :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ N : ℕ in atTop,
      C₁ * Real.log N ≤ TC N ∧ TC N ≤ C₂ * Real.log N := by
  have hκ : 0 < κ0 := by unfold κ0; positivity
  have hρ := ρ_nonneg
  have hw := w0_pos
  have hπ := pi_pos
  set K := 2 * π * (κ0 / 2 + ρ)
  -- lower: TC ≥ α log N − K₁
  set α := w0 * (κ0 / 2) * (4 / π)
  set K₁ := w0 * K + 4 * π
  have hα : 0 < α := by positivity
  -- upper: TC ≤ β log N + K₂
  set β := π / 2 * (κ0 / 2) * (2 * π)
  set K₂ := π / 2 * (κ0 / 2) * (2 * π) * (1 + Real.log 3) + π / 2 * K + 4 * π
  have hβ : 0 < β := by positivity
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨α / 2, β + 1, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 1, hlog.eventually_ge_atTop (2 * K₁ / α),
    hlog.eventually_ge_atTop K₂] with N hN h1 h2
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hT1, hT2⟩ := TC_bounds N
  obtain ⟨hI1, hI2⟩ := I2_bounds N
  have hL1 := L_lower N
  have hL2 := L_upper N
  have hlogN : Real.log N ≤ Real.log (N + 1) := Real.log_le_log (by linarith) (by linarith)
  have hlog3 : Real.log (2 * N + 1) ≤ Real.log 3 + Real.log N := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  constructor
  · have hlow : α * Real.log N - K₁ ≤ TC N := by
      have : α * Real.log N ≤ w0 * (κ0 / 2 * L N) := by
        calc α * Real.log N = w0 * (κ0 / 2) * (4 / π * Real.log N) := by ring
          _ ≤ w0 * (κ0 / 2) * (4 / π * Real.log (N + 1)) := by gcongr
          _ ≤ w0 * (κ0 / 2) * L N := by gcongr
          _ = w0 * (κ0 / 2 * L N) := by ring
      have hI1' : κ0 / 2 * L N - K ≤ I2 N := hI1
      have hK1 : K₁ = w0 * K + 4 * π := rfl
      have := mul_le_mul_of_nonneg_left hI1' hw.le
      linarith
    have : K₁ ≤ α / 2 * Real.log N := by
      have := (div_le_iff₀ hα).mp h1
      linarith
    linarith
  · have hup : TC N ≤ β * Real.log N + K₂ := by
      have hLN : L N ≤ 2 * π * (1 + (Real.log 3 + Real.log N)) := by
        calc L N ≤ 2 * π * (1 + Real.log (2 * N + 1)) := hL2
          _ ≤ 2 * π * (1 + (Real.log 3 + Real.log N)) := by gcongr
      have hI2' : I2 N ≤ κ0 / 2 * L N + K := hI2
      have : I2 N ≤ κ0 / 2 * (2 * π * (1 + (Real.log 3 + Real.log N))) + K :=
        le_trans hI2' (by gcongr)
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ π / 2)
      have hb : β = π / 2 * (κ0 / 2) * (2 * π) := rfl
      have hK2 : K₂ = π / 2 * (κ0 / 2) * (2 * π) * (1 + Real.log 3) + π / 2 * K + 4 * π := rfl
      rw [hK2, hb]
      linarith
    linarith

/-! ### The curve `γ_N`, the curvature identity and the unit tangent -/

/-- `γ_N(θ) = S_N(θ) e^{iθ}`. -/
def γ (N : ℕ) (θ : ℝ) : ℂ := (S N θ : ℂ) * Complex.exp (θ * Complex.I)

/-- `γ_N'`. -/
def γ1 (N : ℕ) (θ : ℝ) : ℂ :=
  ((S1 N θ : ℂ) + S N θ * Complex.I) * Complex.exp (θ * Complex.I)

/-- `γ_N''`. -/
def γ2 (N : ℕ) (θ : ℝ) : ℂ :=
  ((S2 N θ : ℂ) - S N θ + 2 * S1 N θ * Complex.I) * Complex.exp (θ * Complex.I)

lemma hasDerivAt_cexp (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (t * Complex.I))
      (Complex.exp (θ * Complex.I) * Complex.I) θ := by
  have h := ((hasDerivAt_id' θ).ofReal_comp.mul_const Complex.I).cexp
  convert h using 1; simp

lemma hasDerivAt_γ (N : ℕ) (θ : ℝ) : HasDerivAt (γ N) (γ1 N θ) θ := by
  have := (hasDerivAt_S N θ).ofReal_comp.mul (hasDerivAt_cexp θ)
  exact this.congr_deriv (by unfold γ1; ring)

lemma hasDerivAt_γ1 (N : ℕ) (θ : ℝ) : HasDerivAt (γ1 N) (γ2 N θ) θ := by
  have := ((hasDerivAt_S1 N θ).ofReal_comp.add
    ((hasDerivAt_S N θ).ofReal_comp.mul_const Complex.I)).mul (hasDerivAt_cexp θ)
  exact this.congr_deriv (by
    unfold γ2
    simp only [Pi.add_apply]
    linear_combination (S N θ : ℂ) * Complex.exp (θ * Complex.I) * Complex.I_sq)

/-- **The polar curvature identity**: `k_N = Im(conj γ_N' · γ_N'') / |γ_N'|²`, i.e.
`k_N dθ = κ_N^s ds_N` (signed curvature `Im(conj γ' γ'')/|γ'|³`, arclength `|γ'| dθ`). -/
theorem k_eq (N : ℕ) (θ : ℝ) :
    k N θ = ((starRingEnd ℂ) (γ1 N θ) * γ2 N θ).im / ‖γ1 N θ‖ ^ 2 := by
  have hE : (starRingEnd ℂ) (Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I) = 1 := by
    rw [Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]; simp
  have h1 : (starRingEnd ℂ) (γ1 N θ) * γ2 N θ =
      (starRingEnd ℂ) ((S1 N θ : ℂ) + S N θ * Complex.I) *
        ((S2 N θ : ℂ) - S N θ + 2 * S1 N θ * Complex.I) := by
    unfold γ1 γ2
    rw [map_mul]
    linear_combination ((starRingEnd ℂ) ((S1 N θ : ℂ) + S N θ * Complex.I) *
        ((S2 N θ : ℂ) - S N θ + 2 * S1 N θ * Complex.I)) * hE
  have h2 : ‖γ1 N θ‖ ^ 2 = S N θ ^ 2 + S1 N θ ^ 2 := by
    unfold γ1
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.sq_norm, Complex.normSq_apply]
    simp; ring
  rw [h1, h2]
  unfold k
  congr 1
  simp [Complex.mul_im]
  ring

/-- The unit tangent `T_N = γ_N'/|γ_N'|`. -/
def T (N : ℕ) (θ : ℝ) : ℂ := γ1 N θ / (‖γ1 N θ‖ : ℂ)

/-- The tangent angle minus `π/2`: `g_N = θ − arctan(S_N'/S_N)`. -/
def g (N : ℕ) (θ : ℝ) : ℝ := θ - Real.arctan (S1 N θ / S N θ)

lemma norm_γ1 (N : ℕ) (θ : ℝ) : ‖γ1 N θ‖ = √(S N θ ^ 2 + S1 N θ ^ 2) := by
  unfold γ1
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_def, Complex.normSq_apply]
  congr 1; simp; ring

/-- `(d + i s) e^{iθ} / |d + i s| = i e^{i(θ − arctan(d/s))}` for `s > 0`. -/
lemma unit_vec (s d θ : ℝ) (hs : 0 < s) :
    ((d : ℂ) + s * Complex.I) * Complex.exp (θ * Complex.I) / ((√(s ^ 2 + d ^ 2) : ℝ) : ℂ) =
      Complex.I * Complex.exp (((θ - Real.arctan (d / s) : ℝ) : ℂ) * Complex.I) := by
  have hP : 0 < s ^ 2 + d ^ 2 := by positivity
  have hr : 0 < √(s ^ 2 + d ^ 2) := Real.sqrt_pos.mpr hP
  have hr2 : √(s ^ 2 + d ^ 2) ^ 2 = s ^ 2 + d ^ 2 := Real.sq_sqrt hP.le
  have hsq : √(1 + (d / s) ^ 2) = √(s ^ 2 + d ^ 2) / s := by
    rw [show 1 + (d / s) ^ 2 = (√(s ^ 2 + d ^ 2) / s) ^ 2 by
      rw [div_pow √(s ^ 2 + d ^ 2) s 2, hr2]; field_simp]
    exact Real.sqrt_sq (by positivity)
  have hcos : Real.cos (Real.arctan (d / s)) = s / √(s ^ 2 + d ^ 2) := by
    rw [Real.cos_arctan, hsq]; field_simp
  have hsin : Real.sin (Real.arctan (d / s)) = d / √(s ^ 2 + d ^ 2) := by
    rw [Real.sin_arctan, hsq]; field_simp
  have hexp : Complex.exp (((θ - Real.arctan (d / s) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (θ * Complex.I) * ((s / √(s ^ 2 + d ^ 2) : ℝ) -
        ((d / √(s ^ 2 + d ^ 2) : ℝ) : ℂ) * Complex.I) := by
    rw [show ((θ - Real.arctan (d / s) : ℝ) : ℂ) * Complex.I =
      (θ : ℂ) * Complex.I + ((-Real.arctan (d / s) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_add]
    congr 1
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
      hcos, hsin]
    push_cast; ring
  rw [hexp]
  have hr0 : ((√(s ^ 2 + d ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  linear_combination (Complex.exp (θ * Complex.I) * d / ((√(s ^ 2 + d ^ 2) : ℝ) : ℂ)) *
    Complex.I_sq

lemma T_eq (N : ℕ) (θ : ℝ) :
    T N θ = Complex.I * Complex.exp ((g N θ : ℂ) * Complex.I) := by
  unfold T g
  rw [norm_γ1]
  exact unit_vec _ _ _ (S_pos N θ)

lemma hasDerivAt_g (N : ℕ) (θ : ℝ) : HasDerivAt (g N) (k N θ) θ := by
  have hs := S_pos N θ
  have hu := (hasDerivAt_S1 N θ).div (hasDerivAt_S N θ) hs.ne'
  have := (hasDerivAt_id' θ).sub hu.arctan
  unfold g
  convert this using 1
  simp only [Pi.div_apply]
  unfold k
  have := den_pos N θ
  field_simp
  ring

/-- The Frenet relation `dT_N/dθ = i k_N T_N`. -/
theorem hasDerivAt_T (N : ℕ) (θ : ℝ) :
    HasDerivAt (T N) (Complex.I * k N θ * T N θ) θ := by
  have hT : T N = fun t => Complex.I * Complex.exp ((g N t : ℂ) * Complex.I) :=
    funext (T_eq N)
  have := (((hasDerivAt_g N θ).ofReal_comp.mul_const Complex.I).cexp).const_mul Complex.I
  rw [hT]
  convert this using 1
  ring

lemma deriv_T (N : ℕ) : deriv (T N) = fun θ => Complex.I * k N θ * T N θ :=
  funext (fun θ => (hasDerivAt_T N θ).deriv)

lemma norm_T (N : ℕ) (θ : ℝ) : ‖T N θ‖ = 1 := by
  rw [T_eq, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma continuous_g (N : ℕ) : Continuous (g N) :=
  continuous_id.sub (Real.continuous_arctan.comp
    ((continuous_S1 N).div (continuous_S N) (fun θ => (S_pos N θ).ne')))

lemma continuous_T (N : ℕ) : Continuous (T N) := by
  rw [show T N = fun t => Complex.I * Complex.exp ((g N t : ℂ) * Complex.I) from funext (T_eq N)]
  have := continuous_g N
  fun_prop

lemma T_periodic (N : ℕ) : Function.Periodic (T N) (2 * π) := by
  intro θ
  rw [T_eq, T_eq]
  have hg : g N (θ + 2 * π) = g N θ + 2 * π := by
    unfold g; rw [S_periodic N θ, S1_periodic N θ]; ring
  rw [hg]
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-! ### Non-convergence (uniform boundedness principle) -/

/-- **Uniform boundedness**: if `∫ f g_N` converges for every continuous `f` on `ℝ/2πℤ`, then
`sup_N ∫|g_N| < ∞`. -/
theorem bounded_of_converges (G : ℕ → ℝ → ℝ) (hG : ∀ N, Continuous (G N))
    (hper : ∀ N, Function.Periodic (G N) (2 * π))
    (h : ∀ f : C(AddCircle (2 * π), ℝ), ∃ l : ℝ,
      Tendsto (fun N => ∫ θ in (-π)..π, f θ * G N θ) atTop (𝓝 l)) :
    ∃ C, ∀ N, ∫ θ in (-π)..π, |G N θ| ≤ C := by
  have hcoe : Continuous (fun θ : ℝ => (θ : AddCircle (2 * π))) := AddCircle.continuous_mk' _
  have hint : ∀ (f : C(AddCircle (2 * π), ℝ)) N,
      IntervalIntegrable (fun θ : ℝ => f θ * G N θ) volume (-π) π :=
    fun f N => ((f.continuous.comp hcoe).mul (hG N)).intervalIntegrable _ _
  have hpi : -π ≤ π := by linarith [pi_pos]
  let Λ : ℕ → C(AddCircle (2 * π), ℝ) →L[ℝ] ℝ := fun N =>
    LinearMap.mkContinuous
      { toFun := fun f => ∫ θ in (-π)..π, f θ * G N θ
        map_add' := fun f f' => by
          simp only [ContinuousMap.add_apply, add_mul]
          exact intervalIntegral.integral_add (hint f N) (hint f' N)
        map_smul' := fun c f => by
          simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
          exact intervalIntegral.integral_const_mul c _ }
      (∫ θ in (-π)..π, |G N θ|)
      (fun f => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        calc ‖∫ θ in (-π)..π, f θ * G N θ‖ ≤ ∫ θ in (-π)..π, ‖f‖ * |G N θ| := by
              apply intervalIntegral.norm_integral_le_of_norm_le hpi
              · exact Filter.Eventually.of_forall (fun θ _ => by
                  rw [norm_mul, Real.norm_eq_abs (G N θ)]
                  exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (abs_nonneg _))
              · exact ((hG N).abs.intervalIntegrable _ _).const_mul _
          _ = (∫ θ in (-π)..π, |G N θ|) * ‖f‖ := by
              rw [intervalIntegral.integral_const_mul, mul_comm])
  have hΛ : ∀ N f, Λ N f = ∫ θ in (-π)..π, f θ * G N θ := fun N f => rfl
  have hb : ∀ f, ∃ C, ∀ N, ‖Λ N f‖ ≤ C := by
    intro f
    obtain ⟨l, hl⟩ := h f
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ hl)
    exact ⟨C, fun N => by rw [hΛ]; exact hC _ ⟨N, rfl⟩⟩
  obtain ⟨C', hC'⟩ := banach_steinhaus hb
  refine ⟨C' + 2 * π, fun N => ?_⟩
  have hq : Function.Periodic (fun θ => G N θ / (|G N θ| + 1)) (2 * π) := fun θ => by
    simp only [hper N θ]
  have hqc : Continuous (fun θ => G N θ / (|G N θ| + 1)) :=
    (hG N).div ((hG N).abs.add continuous_const) (fun θ => by positivity)
  let fN : C(AddCircle (2 * π), ℝ) := ⟨fun x => hq.lift x, continuous_coinduced_dom.mpr hqc⟩
  have hfN : ∀ θ : ℝ, fN θ = G N θ / (|G N θ| + 1) := fun θ => rfl
  have hfN1 : ‖fN‖ ≤ 1 := by
    refine (ContinuousMap.norm_le fN zero_le_one).mpr (fun x => ?_)
    induction x using QuotientAddGroup.induction_on with
    | H θ =>
      show ‖G N θ / (|G N θ| + 1)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < |G N θ| + 1),
        div_le_one (by positivity)]
      linarith
  have hlow : (∫ θ in (-π)..π, |G N θ|) - 2 * π ≤ Λ N fN := by
    rw [hΛ]
    calc (∫ θ in (-π)..π, |G N θ|) - 2 * π = ∫ θ in (-π)..π, (|G N θ| - 1) := by
          rw [intervalIntegral.integral_sub ((hG N).abs.intervalIntegrable _ _)
            intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
          ring
      _ ≤ ∫ θ in (-π)..π, fN θ * G N θ := by
          apply intervalIntegral.integral_mono_on hpi
            (((hG N).abs.intervalIntegrable _ _).sub intervalIntegrable_const) (hint fN N)
          intro θ _
          rw [hfN, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          nlinarith [sq_abs (G N θ), abs_nonneg (G N θ)]
  have h1 := (Λ N).le_opNorm fN
  have h2 : ‖Λ N‖ * ‖fN‖ ≤ C' := by
    calc ‖Λ N‖ * ‖fN‖ ≤ ‖Λ N‖ * 1 := mul_le_mul_of_nonneg_left hfN1 (norm_nonneg (Λ N))
      _ ≤ C' := by rw [mul_one]; exact hC' N
  have h3 : Λ N fN ≤ ‖Λ N fN‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
  linarith

/-- `TC(Γ_N) → ∞`. -/
theorem TC_tendsto : Tendsto TC atTop atTop := by
  obtain ⟨C₁, C₂, h1, -, hev⟩ := curvature_growth
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono' atTop (hev.mono fun N h => h.1) (hlog.const_mul_atTop h1)

theorem TC_unbounded : ¬ ∃ C, ∀ N, TC N ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨N, hN⟩ := (TC_tendsto.eventually_gt_atTop C).exists
  linarith [hC N]

/-- **Prop. 3.10, signed turning measures** `dτ_N = κ_N^s ds_N = k_N dθ`: the integrals against
continuous functions on the parameter circle do not all converge. -/
theorem turning_not_converge :
    ¬ ∀ f : C(AddCircle (2 * π), ℝ), ∃ l : ℝ,
      Tendsto (fun N => ∫ θ in (-π)..π, f θ * k N θ) atTop (𝓝 l) := fun h =>
  TC_unbounded (bounded_of_converges k continuous_k k_periodic h)

/-- **Prop. 3.10, absolute curvature measures** `dμ_N = |κ_N^s| ds_N = |k_N| dθ`. -/
theorem abs_curvature_not_converge :
    ¬ ∀ f : C(AddCircle (2 * π), ℝ), ∃ l : ℝ,
      Tendsto (fun N => ∫ θ in (-π)..π, f θ * |k N θ|) atTop (𝓝 l) := by
  intro h
  obtain ⟨C, hC⟩ := bounded_of_converges (fun N θ => |k N θ|) (fun N => (continuous_k N).abs)
    (fun N θ => by simp only [k_periodic N θ]) h
  refine TC_unbounded ⟨C, fun N => ?_⟩
  have := hC N
  simp only [abs_abs] at this
  exact this

lemma re_integral (f : ℝ → ℝ) (z : ℝ → ℂ) (hf : Continuous f) (hz : Continuous z) :
    (∫ θ in (-π)..π, (f θ : ℂ) * z θ).re = ∫ θ in (-π)..π, f θ * (z θ).re := by
  have hi : IntervalIntegrable (fun θ => (f θ : ℂ) * z θ) volume (-π) π :=
    ((Complex.continuous_ofReal.comp hf).mul hz).intervalIntegrable _ _
  rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hi]
  simp

lemma im_integral (f : ℝ → ℝ) (z : ℝ → ℂ) (hf : Continuous f) (hz : Continuous z) :
    (∫ θ in (-π)..π, (f θ : ℂ) * z θ).im = ∫ θ in (-π)..π, f θ * (z θ).im := by
  have hi : IntervalIntegrable (fun θ => (f θ : ℂ) * z θ) volume (-π) π :=
    ((Complex.continuous_ofReal.comp hf).mul hz).intervalIntegrable _ _
  rw [← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm hi]
  simp

/-- **Prop. 3.10, vector curvature measures** `dK_N = dT_N = T_N'(θ) dθ`. -/
theorem vector_curvature_not_converge :
    ¬ ∀ f : C(AddCircle (2 * π), ℝ), ∃ l : ℂ,
      Tendsto (fun N => ∫ θ in (-π)..π, (f θ : ℂ) * deriv (T N) θ) atTop (𝓝 l) := by
  intro h
  have hcoe : Continuous (fun θ : ℝ => (θ : AddCircle (2 * π))) := AddCircle.continuous_mk' _
  set z : ℕ → ℝ → ℂ := fun N θ => Complex.I * k N θ * T N θ with hz
  have hzc : ∀ N, Continuous (z N) := fun N => by
    have := continuous_k N; have := continuous_T N
    simp only [hz]; fun_prop
  have hzp : ∀ N, Function.Periodic (z N) (2 * π) := fun N θ => by
    simp only [hz, k_periodic N θ, T_periodic N θ]
  have hre : ∀ f : C(AddCircle (2 * π), ℝ), ∃ l : ℝ,
      Tendsto (fun N => ∫ θ in (-π)..π, f θ * (z N θ).re) atTop (𝓝 l) := by
    intro f
    obtain ⟨l, hl⟩ := h f
    refine ⟨l.re, ?_⟩
    have := (Complex.continuous_re.tendsto l).comp hl
    convert this using 1
    funext N
    simp only [Function.comp, deriv_T]
    exact (re_integral (fun θ : ℝ => f θ) (z N) (f.continuous.comp hcoe) (hzc N)).symm
  have him : ∀ f : C(AddCircle (2 * π), ℝ), ∃ l : ℝ,
      Tendsto (fun N => ∫ θ in (-π)..π, f θ * (z N θ).im) atTop (𝓝 l) := by
    intro f
    obtain ⟨l, hl⟩ := h f
    refine ⟨l.im, ?_⟩
    have := (Complex.continuous_im.tendsto l).comp hl
    convert this using 1
    funext N
    simp only [Function.comp, deriv_T]
    exact (im_integral (fun θ : ℝ => f θ) (z N) (f.continuous.comp hcoe) (hzc N)).symm
  obtain ⟨Ca, hCa⟩ := bounded_of_converges (fun N θ => (z N θ).re)
    (fun N => Complex.continuous_re.comp (hzc N)) (fun N θ => by simp only [hzp N θ]) hre
  obtain ⟨Cb, hCb⟩ := bounded_of_converges (fun N θ => (z N θ).im)
    (fun N => Complex.continuous_im.comp (hzc N)) (fun N θ => by simp only [hzp N θ]) him
  refine TC_unbounded ⟨Ca + Cb, fun N => ?_⟩
  have hpi : -π ≤ π := by linarith [pi_pos]
  calc TC N ≤ ∫ θ in (-π)..π, (|(z N θ).re| + |(z N θ).im|) := by
        apply intervalIntegral.integral_mono_on hpi ((continuous_k N).abs.intervalIntegrable _ _)
          (((Complex.continuous_re.comp (hzc N)).abs.add
            (Complex.continuous_im.comp (hzc N)).abs).intervalIntegrable _ _)
        intro θ _
        have hn : ‖z N θ‖ = |k N θ| := by
          simp only [hz]
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul, norm_T, mul_one, Complex.norm_real,
            Real.norm_eq_abs]
        rw [← hn]
        exact Complex.norm_le_abs_re_add_abs_im _
    _ = (∫ θ in (-π)..π, |(z N θ).re|) + ∫ θ in (-π)..π, |(z N θ).im| :=
        intervalIntegral.integral_add
          ((Complex.continuous_re.comp (hzc N)).abs.intervalIntegrable _ _)
          ((Complex.continuous_im.comp (hzc N)).abs.intervalIntegrable _ _)
    _ ≤ Ca + Cb := add_le_add (hCa N) (hCb N)

/-- The contrast in Prop. 3.10: `d_H(Γ_E, Γ_N) = E_N → 0`. -/
theorem hausdorff_tendsto :
    Tendsto (fun N => Metric.hausdorffDist (polarCurve rE) (polarCurve (S N))) atTop (𝓝 0) := by
  simp_rw [fun N => (sharp_truncation N).2.2]
  have h2N : Tendsto (fun N : ℕ => (2 : ℝ) * N + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
  have := (tendsto_const_nhds (x := (2 / π) ^ 3)).div_atTop h2N
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this
    (fun N => (EN_pos N).le) (fun N => (EN_lt N).le)

end EulerianCert.CurvatureGrowth
