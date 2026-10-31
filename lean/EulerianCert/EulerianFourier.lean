/-
# V001 §3.11, Eqs. (80)–(81): the Eulerian densities and Fourier inversion

`D = n + 1`.  Let `X_1, …, X_D` be independent and uniform on `[0, 1]`; `Y_j = X_j − ½`.
With `U_n` the B-spline numerator of `CubeSlabs`:
* `∫₀ˣ U_n/n! = Vol_D{x ∈ [0,1]^D : ∑ x ≤ x}` (`x ≥ 0`), i.e. `U_n/n!` is the density of
  `X_1 + ⋯ + X_D`, and `g_D(s) = U_n(s + D/2)/n!` is the density of `Y_1 + ⋯ + Y_D`;
* the samples: `p_{n,k} = E(n,k−1)/n! = g_D(k − D/2)`;
* `g_{D+1}(s) = ∫_{−½}^{½} g_D(s − y) dy`;
* **Eq. (80)**: `ĝ_D(t) = ∫_ℝ g_D(s) e^{its} ds = r_E(t)^D` for every real `t`;
* **Eq. (81)** (Fourier inversion, `D ≥ 2`):
  `p_{n,k} = E(n,k−1)/n! = (1/2π) ∫_ℝ r_E(t)^{n+1} cos(t(k − (n+1)/2)) dt`.
Here `r_E(t) = sinc(t/2) = 2 sin(t/2)/t` on all of `ℝ` (module `FourierModes`).
-/
import EulerianCert.CubeSlabs
import EulerianCert.FourierModes
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

open Real MeasureTheory Set Filter Topology Finset
open scoped FourierTransform
open EulerianCert.CubeSlabs

noncomputable section

namespace EulerianCert.EulerianFourier

local notation "rE" => EulerianCert.FourierModes.rE

/-! ### Properties of `U_n` and `IH_n` -/

lemma U_of_neg (m : ℕ) {x : ℝ} (hx : x < 0) : U m x = 0 := by
  unfold U
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [tp_of_neg (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
                    linarith), mul_zero]

lemma U_of_nonpos {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : x ≤ 0) : U m x = 0 := by
  rcases hx.lt_or_eq with h | h
  · exact U_of_neg m h
  · rw [h]; exact U_at_zero hm

lemma measurable_U (m : ℕ) : Measurable (U m) := by
  unfold U
  exact Finset.measurable_sum _ (fun j _ =>
    measurable_const.mul ((measurable_tp m).comp (measurable_id.sub measurable_const)))

lemma continuous_U {m : ℕ} (hm : 1 ≤ m) : Continuous (U m) := by
  unfold U; have := continuous_tp hm; fun_prop

lemma abs_U_le (m : ℕ) (x : ℝ) : |U m x| ≤ 2 ^ (m + 1) * ((m : ℝ) + 1) ^ m := by
  by_cases h0 : x < 0
  · rw [U_of_neg m h0, abs_zero]; positivity
  by_cases h1 : (m : ℝ) + 1 ≤ x
  · rw [U_eq_zero_of_ge m h1, abs_zero]; positivity
  push Not at h0 h1
  unfold U
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ range (m + 2), |(-1 : ℝ) ^ j * ((m + 1).choose j) * tp m (x - j)|
      ≤ ∑ j ∈ range (m + 2), ((m + 1).choose j : ℝ) * ((m : ℝ) + 1) ^ m := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast,
          abs_of_nonneg (tp_nonneg _ _)]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        unfold tp
        split_ifs with h
        · exact pow_le_pow_left₀ h (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
                                       linarith) m
        · positivity
    _ = 2 ^ (m + 1) * ((m : ℝ) + 1) ^ m := by
        rw [← Finset.sum_mul]
        congr 1
        have := Nat.sum_range_choose (m + 1)
        exact_mod_cast this

/-- `u ↦ IH_n(c ± u)` is interval integrable (a signed sum of monotone functions). -/
lemma intervalIntegrable_IH_shift (n : ℕ) (c σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (a b : ℝ) :
    IntervalIntegrable (fun u => IH n (σ * u + c)) volume a b := by
  have hs : ∀ j ∈ range (n + 1), IntervalIntegrable
      (fun u => (-1 : ℝ) ^ j * (n.choose j) * tp n (σ * u + c - j)) volume a b := by
    intro j _
    apply IntervalIntegrable.const_mul
    rcases hσ with h | h
    · subst h
      exact ((tp_mono n).comp (fun a b hab => by linarith)).intervalIntegrable
    · subst h
      exact ((tp_mono n).comp_antitone (fun a b hab => by linarith)).intervalIntegrable
  have := (IntervalIntegrable.sum (range (n + 1)) hs).const_mul (1 / (n.factorial : ℝ))
  refine this.congr (fun t _ => ?_)
  simp [IH, Finset.sum_apply]

lemma intervalIntegrable_IH (n : ℕ) (x a b : ℝ) :
    IntervalIntegrable (fun t => IH n (x - t)) volume a b := by
  have := intervalIntegrable_IH_shift n x (-1) (Or.inr rfl) a b
  refine this.congr (fun t _ => ?_); show _ = _; congr 1; ring

lemma IH_of_neg (n : ℕ) {x : ℝ} (hx : x < 0) : IH n x = 0 := by
  unfold IH
  rw [Finset.sum_eq_zero (fun j _ => by
    rw [tp_of_neg (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
                      linarith), mul_zero]), mul_zero]

/-- `U_{n+1}(x)/(n+1)! = ∫₀¹ U_n(x − t)/n! dt` (convolution with the uniform density). -/
lemma U_conv (n : ℕ) (x : ℝ) :
    U (n + 1) x / (n + 1).factorial = ∫ t in (0 : ℝ)..1, U n (x - t) / n.factorial := by
  rw [← IH_sub, ← IH_succ, ← IH_succ, ← intervalIntegral.integral_sub
    (intervalIntegrable_IH n x 0 1) (intervalIntegrable_IH n (x - 1) 0 1)]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  show _ = _
  rw [← IH_sub, show x - 1 - t = x - t - 1 by ring]

lemma intervalIntegrable_IH' (n : ℕ) (c a b : ℝ) :
    IntervalIntegrable (fun u => IH n (u - c)) volume a b := by
  have := intervalIntegrable_IH_shift n (-c) 1 (Or.inl rfl) a b
  refine this.congr (fun t _ => ?_); show _ = _; congr 1; ring

/-! ### The density of `X₁ + ⋯ + X_D` -/

/-- **`U_n/n!` is the density of the sum of `n + 1` independent uniform `[0,1]` variables**:
`Vol_{n+1}{x ∈ [0,1]^{n+1} : ∑ x ≤ x₀} = ∫₀^{x₀} U_n/n!` for `x₀ ≥ 0`. -/
theorem density (n : ℕ) (x₀ : ℝ) :
    volume (S (n + 1) x₀) = ENNReal.ofReal (∫ u in (0 : ℝ)..x₀, U n u / n.factorial) := by
  rw [volume_S]
  congr 1
  have hI : ∀ a b, IntervalIntegrable (IH n) volume a b := fun a b => by
    have := intervalIntegrable_IH' n 0 a b
    simpa using this
  rw [← IH_succ]
  have e1 : ∫ t in (0 : ℝ)..1, IH n (x₀ - t) = ∫ u in (x₀ - 1)..x₀, IH n u := by
    rw [intervalIntegral.integral_comp_sub_left (IH n) x₀]; simp
  have e2 : ∫ u in (0 : ℝ)..x₀, U n u / n.factorial =
      (∫ u in (0 : ℝ)..x₀, IH n u) - ∫ u in (0 : ℝ)..x₀, IH n (u - 1) := by
    rw [← intervalIntegral.integral_sub (hI _ _) (intervalIntegrable_IH' n 1 0 x₀)]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    show _ = _
    rw [IH_sub]
  have e3 : ∫ u in (0 : ℝ)..x₀, IH n (u - 1) = ∫ u in (-1 : ℝ)..(x₀ - 1), IH n u := by
    rw [intervalIntegral.integral_comp_sub_right (IH n) 1]; norm_num
  have e4 : ∫ u in (-1 : ℝ)..0, IH n u = 0 := by
    have h0 : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 0 := by rw [ae_iff]; simp
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) (by
      filter_upwards [h0] with u hu hmem
      rw [uIoc_of_le (by norm_num)] at hmem
      exact IH_of_neg n (lt_of_le_of_ne hmem.2 hu))]
    simp
  have a1 := intervalIntegral.integral_add_adjacent_intervals (hI (x₀ - 1) 0) (hI 0 x₀)
  have a2 := intervalIntegral.integral_add_adjacent_intervals (hI (-1) 0) (hI 0 (x₀ - 1))
  have a3 := intervalIntegral.integral_symm (μ := volume) (f := IH n) 0 (x₀ - 1)
  rw [e1, e2, e3]
  linarith

/-! ### The densities `g_D` of `Y₁ + ⋯ + Y_D` and their samples -/

/-- `g_D(s) = U_n(s + D/2)/n!`, `D = n + 1`: the density of `Y₁ + ⋯ + Y_D`. -/
def g (n : ℕ) (s : ℝ) : ℝ := U n (s + (n + 1) / 2) / n.factorial

/-- `p_{n,k} = E(n,k−1)/n! = g_D(k − D/2)`. -/
theorem g_sample {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    g n (k - (n + 1) / 2) = (EulerianCert.Bracket.E n (k - 1) : ℝ) / n.factorial := by
  unfold g
  rw [E_eq_U hn, show (((k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) by push_cast [Nat.cast_sub hk]; ring]
  congr 2; ring

lemma g_eq_zero {n : ℕ} {s : ℝ} (hs : (n + 1) / 2 < |s|) : g n s = 0 := by
  unfold g
  rcases le_or_gt 0 s with h | h
  · rw [abs_of_nonneg h] at hs
    rw [U_eq_zero_of_ge n (by linarith), zero_div]
  · rw [abs_of_neg h] at hs
    rw [U_of_neg n (by linarith), zero_div]

lemma abs_g_le (n : ℕ) (s : ℝ) : |g n s| ≤ 2 ^ (n + 1) * ((n : ℝ) + 1) ^ n / n.factorial := by
  unfold g
  rw [abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (abs_U_le n _) (by positivity)

lemma measurable_g (n : ℕ) : Measurable (g n) :=
  ((measurable_U n).comp (measurable_id.add_const _)).div_const _

lemma continuous_g {n : ℕ} (hn : 1 ≤ n) : Continuous (g n) :=
  ((continuous_U hn).comp (continuous_id.add continuous_const)).div_const _

/-- `g_{D+1}(s) = ∫_{−½}^{½} g_D(s − y) dy`. -/
theorem g_succ (n : ℕ) (s : ℝ) : g (n + 1) s = ∫ y in (-1 / 2 : ℝ)..(1 / 2), g n (s - y) := by
  unfold g
  rw [U_conv]
  have := intervalIntegral.integral_comp_add_right
    (fun t => U n (s + ((n + 1 : ℕ) + 1) / 2 - t) / n.factorial) (1 / 2 : ℝ)
    (a := -1 / 2) (b := 1 / 2)
  rw [show (-1 / 2 : ℝ) + 1 / 2 = 0 by ring, show (1 / 2 : ℝ) + 1 / 2 = 1 by ring] at this
  rw [← this]
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  show _ = _
  congr 2; push_cast; ring

/-! ### Eq. (80): the characteristic function -/

/-- `ĝ_D(t) = ∫ g_D(s) e^{its} ds`. -/
def ghat (n : ℕ) (t : ℝ) : ℂ := ∫ s, (g n s : ℂ) * Complex.exp (t * s * Complex.I)

lemma integral_exp_Ioc (t : ℝ) :
    ∫ y in Ioc (-1 / 2 : ℝ) (1 / 2), Complex.exp (t * y * Complex.I) = (rE t : ℂ) := by
  rw [← intervalIntegral.integral_of_le (by norm_num)]
  rcases eq_or_ne t 0 with h | h
  · subst h; simp [EulerianCert.FourierModes.rE]; norm_num
  · have hc : (t : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast h) Complex.I_ne_zero
    have := integral_exp_mul_complex (a := -1 / 2) (b := 1 / 2) hc
    rw [show (fun y : ℝ => Complex.exp (t * y * Complex.I)) =
      fun y : ℝ => Complex.exp (t * Complex.I * y) by funext y; ring_nf, this,
      EulerianCert.FourierModes.rE_of_ne_zero h]
    have e1 : Complex.exp ((t : ℂ) * Complex.I * ((1 / 2 : ℝ) : ℂ)) =
        Complex.cos ((t / 2 : ℝ)) + Complex.sin ((t / 2 : ℝ)) * Complex.I := by
      rw [← Complex.exp_mul_I]; push_cast; ring_nf
    have e2 : Complex.exp ((t : ℂ) * Complex.I * ((-1 / 2 : ℝ) : ℂ)) =
        Complex.cos ((t / 2 : ℝ)) - Complex.sin ((t / 2 : ℝ)) * Complex.I := by
      rw [show ((t : ℂ) * Complex.I * ((-1 / 2 : ℝ) : ℂ)) = ((-(t / 2) : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_mul_I]
      push_cast
      rw [Complex.cos_neg, Complex.sin_neg]; ring
    rw [e1, e2, ← Complex.ofReal_sin]
    push_cast
    field_simp
    ring

lemma ghat_zero (t : ℝ) : ghat 0 t = (rE t : ℂ) := by
  unfold ghat
  have h : (fun s : ℝ => (g 0 s : ℂ) * Complex.exp (t * s * Complex.I)) =
      (Ico (-1 / 2 : ℝ) (1 / 2)).indicator (fun s => Complex.exp (t * s * Complex.I)) := by
    funext s
    unfold g
    rw [U_zero_eq]
    simp only [Nat.factorial_zero, Nat.cast_one, div_one, CharP.cast_eq_zero, zero_add]
    by_cases h1 : s ∈ Ico (-1 / 2 : ℝ) (1 / 2)
    · rw [indicator_of_mem h1, tp_of_nonneg (by linarith [h1.1]), tp_of_neg (by linarith [h1.2])]
      simp
    · rw [indicator_of_notMem h1]
      simp only [Set.mem_Ico, not_and_or, not_le, not_lt] at h1
      rcases h1 with h1 | h1
      · rw [tp_of_neg (by linarith), tp_of_neg (by linarith)]; simp
      · rw [tp_of_nonneg (by linarith), tp_of_nonneg (by linarith)]; simp
  rw [h, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc, integral_exp_Ioc]

/-- **Eq. (80)**: `ĝ_D(t) = r_E(t)^D`. -/
theorem ghat_eq (n : ℕ) (t : ℝ) : ghat n t = (rE t : ℂ) ^ (n + 1) := by
  induction n with
  | zero => rw [ghat_zero, zero_add, pow_one]
  | succ n ih =>
    set ν : Measure ℝ := volume.restrict (Ioc (-1 / 2 : ℝ) (1 / 2))
    set F : ℝ → ℝ → ℂ := fun s y => (g n (s - y) : ℂ) * Complex.exp (t * s * Complex.I)
    set B : ℝ := 2 ^ (n + 1) * ((n : ℝ) + 1) ^ n / n.factorial
    set A : ℝ := ((n : ℝ) + 2) / 2
    have hF : Integrable (Function.uncurry F) (volume.prod ν) := by
      have hb : Integrable (fun z : ℝ × ℝ => (Icc (-A) A).indicator (fun _ => (B : ℝ)) z.1 *
          (1 : ℝ)) (volume.prod ν) := by
        haveI : IsFiniteMeasure ν := by
          simp only [ν]; exact isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ioc])
        exact Integrable.mul_prod (f := (Icc (-A) A).indicator (fun _ => (B : ℝ)))
          (g := fun _ => (1 : ℝ))
          ((integrable_indicator_iff measurableSet_Icc).mpr
            (integrableOn_const (by simp [Real.volume_Icc]))) (integrable_const 1)
      refine hb.mono' ?_ ?_
      · apply Measurable.aestronglyMeasurable
        simp only [Function.uncurry_def, F]
        exact (Complex.measurable_ofReal.comp ((measurable_g n).comp
          (measurable_fst.sub measurable_snd))).mul (Complex.continuous_exp.measurable.comp
          (((Complex.measurable_ofReal.comp measurable_fst).const_mul (t : ℂ)).mul_const _))
      · have hae : ∀ᵐ z ∂((volume : Measure ℝ).prod ν), z.2 ∈ Ioc (-1 / 2 : ℝ) (1 / 2) := by
          rw [ae_iff]
          have : {a : ℝ × ℝ | a.2 ∉ Ioc (-1 / 2 : ℝ) (1 / 2)} = univ ×ˢ (Ioc (-1 / 2 : ℝ) (1 / 2))ᶜ := by
            ext z; simp
          rw [this, Measure.prod_prod]
          simp [ν, Measure.restrict_apply measurableSet_Ioc.compl]
        filter_upwards [hae] with z hz
        simp only [Function.uncurry_def, F, mul_one]
        rw [norm_mul, show (t : ℂ) * (z.1 : ℂ) * Complex.I = ((t * z.1 : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs]
        by_cases hzA : z.1 ∈ Icc (-A) A
        · rw [indicator_of_mem hzA]; exact abs_g_le n _
        · rw [indicator_of_notMem hzA, g_eq_zero, abs_zero]
          simp only [Set.mem_Icc, not_and_or, not_le, A] at hzA
          have h1 := hz.1; have h2 := hz.2
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          rcases hzA with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
    unfold ghat
    have step1 : ∀ s, (g (n + 1) s : ℂ) * Complex.exp (t * s * Complex.I) = ∫ y, F s y ∂ν := by
      intro s
      rw [g_succ, intervalIntegral.integral_of_le (by norm_num), ← integral_complex_ofReal,
        ← integral_mul_const]
    simp_rw [step1]
    rw [integral_integral_swap hF]
    have step2 : ∀ y, ∫ s, F s y = Complex.exp (t * y * Complex.I) * ghat n t := by
      intro y
      calc ∫ s, F s y = ∫ s, (fun u => (g n u : ℂ) * Complex.exp (t * (u + y) * Complex.I))
            (s - y) := by
            congr 1; funext s; simp only [F]; congr 3; push_cast; ring
        _ = ∫ s, (g n s : ℂ) * Complex.exp (t * (s + y) * Complex.I) :=
            integral_sub_right_eq_self (μ := (volume : Measure ℝ))
              (fun u => (g n u : ℂ) * Complex.exp (t * (u + y) * Complex.I)) y
        _ = Complex.exp (t * y * Complex.I) * ghat n t := by
            rw [ghat, ← integral_const_mul]
            congr 1; funext s
            rw [show (t : ℂ) * (s + y) * Complex.I = t * y * Complex.I + t * s * Complex.I by
              ring, Complex.exp_add]
            ring
    simp_rw [step2]
    rw [integral_mul_const, integral_exp_Ioc, ih]
    ring

/-! ### Eq. (81): Fourier inversion -/

lemma abs_rE_le_one (t : ℝ) : |rE t| ≤ 1 := Real.abs_sinc_le_one _

lemma abs_rE_le (t : ℝ) (ht : t ≠ 0) : |rE t| ≤ 2 / |t| := by
  rw [EulerianCert.FourierModes.rE_of_ne_zero ht, abs_div, abs_mul, abs_two]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  nlinarith [abs_sin_le_one (t / 2)]

/-- `|r_E(t)|^D ≤ 8/(4 + t²)` for `D ≥ 2`. -/
lemma pow_rE_le {n : ℕ} (hn : 1 ≤ n) (t : ℝ) : |rE t| ^ (n + 1) ≤ 8 * (4 + t ^ 2)⁻¹ := by
  have h1 := abs_rE_le_one t
  have h0 := abs_nonneg (rE t)
  have hsq : |rE t| ^ (n + 1) ≤ |rE t| ^ 2 := pow_le_pow_of_le_one h0 h1 (by omega)
  refine hsq.trans ?_
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  rcases eq_or_ne t 0 with ht | ht
  · subst ht; nlinarith
  · have h2 := abs_rE_le t ht
    have ht2 : 0 < t ^ 2 := by positivity
    have : |rE t| ^ 2 * t ^ 2 ≤ 4 := by
      have := mul_le_mul h2 h2 (abs_nonneg _) (by positivity)
      rw [show 2 / |t| * (2 / |t|) = 4 / t ^ 2 by rw [div_mul_div_comm, ← sq_abs t]; ring] at this
      rw [sq]; calc |rE t| * |rE t| * t ^ 2 ≤ 4 / t ^ 2 * t ^ 2 :=
            mul_le_mul_of_nonneg_right this ht2.le
        _ = 4 := by field_simp
    nlinarith [sq_nonneg (rE t)]

lemma integrable_pow_rE {n : ℕ} (hn : 1 ≤ n) : Integrable (fun t => (rE t) ^ (n + 1)) := by
  have hb : Integrable (fun t : ℝ => 8 * (4 + t ^ 2)⁻¹) := by
    have := (integrable_inv_one_add_sq.comp_mul_left' (show (1 / 2 : ℝ) ≠ 0 by norm_num)).const_mul 2
    refine this.congr (Eventually.of_forall (fun t => ?_))
    simp only
    field_simp
    ring
  refine hb.mono' ?_ (Eventually.of_forall (fun t => ?_))
  · exact (EulerianCert.FourierModes.continuous_rE.pow _).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_pow]; exact pow_rE_le hn t

/-- **Fourier inversion** for `g_D`, `D ≥ 2`:
`g_D(s) = (1/2π) ∫ r_E(t)^D cos(ts) dt`. -/
theorem g_inversion {n : ℕ} (hn : 1 ≤ n) (s : ℝ) :
    g n s = 1 / (2 * π) * ∫ t, (rE t) ^ (n + 1) * Real.cos (t * s) := by
  set f : ℝ → ℂ := fun v => (g n v : ℂ)
  have hfc : Continuous f := Complex.continuous_ofReal.comp (continuous_g hn)
  have hfs : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_Icc (a := -((n : ℝ) + 1) / 2) (b := ((n : ℝ) + 1) / 2))
    intro v hv
    simp only [Set.mem_Icc, not_and_or, not_le] at hv
    simp only [f, Complex.ofReal_eq_zero]
    apply g_eq_zero
    rcases hv with h | h
    · rw [abs_of_neg (by linarith [show (0 : ℝ) ≤ ((n : ℝ) + 1) / 2 by positivity])]; linarith
    · rw [abs_of_pos (by linarith [show (0 : ℝ) ≤ ((n : ℝ) + 1) / 2 by positivity])]; linarith
  have hfi : Integrable f := hfc.integrable_of_hasCompactSupport hfs
  have hFT : ∀ w, 𝓕 f w = ((rE (2 * π * w)) ^ (n + 1) : ℝ) := by
    intro w
    rw [Real.fourier_real_eq_integral_exp_smul]
    have := ghat_eq n (-(2 * π * w))
    unfold ghat at this
    rw [EulerianCert.FourierModes.rE_neg] at this
    push_cast at this ⊢
    rw [← this]
    congr 1; funext v
    simp only [f, smul_eq_mul]
    rw [mul_comm]; congr 2; push_cast; ring
  have hFTi : Integrable (𝓕 f) := by
    rw [show 𝓕 f = fun w => (((rE (2 * π * w)) ^ (n + 1) : ℝ) : ℂ) from funext hFT]
    exact ((integrable_pow_rE hn).comp_mul_left' (by positivity : (2 * π) ≠ 0)).ofReal
  have hinv := congrFun (hfc.fourierInv_fourier_eq hfi hFTi) s
  rw [Real.fourierInv_eq'] at hinv
  simp only [hFT, f] at hinv
  -- substitute `t = 2πw`
  have hsub : ∫ w : ℝ, Complex.exp (↑(2 * π * (w * s)) * Complex.I) •
      (((rE (2 * π * w)) ^ (n + 1) : ℝ) : ℂ) =
      ((1 / (2 * π) : ℝ) : ℂ) * ∫ t : ℝ, Complex.exp (↑(t * s) * Complex.I) *
        (((rE t) ^ (n + 1) : ℝ) : ℂ) := by
    have := Measure.integral_comp_mul_left
      (fun t : ℝ => Complex.exp (↑(t * s) * Complex.I) * (((rE t) ^ (n + 1) : ℝ) : ℂ)) (2 * π)
    rw [show (fun w : ℝ => Complex.exp (↑(2 * π * (w * s)) * Complex.I) •
        (((rE (2 * π * w)) ^ (n + 1) : ℝ) : ℂ)) =
        fun w : ℝ => Complex.exp (↑(2 * π * w * s) * Complex.I) *
        (((rE (2 * π * w)) ^ (n + 1) : ℝ) : ℂ) by funext w; rw [smul_eq_mul]; ring_nf, this]
    rw [abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹), Complex.real_smul]
    push_cast; ring
  simp_rw [Real.inner_apply] at hinv
  rw [hsub] at hinv
  have hre := congrArg Complex.re hinv
  rw [Complex.ofReal_re] at hre
  rw [← hre, Complex.re_ofReal_mul]
  congr 1
  have hint : Integrable (fun t : ℝ => Complex.exp (↑(t * s) * Complex.I) *
      (((rE t) ^ (n + 1) : ℝ) : ℂ)) := by
    refine (integrable_pow_rE hn).ofReal.bdd_mul
      (f := fun t : ℝ => Complex.exp (↑(t * s) * Complex.I)) (c := 1) ?_ ?_
    · exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (continuous_id.mul continuous_const)).mul continuous_const)).aestronglyMeasurable
    · exact Eventually.of_forall (fun t => by rw [Complex.norm_exp_ofReal_mul_I])
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hint]
  congr 1; funext t
  simp only [Complex.reCLM_apply]
  rw [mul_comm, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- **Eq. (81)**: `p_{n,k} = E(n,k−1)/n! = (1/2π) ∫ r_E(t)^{n+1} cos(t(k − (n+1)/2)) dt`. -/
theorem eulerian_fourier_inversion {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (EulerianCert.Bracket.E n (k - 1) : ℝ) / n.factorial =
      1 / (2 * π) * ∫ t, (rE t) ^ (n + 1) * Real.cos (t * (k - (n + 1) / 2)) := by
  rw [← g_sample hn hk, g_inversion hn]

lemma integrable_pow_rE_mul_cos {n : ℕ} (hn : 1 ≤ n) (c : ℝ) :
    Integrable (fun t => (rE t) ^ (n + 1) * Real.cos (t * c)) :=
  (integrable_pow_rE hn).mul_bdd (c := 1)
    ((Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
    (Eventually.of_forall (fun t => by rw [Real.norm_eq_abs]; exact abs_cos_le_one _))

/-- Symmetry of the Eulerian distribution, read off from Eq. (81):
`E(n,k−1) = E(n,n−k)` for `1 ≤ k ≤ n`. -/
theorem eulerian_symmetry {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    EulerianCert.Bracket.E n (k - 1) = EulerianCert.Bracket.E n (n - k) := by
  have h1 := eulerian_fourier_inversion hn hk
  have h2 := eulerian_fourier_inversion hn (show 1 ≤ n + 1 - k by omega)
  rw [show n + 1 - k - 1 = n - k by omega] at h2
  have hc : ∀ t : ℝ, Real.cos (t * (((n + 1 - k : ℕ) : ℝ) - (n + 1) / 2)) =
      Real.cos (t * ((k : ℝ) - (n + 1) / 2)) := by
    intro t
    rw [show (((n + 1 - k : ℕ) : ℝ) - (n + 1) / 2) = -((k : ℝ) - (n + 1) / 2) by
      push_cast [Nat.cast_sub (show k ≤ n + 1 by omega)]; ring, mul_neg, Real.cos_neg]
  simp_rw [hc] at h2
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have := h1.trans h2.symm
  rw [div_left_inj' hf] at this
  exact_mod_cast this

/-- **Lemma 3.15, Eq. (84)**, integral form of the central slope: for odd `n = 2j + 1 ≥ 3`,
`s_n = (n+1)(p_{n,(n+1)/2} − p_{n,(n−1)/2}) = ((n+1)/2π) ∫ r_E(t)^{n+1} (1 − cos t) dt`. -/
theorem central_slope_integral {j : ℕ} (hj : 1 ≤ j) :
    ((2 * j + 1 : ℕ) + 1 : ℝ) * ((EulerianCert.Bracket.E (2 * j + 1) j : ℝ) / (2 * j + 1).factorial -
      (EulerianCert.Bracket.E (2 * j + 1) (j - 1) : ℝ) / (2 * j + 1).factorial) =
      ((2 * j + 1 : ℕ) + 1 : ℝ) / (2 * π) *
        ∫ t, (rE t) ^ (2 * j + 1 + 1) * (1 - Real.cos t) := by
  have hn : 1 ≤ 2 * j + 1 := by omega
  have h1 := eulerian_fourier_inversion hn (show 1 ≤ j + 1 by omega)
  have h2 := eulerian_fourier_inversion hn hj
  rw [show j + 1 - 1 = j by omega] at h1
  have e1 : ∀ t : ℝ, Real.cos (t * (((j + 1 : ℕ) : ℝ) - (((2 * j + 1 : ℕ) : ℝ) + 1) / 2)) = 1 := by
    intro t; rw [show (((j + 1 : ℕ) : ℝ) - (((2 * j + 1 : ℕ) : ℝ) + 1) / 2) = 0 by push_cast; ring,
      mul_zero, Real.cos_zero]
  have e2 : ∀ t : ℝ, Real.cos (t * ((j : ℝ) - (((2 * j + 1 : ℕ) : ℝ) + 1) / 2)) = Real.cos t := by
    intro t; rw [show ((j : ℝ) - (((2 * j + 1 : ℕ) : ℝ) + 1) / 2) = -1 by push_cast; ring,
      mul_neg, mul_one, Real.cos_neg]
  simp_rw [e1, mul_one] at h1
  simp_rw [e2] at h2
  rw [h1, h2]
  have hi1 := integrable_pow_rE (n := 2 * j + 1) hn
  have hi2 := integrable_pow_rE_mul_cos (n := 2 * j + 1) hn 1
  simp only [mul_one] at hi2
  rw [show (fun t => (rE t) ^ (2 * j + 1 + 1) * (1 - Real.cos t)) =
    fun t => (rE t) ^ (2 * j + 1 + 1) - (rE t) ^ (2 * j + 1 + 1) * Real.cos t by
      funext t; ring, integral_sub hi1 hi2]
  ring

end EulerianCert.EulerianFourier
