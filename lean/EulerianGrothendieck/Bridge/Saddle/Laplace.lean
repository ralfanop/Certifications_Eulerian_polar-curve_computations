import Bridge.Saddle.Spline
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Lemma 5.5, part 2: regularity of `w_M` and its two-sided Laplace transform

Manuscript V173, Section 5: `∫ e^{zy} w_M(y) dy = A(z)^M` for every complex `z` and `M ≥ 1`.

* `w_measurable`, `w_le_one`: `w_M` is measurable with `0 ≤ w_M ≤ 1`;
* `w_succ_primitive`: `w_{M+1}(y) = ∫_{y-1/2}^{y+1/2} w_M`;
* `w_continuous`: `w_M` is continuous for `M ≥ 2`;
* `integrable_mul_w`: `g · w_M` is integrable for every continuous `g`;
* `laplace_w`: `∫ e^{zy} w_M(y) dy = A(z)^M`.
-/

open MeasureTheory Set Complex Filter Topology

namespace EulerianBridge.Saddle

theorem w_succ (M : ℕ) (hM : 1 ≤ M) (y : ℝ) :
    w (M + 1) y = ∫ t in (-1/2:ℝ)..(1/2), w M (y - t) := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  exact w_succ_succ k y

theorem w_succ_primitive (M : ℕ) (hM : 1 ≤ M) (y : ℝ) :
    w (M + 1) y = ∫ t in (y - 1/2)..(y + 1/2), w M t := by
  rw [w_succ M hM, intervalIntegral.integral_comp_sub_left (fun t => w M t) y]
  congr 1 <;> ring

/-- A measurable function bounded by one is interval integrable. -/
theorem intervalIntegrable_of_le_one {f : ℝ → ℝ} (hf : Measurable f) (h0 : ∀ y, 0 ≤ f y)
    (h1 : ∀ y, f y ≤ 1) (a b : ℝ) : IntervalIntegrable f volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => (1:ℝ)) _root_.intervalIntegrable_const
    hf.aestronglyMeasurable (Eventually.of_forall (fun y => ?_))
  show ‖f y‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (h0 y)]; exact h1 y

/-- The primitive-difference `y ↦ ∫_{y-1/2}^{y+1/2} f` of a bounded measurable `f` is continuous. -/
theorem continuous_window {f : ℝ → ℝ} (hf : Measurable f) (h0 : ∀ y, 0 ≤ f y)
    (h1 : ∀ y, f y ≤ 1) : Continuous (fun y => ∫ t in (y - 1/2)..(y + 1/2), f t) := by
  have hI := intervalIntegrable_of_le_one hf h0 h1
  have hc := intervalIntegral.continuous_primitive (μ := volume) hI 0
  have heq : (fun y => ∫ t in (y - 1/2)..(y + 1/2), f t) =
      fun y => (∫ t in (0:ℝ)..(y + 1/2), f t) - ∫ t in (0:ℝ)..(y - 1/2), f t := by
    funext y
    rw [intervalIntegral.integral_interval_sub_left (hI _ _) (hI _ _)]
  rw [heq]
  exact (hc.comp (continuous_id.add continuous_const)).sub
    (hc.comp (continuous_id.sub continuous_const))

theorem w_window_le_one {f : ℝ → ℝ} (hf : Measurable f) (h0 : ∀ y, 0 ≤ f y)
    (h1 : ∀ y, f y ≤ 1) (y : ℝ) : ∫ t in (y - 1/2)..(y + 1/2), f t ≤ 1 := by
  have hI := intervalIntegrable_of_le_one hf h0 h1
  calc ∫ t in (y - 1/2)..(y + 1/2), f t ≤ ∫ t in (y - 1/2)..(y + 1/2), (1:ℝ) :=
        intervalIntegral.integral_mono_on (by linarith) (hI _ _) _root_.intervalIntegrable_const
          (fun t _ => h1 t)
    _ = 1 := by simp; norm_num

/-- Joint induction: measurability and the bounds `0 ≤ w_M ≤ 1`. -/
theorem w_meas_bdd : ∀ M : ℕ, Measurable (w M) ∧ ∀ y, 0 ≤ w M y ∧ w M y ≤ 1
  | 0 => ⟨by simp only [w]; exact measurable_const, fun y => by simp [w]⟩
  | 1 => ⟨by
      simp only [w]
      exact measurable_const.indicator measurableSet_Ioc,
      fun y => by rw [w_one_eq]; split_ifs <;> norm_num⟩
  | (M + 2) => by
      obtain ⟨hm, hb⟩ := w_meas_bdd (M + 1)
      have h0 : ∀ y, 0 ≤ w (M + 1) y := fun y => (hb y).1
      have h1 : ∀ y, w (M + 1) y ≤ 1 := fun y => (hb y).2
      have heq : w (M + 2) = fun y => ∫ t in (y - 1/2)..(y + 1/2), w (M + 1) t := by
        funext y; exact w_succ_primitive (M + 1) (by omega) y
      refine ⟨?_, fun y => ⟨w_nonneg _ _, ?_⟩⟩
      · rw [heq]; exact (continuous_window hm h0 h1).measurable
      · rw [heq]; exact w_window_le_one hm h0 h1 y

theorem w_measurable (M : ℕ) : Measurable (w M) := (w_meas_bdd M).1

theorem w_le_one (M : ℕ) (y : ℝ) : w M y ≤ 1 := ((w_meas_bdd M).2 y).2

theorem w_continuous (M : ℕ) (hM : 2 ≤ M) : Continuous (w M) := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 + 1 := ⟨M - 2, by omega⟩
  have heq : w (k + 1 + 1) = fun y => ∫ t in (y - 1/2)..(y + 1/2), w (k + 1) t := by
    funext y; exact w_succ_primitive (k + 1) (by omega) y
  rw [heq]
  exact continuous_window (w_measurable _) (fun y => w_nonneg _ _) (w_le_one _)

theorem w_eq_indicator (M : ℕ) (hM : 1 ≤ M) :
    w M = (Icc (-((M:ℝ)/2)) ((M:ℝ)/2)).indicator (w M) := by
  funext y
  by_cases hy : y ∈ Icc (-((M:ℝ)/2)) ((M:ℝ)/2)
  · rw [indicator_of_mem hy]
  · rw [indicator_of_notMem hy]
    apply w_support M hM
    rw [mem_Icc, not_and_or, not_le, not_le] at hy
    rw [lt_abs]
    rcases hy with hy | hy
    · right; linarith
    · left; exact hy

/-- `g · w_M` is integrable for continuous `g` (complex valued). -/
theorem integrable_mul_w (M : ℕ) (hM : 1 ≤ M) {g : ℝ → ℂ} (hg : Continuous g) :
    Integrable (fun y => g y * (w M y : ℂ)) := by
  set R : ℝ := (M:ℝ) / 2
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hg.continuousOn
  have hint : Integrable ((Icc (-R) R).indicator (fun _ => C)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  refine hint.mono' ((hg.aestronglyMeasurable).mul
    (Complex.measurable_ofReal.comp (w_measurable M)).aestronglyMeasurable)
    (Eventually.of_forall (fun y => ?_))
  by_cases hy : y ∈ Icc (-R) R
  · rw [indicator_of_mem hy, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (w_nonneg M y)]
    calc ‖g y‖ * w M y ≤ C * 1 :=
          mul_le_mul (hC y hy) (w_le_one M y) (w_nonneg M y) ((norm_nonneg _).trans (hC y hy))
      _ = C := mul_one C
  · rw [indicator_of_notMem hy]
    have : w M y = 0 := by
      rw [w_eq_indicator M hM]; exact indicator_of_notMem hy _
    simp [this]

theorem A_eq_setIntegral (z : ℂ) : A z = ∫ t in Ioc (-1/2:ℝ) (1/2), cexp (z * t) := by
  rw [A, intervalIntegral.integral_of_le (by norm_num)]

/-- The Laplace transform of `w_M`: `∫ e^{zy} w_M(y) dy = A(z)^M`. -/
theorem laplace_w : ∀ (M : ℕ), 1 ≤ M → ∀ z : ℂ, ∫ y : ℝ, cexp (z * y) * (w M y : ℂ) = A z ^ M
  | 0, h, _ => absurd h (by norm_num)
  | 1, _, z => by
      have : (fun y : ℝ => cexp (z * y) * (w 1 y : ℂ)) =
          (Ioc (-1/2:ℝ) (1/2)).indicator (fun y => cexp (z * y)) := by
        funext y
        rw [w_one_eq]
        by_cases hy : y ∈ Ioc (-1/2:ℝ) (1/2)
        · rw [if_pos hy, indicator_of_mem hy]; simp
        · rw [if_neg hy, indicator_of_notMem hy]; simp
      rw [this, MeasureTheory.integral_indicator measurableSet_Ioc, ← A_eq_setIntegral, pow_one]
  | (M + 2), _, z => by
      have ih := laplace_w (M + 1) (by omega) z
      set N := M + 1
      -- the integrand of the double integral
      set G : ℝ → ℝ → ℂ := fun y t =>
        (Ioc (-1/2:ℝ) (1/2)).indicator (fun _ => (1:ℂ)) t * (cexp (z * y) * (w N (y - t) : ℂ))
      have hw : ∀ y, (w (M + 2) y : ℂ) =
          ∫ t, (Ioc (-1/2:ℝ) (1/2)).indicator (fun _ => (1:ℂ)) t * (w N (y - t) : ℂ) := by
        intro y
        rw [w_succ_succ, intervalIntegral.integral_of_le (by norm_num)]
        rw [← integral_complex_ofReal]
        rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
        congr 1; funext t
        by_cases ht : t ∈ Ioc (-1/2:ℝ) (1/2)
        · rw [indicator_of_mem ht, indicator_of_mem ht, one_mul]
        · rw [indicator_of_notMem ht, indicator_of_notMem ht, zero_mul]
      have h1 : ∫ y : ℝ, cexp (z * y) * (w (M + 2) y : ℂ) = ∫ y, ∫ t, G y t := by
        congr 1; funext y
        rw [hw y, ← MeasureTheory.integral_const_mul]
        congr 1; funext t; simp only [G]; ring
      -- integrability on the product
      have hGint : Integrable (Function.uncurry G) (volume.prod volume) := by
        set R : ℝ := (N:ℝ) / 2 + 1
        have hR : R = (N:ℝ) / 2 + 1 := rfl
        set C : ℝ := Real.exp (‖z‖ * R)
        have hf : Integrable ((Icc (-R) R).indicator (fun _ => C)) :=
          (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
        have hg : Integrable ((Ioc (-1/2:ℝ) (1/2)).indicator (fun _ => (1:ℝ))) :=
          (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
        have hprod := hf.mul_prod hg
        refine hprod.mono' ?_ (Eventually.of_forall (fun p => ?_))
        · apply Measurable.aestronglyMeasurable
          apply Measurable.mul
          · exact (measurable_const.indicator measurableSet_Ioc).comp measurable_snd
          · apply Measurable.mul
            · exact (Complex.continuous_exp.comp (continuous_const.mul
                (Complex.continuous_ofReal.comp continuous_fst))).measurable
            · exact Complex.measurable_ofReal.comp ((w_measurable N).comp
                (measurable_fst.sub measurable_snd))
        · obtain ⟨y, t⟩ := p
          simp only [Function.uncurry_apply_pair, G]
          by_cases ht : t ∈ Ioc (-1/2:ℝ) (1/2)
          · rw [indicator_of_mem ht, indicator_of_mem ht, one_mul, mul_one]
            by_cases hy : y ∈ Icc (-R) R
            · rw [indicator_of_mem hy, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (w_nonneg N _), Complex.norm_exp]
              have hre : (z * (y:ℂ)).re ≤ ‖z‖ * R := by
                calc (z * (y:ℂ)).re ≤ ‖z * (y:ℂ)‖ := Complex.re_le_norm _
                  _ = ‖z‖ * |y| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
                  _ ≤ ‖z‖ * R := mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hy.1, hy.2⟩) (norm_nonneg _)
              calc Real.exp (z * (y:ℂ)).re * w N (y - t) ≤ C * 1 :=
                    mul_le_mul (Real.exp_le_exp.mpr hre) (w_le_one N _) (w_nonneg N _) (Real.exp_pos _).le
                _ = C := mul_one C
            · rw [indicator_of_notMem hy]
              have : w N (y - t) = 0 := by
                apply w_support N (by omega)
                rw [mem_Icc, not_and_or, not_le, not_le] at hy
                rw [lt_abs]
                rcases hy with hy | hy
                · right; linarith [ht.1, ht.2, hR]
                · left; linarith [ht.1, ht.2, hR]
              simp [this]
          · rw [indicator_of_notMem ht, indicator_of_notMem ht]; simp
      rw [h1, integral_integral_swap hGint]
      have h2 : ∀ t, ∫ y, G y t =
          (Ioc (-1/2:ℝ) (1/2)).indicator (fun _ => (1:ℂ)) t * (cexp (z * t) * A z ^ N) := by
        intro t
        simp only [G]
        rw [MeasureTheory.integral_const_mul]
        congr 1
        have hshift : ∫ y : ℝ, cexp (z * y) * (w N (y - t) : ℂ) =
            ∫ y : ℝ, cexp (z * ((y:ℂ) + t)) * (w N y : ℂ) := by
          rw [← integral_sub_right_eq_self (μ := volume)
            (fun y : ℝ => cexp (z * ((y:ℂ) + t)) * (w N y : ℂ)) t]
          congr 1; funext y; push_cast; ring_nf
        rw [hshift, ← ih, ← MeasureTheory.integral_const_mul]
        congr 1; funext y
        rw [show z * ((y:ℂ) + t) = z * t + z * y by ring, Complex.exp_add]; ring
      have h3 : ∫ t, (Ioc (-1/2:ℝ) (1/2)).indicator (fun _ => (1:ℂ)) t * cexp (z * t) = A z := by
        rw [A_eq_setIntegral, ← MeasureTheory.integral_indicator measurableSet_Ioc]
        congr 1; funext t
        by_cases ht : t ∈ Ioc (-1/2:ℝ) (1/2)
        · rw [indicator_of_mem ht, indicator_of_mem ht, one_mul]
        · rw [indicator_of_notMem ht, indicator_of_notMem ht, zero_mul]
      have h4 : ∫ t, (Ioc (-1/2:ℝ) (1/2)).indicator (fun _ => (1:ℂ)) t * (cexp (z * t) * A z ^ N) =
          (∫ t, (Ioc (-1/2:ℝ) (1/2)).indicator (fun _ => (1:ℂ)) t * cexp (z * t)) * A z ^ N := by
        rw [← MeasureTheory.integral_mul_const]; congr 1; funext t; ring
      simp_rw [h2]
      rw [h4, h3, show M + 2 = N + 1 from rfl, pow_succ]
      ring

end EulerianBridge.Saddle
