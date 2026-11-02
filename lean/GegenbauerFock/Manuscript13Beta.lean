import Mathlib.Probability.Distributions.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Manuscript 13: the real beta integral and the symmetric weight `(1-u²)^s` on `(-1,1)`

* `beta_real`: `∫_0^1 x^{a-1}(1-x)^{b-1} dx = Γ(a)Γ(b)/Γ(a+b)` with interval integrability, `a, b > 0`
  (from Mathlib's complex beta integral);
* `sym_weight`: for `s > -1`, `(1-u²)^s` is interval integrable on `[-1,1]` and
  `∫_{-1}^1 (1-u²)^s du = 2^{2s+1} Γ(s+1)²/Γ(2s+2)` (affine change of variables `u = 2x-1`). -/

open Real MeasureTheory Set intervalIntegral

namespace GegenbauerFock.Manuscript13

theorem beta_real {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1)) volume 0 1 ∧
      ∫ x in (0:ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) = ProbabilityTheory.beta a b := by
  have hc := Complex.betaIntegral_convergent (u := (a:ℂ)) (v := (b:ℂ)) (by simpa) (by simpa)
  have heq : EqOn (fun x : ℝ => ((x:ℂ) ^ ((a:ℂ) - 1) * (1 - (x:ℂ)) ^ ((b:ℂ) - 1)))
      (fun x : ℝ => ((x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ)) (uIoc 0 1) := by
    intro x hx
    rw [uIoc_of_le (by norm_num)] at hx
    have h0 : 0 ≤ x := hx.1.le
    have h1 : 0 ≤ 1 - x := by linarith [hx.2]
    simp only [Complex.ofReal_mul]
    rw [Complex.ofReal_cpow h0, Complex.ofReal_cpow h1]
    push_cast
    ring_nf
  have hcR : IntervalIntegrable (fun x : ℝ => ((x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ))
      volume 0 1 := by
    refine (intervalIntegrable_congr_ae ?_).mp hc
    exact (ae_restrict_of_forall_mem measurableSet_uIoc heq)
  have hR : IntervalIntegrable (fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1)) volume 0 1 :=
    hcR.norm.mono_fun' (f := fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1))
      (by fun_prop : Measurable fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simp)
  refine ⟨hR, ?_⟩
  have hb2 : Complex.betaIntegral a b = ((∫ x in (0:ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_congr_ae
      (Filter.Eventually.of_forall fun x hx => heq hx), intervalIntegral.integral_ofReal]
  rw [ProbabilityTheory.beta_eq_betaIntegralReal a b ha hb, hb2, Complex.ofReal_re]

/-- `(1-u²)^s` on `(-1,1)`, `s > -1`: integrability and value. -/
theorem sym_weight {s : ℝ} (hs : -1 < s) :
    IntervalIntegrable (fun u : ℝ => (1 - u ^ 2) ^ s) volume (-1) 1 ∧
      ∫ u in (-1:ℝ)..1, (1 - u ^ 2) ^ s =
        2 ^ (2 * s + 1) * (Real.Gamma (s + 1) ^ 2 / Real.Gamma (2 * s + 2)) := by
  obtain ⟨hI, hV⟩ := beta_real (a := s + 1) (b := s + 1) (by linarith) (by linarith)
  simp only [add_sub_cancel_right] at hI hV
  have hpt : ∀ x ∈ Icc (0:ℝ) 1, (1 - (2 * x - 1) ^ 2) ^ s = 4 ^ s * (x ^ s * (1 - x) ^ s) := by
    intro x hx
    rw [show 1 - (2 * x - 1) ^ 2 = 4 * (x * (1 - x)) by ring,
      Real.mul_rpow (by norm_num) (mul_nonneg hx.1 (by linarith [hx.2])),
      Real.mul_rpow hx.1 (by linarith [hx.2])]
  -- change of variables u = 2x - 1
  have hcomp := intervalIntegral.integral_comp_mul_sub (fun u : ℝ => (1 - u ^ 2) ^ s)
    (by norm_num : (2:ℝ) ≠ 0) (a := 0) (b := 1) 1
  norm_num at hcomp
  have hII : IntervalIntegrable (fun u : ℝ => (1 - u ^ 2) ^ s) volume (-1) 1 := by
    have h1 : IntervalIntegrable (fun x : ℝ => 4 ^ s * (x ^ s * (1 - x) ^ s)) volume 0 1 :=
      hI.const_mul _
    have h2 : IntervalIntegrable (fun x : ℝ => (1 - (2 * x - 1) ^ 2) ^ s) volume 0 1 := by
      refine (intervalIntegrable_congr_ae ?_).mpr h1
      refine ae_restrict_of_forall_mem measurableSet_uIoc fun x hx => ?_
      rw [uIoc_of_le (by norm_num)] at hx
      exact hpt x ⟨hx.1.le, hx.2⟩
    have h4 := (h2.comp_mul_left (c := 1/2)).comp_sub_right (-1)
    have h5 : IntervalIntegrable (fun u : ℝ => (1 - u ^ 2) ^ s) volume
        ((0:ℝ) / (1/2) + -1) (1 / (1/2) + -1) := by
      refine (intervalIntegrable_congr_ae ?_).mp h4
      exact Filter.Eventually.of_forall fun u => by
        show (1 - (2 * ((1/2) * (u - -1)) - 1) ^ 2) ^ s = (1 - u ^ 2) ^ s
        congr 1; ring
    have e1 : (0:ℝ) / (1/2) + -1 = -1 := by norm_num
    have e2 : (1:ℝ) / (1/2) + -1 = 1 := by norm_num
    rw [e1, e2] at h5
    exact h5
  refine ⟨hII, ?_⟩
  have hval : ∫ x in (0:ℝ)..1, (1 - (2 * x - 1) ^ 2) ^ s =
      4 ^ s * ProbabilityTheory.beta (s + 1) (s + 1) := by
    rw [intervalIntegral.integral_congr (g := fun x : ℝ => 4 ^ s * (x ^ s * (1 - x) ^ s)),
      intervalIntegral.integral_const_mul, hV]
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    exact hpt x hx
  have : ∫ u in (-1:ℝ)..1, (1 - u ^ 2) ^ s = 2 * (4 ^ s * ProbabilityTheory.beta (s + 1) (s + 1)) := by
    rw [← hval, hcomp]; ring
  rw [this, ProbabilityTheory.beta, show s + 1 + (s + 1) = 2 * s + 2 by ring,
    show (4:ℝ) ^ s = 2 ^ (2 * s) by
      rw [show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)],
    Real.rpow_add (by norm_num), Real.rpow_one]
  ring

end GegenbauerFock.Manuscript13
