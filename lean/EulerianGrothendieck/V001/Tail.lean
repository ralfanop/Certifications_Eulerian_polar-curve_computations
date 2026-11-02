import V001.Integrand
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Manuscript 11, proof of Lemma 3.15: Eq. (88) verbatim

For `D ≥ 2` and `δ = D^{−2/5}` (so `0 < δ ≤ 1`),

  `∫_{|t| ≥ δ} |r_E(t)|^D (1 − cos t) dt ≤ 4π / exp((D − 2)δ²/24) = O(1/e^{D^{1/5}/25})`.

Classical input, stated as an explicit hypothesis and not re-proved (as for Plancherel's theorem
in the library `Bridge`): `r_E² ∈ L¹(ℝ)` and `∫_ℝ r_E(t)² dt = 2π`, i.e. `∫_ℝ (sin u/u)² du = π`.

Proved here: the pointwise bound `|r_E(t)| ≤ e^{−δ²/24}` for `|t| ≥ δ`, `0 < δ ≤ 1` (the three
ranges `δ ≤ |t| ≤ 1`, `1 ≤ |t| ≤ 2π`, `|t| ≥ 2π` of the manuscript), the integral inequality with
the constant `4π`, and the estimate `4π/exp((D − 2)δ²/24) ≤ C e^{−D^{1/5}/25}`.
-/

open Real MeasureTheory Set

noncomputable section

namespace V001Cert

/-- The classical input: `r_E² ∈ L¹(ℝ)` and `∫_ℝ r_E² = 2π`. -/
def L2Input : Prop := Integrable (fun t => rE t ^ 2) ∧ ∫ t, rE t ^ 2 = 2 * π

lemma continuous_rE : Continuous rE := by
  unfold rE; exact Real.continuous_sinc.comp (continuous_id.div_const 2)

lemma abs_rE_le_far {t : ℝ} (ht : t ≠ 0) : |rE t| ≤ 2 / |t| := by
  rw [rE_eq_abs t ht, abs_div, abs_of_pos (by positivity : 0 < |t| / 2)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := Real.abs_sin_le_one (|t| / 2)
  nlinarith [abs_nonneg t]

/-- `1 − y/24 + y²/1920 ≤ e^{−y/24}` for `0 ≤ y ≤ 1`. -/
lemma poly_le_exp {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    1 - y / 24 + y ^ 2 / 1920 ≤ Real.exp (-(y / 24)) := by
  have h := exp_ge_cubic (x := -(y / 24)) (by linarith)
  nlinarith [sq_nonneg y, pow_nonneg hy0 3]

/-- **Pointwise bound.** For `0 < δ ≤ 1` and `|t| ≥ δ`: `|r_E(t)| ≤ e^{−δ²/24}`. -/
lemma abs_rE_le_exp {δ t : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ht : δ ≤ |t|) :
    |rE t| ≤ Real.exp (-(δ ^ 2 / 24)) := by
  have hδt : δ ^ 2 ≤ t ^ 2 := by
    have := pow_le_pow_left₀ hδ0.le ht 2; rwa [sq_abs] at this
  have hmono : Real.exp (-(1 / 24)) ≤ Real.exp (-(δ ^ 2 / 24)) := by
    apply Real.exp_le_exp.mpr
    have : δ ^ 2 ≤ 1 := by nlinarith
    linarith
  -- `e^{−1/24} ≥ 1 − 1/24 + 1/1920`
  have hc : 1 - 1 / 24 + 1 / 1920 ≤ Real.exp (-(1 / 24)) := by
    have := poly_le_exp (y := 1) (by norm_num) le_rfl; norm_num at this ⊢; linarith
  by_cases h1 : |t| ≤ 1
  · -- `δ ≤ |t| ≤ 1`
    have ht2 : t ^ 2 ≤ 1 := by
      have := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2; simpa using this
    have h0 : 0 ≤ rE t := rE_nonneg (h1.trans (by linarith [Real.two_le_pi]))
    rw [abs_of_nonneg h0]
    have e4 : t ^ 4 = (t ^ 2) ^ 2 := by ring
    calc rE t ≤ 1 - t ^ 2 / 24 + t ^ 4 / 1920 := rE_le t
      _ ≤ Real.exp (-(t ^ 2 / 24)) := by rw [e4]; exact poly_le_exp (sq_nonneg t) ht2
      _ ≤ Real.exp (-(δ ^ 2 / 24)) := Real.exp_le_exp.mpr (by linarith)
  push_neg at h1
  by_cases h2 : |t| ≤ 2 * π
  · -- `1 ≤ |t| ≤ 2π`: `r_E(t) ≤ 1 − t²/24 + t⁴/1920 ≤ 1 − 1/24 + 1/1920`
    have h0 : 0 ≤ rE t := rE_nonneg h2
    rw [abs_of_nonneg h0]
    have hy1 : 1 ≤ t ^ 2 := by
      have := mul_le_mul h1.le h1.le zero_le_one (abs_nonneg _)
      rwa [one_mul, ← sq, sq_abs] at this
    have hy2 : t ^ 2 ≤ 64 := by
      have h8 : |t| ≤ 8 := h2.trans (by linarith [Real.pi_le_four])
      have := mul_le_mul h8 h8 (abs_nonneg _) (by norm_num)
      rw [← sq, sq_abs] at this; linarith
    have e4 : t ^ 4 = (t ^ 2) ^ 2 := by ring
    calc rE t ≤ 1 - t ^ 2 / 24 + t ^ 4 / 1920 := rE_le t
      _ ≤ 1 - 1 / 24 + 1 / 1920 := by
          rw [e4]; nlinarith [mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr hy2)]
      _ ≤ Real.exp (-(1 / 24)) := hc
      _ ≤ _ := hmono
  · -- `|t| ≥ 2π`: `|r_E(t)| ≤ 2/|t| ≤ 1/π ≤ 1/2`
    push_neg at h2
    have ht0 : t ≠ 0 := by intro h; rw [h, abs_zero] at h1; linarith
    have hπ := Real.two_le_pi
    calc |rE t| ≤ 2 / |t| := abs_rE_le_far ht0
      _ ≤ 2 / (2 * π) := div_le_div_of_nonneg_left (by norm_num) (by positivity) h2.le
      _ ≤ 1 / 2 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      _ ≤ 1 - 1 / 24 + 1 / 1920 := by norm_num
      _ ≤ Real.exp (-(1 / 24)) := hc
      _ ≤ _ := hmono

/-- The integrand of (88) is dominated by `2 e^{−(D−2)δ²/24} r_E²` on `{|t| ≥ δ}`. -/
lemma integrand_le {D : ℕ} (hD : 2 ≤ D) {δ t : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ht : δ ≤ |t|) :
    |rE t| ^ D * (1 - Real.cos t) ≤
      2 * Real.exp (-(((D : ℝ) - 2) * δ ^ 2 / 24)) * rE t ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, D = m + 2 := ⟨D - 2, by omega⟩
  have hb := abs_rE_le_exp hδ0 hδ1 ht
  have hpow : |rE t| ^ m ≤ Real.exp (-(δ ^ 2 / 24)) ^ m :=
    pow_le_pow_left₀ (abs_nonneg _) hb m
  rw [← Real.exp_nat_mul] at hpow
  have hcos : 0 ≤ 1 - Real.cos t := by linarith [Real.cos_le_one t]
  have hcos2 : 1 - Real.cos t ≤ 2 := by linarith [Real.neg_one_le_cos t]
  have e : |rE t| ^ (m + 2) = |rE t| ^ m * rE t ^ 2 := by rw [pow_add, sq_abs]
  have em : ((m + 2 : ℕ) : ℝ) - 2 = m := by push_cast; ring
  rw [e, em]
  have h1 : |rE t| ^ m * rE t ^ 2 * (1 - Real.cos t) ≤
      Real.exp (↑m * -(δ ^ 2 / 24)) * rE t ^ 2 * 2 := by
    apply mul_le_mul (mul_le_mul_of_nonneg_right hpow (sq_nonneg _)) hcos2 hcos
    positivity
  have e2 : (m : ℝ) * -(δ ^ 2 / 24) = -((m : ℝ) * δ ^ 2 / 24) := by ring
  rw [e2] at h1
  linarith

/-- **Eq. (88)**, the inequality: for `D ≥ 2` and `0 < δ ≤ 1`,
`∫_{|t| ≥ δ} |r_E(t)|^D (1 − cos t) dt ≤ 4π / exp((D − 2)δ²/24)`. -/
theorem tail_bound (hL : L2Input) {D : ℕ} (hD : 2 ≤ D) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ t in {t : ℝ | δ ≤ |t|}, |rE t| ^ D * (1 - Real.cos t) ≤
      4 * π / Real.exp (((D : ℝ) - 2) * δ ^ 2 / 24) := by
  obtain ⟨hint, hval⟩ := hL
  set S := {t : ℝ | δ ≤ |t|} with hS
  have hSm : MeasurableSet S := (isClosed_le continuous_const continuous_abs).measurableSet
  set c := 2 * Real.exp (-(((D : ℝ) - 2) * δ ^ 2 / 24)) with hc
  have hg : Integrable (fun t => c * rE t ^ 2) := hint.const_mul c
  have hcont : Continuous (fun t => |rE t| ^ D * (1 - Real.cos t)) := by
    have := continuous_rE; fun_prop
  have hfS : IntegrableOn (fun t => |rE t| ^ D * (1 - Real.cos t)) S := by
    refine Integrable.mono' hg.integrableOn hcont.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' hSm).mpr (Filter.Eventually.of_forall (fun t ht => ?_))
    have h0 : 0 ≤ |rE t| ^ D * (1 - Real.cos t) :=
      mul_nonneg (pow_nonneg (abs_nonneg _) _) (by linarith [Real.cos_le_one t])
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact integrand_le hD hδ0 hδ1 ht
  calc ∫ t in S, |rE t| ^ D * (1 - Real.cos t)
      ≤ ∫ t in S, c * rE t ^ 2 :=
        setIntegral_mono_on hfS hg.integrableOn hSm (fun t ht => integrand_le hD hδ0 hδ1 ht)
    _ ≤ ∫ t, c * rE t ^ 2 :=
        setIntegral_le_integral hg (Filter.Eventually.of_forall (fun t => by positivity))
    _ = c * (2 * π) := by rw [integral_const_mul, hval]
    _ = 4 * π / Real.exp (((D : ℝ) - 2) * δ ^ 2 / 24) := by
        rw [hc, Real.exp_neg]; field_simp; ring

/-- `δ = D^{−2/5}` satisfies `0 < δ ≤ 1` and `D δ² = D^{1/5}`. -/
lemma delta_facts {D : ℕ} (hD : 1 ≤ D) :
    0 < (D : ℝ) ^ (-(2 / 5 : ℝ)) ∧ (D : ℝ) ^ (-(2 / 5 : ℝ)) ≤ 1 ∧
      (D : ℝ) * ((D : ℝ) ^ (-(2 / 5 : ℝ))) ^ 2 = (D : ℝ) ^ (1 / 5 : ℝ) := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  refine ⟨Real.rpow_pos_of_pos hD0 _, Real.rpow_le_one_of_one_le_of_nonpos hD1 (by norm_num), ?_⟩
  have h2 : ((D : ℝ) ^ (-(2 / 5 : ℝ))) ^ 2 = (D : ℝ) ^ (-(4 / 5 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; norm_num
  rw [h2]
  calc (D : ℝ) * (D : ℝ) ^ (-(4 / 5 : ℝ)) = (D : ℝ) ^ (1 : ℝ) * (D : ℝ) ^ (-(4 / 5 : ℝ)) := by
        rw [Real.rpow_one]
    _ = (D : ℝ) ^ ((1 : ℝ) + -(4 / 5 : ℝ)) := (Real.rpow_add hD0 _ _).symm
    _ = (D : ℝ) ^ (1 / 5 : ℝ) := by norm_num

/-- **Eq. (88)**, the order of magnitude: `4π / exp((D − 2)δ²/24) = O(e^{−D^{1/5}/25})` for
`δ = D^{−2/5}`; explicitly, with `C = 4π e^{1/12}`, for every `D ≥ 2`. -/
theorem tail_order :
    ∃ C : ℝ, ∀ D : ℕ, 2 ≤ D →
      4 * π / Real.exp (((D : ℝ) - 2) * ((D : ℝ) ^ (-(2 / 5 : ℝ))) ^ 2 / 24) ≤
        C * Real.exp (-((D : ℝ) ^ (1 / 5 : ℝ) / 25)) := by
  refine ⟨4 * π * Real.exp (1 / 12), fun D hD => ?_⟩
  obtain ⟨hδ0, hδ1, hDδ⟩ := delta_facts (D := D) (by omega)
  set δ := (D : ℝ) ^ (-(2 / 5 : ℝ))
  set x := (D : ℝ) ^ (1 / 5 : ℝ)
  have hx0 : 0 ≤ x := Real.rpow_nonneg (by positivity) _
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith
  -- `(D − 2)δ²/24 ≥ (x − 2)/24 ≥ x/25 − 1/12`
  have key : -(((D : ℝ) - 2) * δ ^ 2 / 24) ≤ 1 / 12 + -(x / 25) := by
    have : ((D : ℝ) - 2) * δ ^ 2 = x - 2 * δ ^ 2 := by rw [← hDδ]; ring
    rw [this]
    nlinarith
  calc 4 * π / Real.exp (((D : ℝ) - 2) * δ ^ 2 / 24)
      = 4 * π * Real.exp (-(((D : ℝ) - 2) * δ ^ 2 / 24)) := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
    _ ≤ 4 * π * Real.exp (1 / 12 + -(x / 25)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr key) (by positivity)
    _ = 4 * π * Real.exp (1 / 12) * Real.exp (-(x / 25)) := by rw [Real.exp_add]; ring

/-- **Eq. (88)** as printed: with `δ = D^{−2/5}`, for every `D ≥ 2`,
`∫_{|t| ≥ δ} |r_E(t)|^D (1 − cos t) dt ≤ 4π / exp((D − 2)δ²/24)`, and the right-hand side is
`O(e^{−D^{1/5}/25})`. -/
theorem eq88 (hL : L2Input) :
    (∀ D : ℕ, 2 ≤ D →
      ∫ t in {t : ℝ | (D : ℝ) ^ (-(2 / 5 : ℝ)) ≤ |t|}, |rE t| ^ D * (1 - Real.cos t) ≤
        4 * π / Real.exp (((D : ℝ) - 2) * ((D : ℝ) ^ (-(2 / 5 : ℝ))) ^ 2 / 24)) ∧
    ∃ C : ℝ, ∀ D : ℕ, 2 ≤ D →
      4 * π / Real.exp (((D : ℝ) - 2) * ((D : ℝ) ^ (-(2 / 5 : ℝ))) ^ 2 / 24) ≤
        C * Real.exp (-((D : ℝ) ^ (1 / 5 : ℝ) / 25)) := by
  refine ⟨fun D hD => ?_, tail_order⟩
  obtain ⟨hδ0, hδ1, -⟩ := delta_facts (D := D) (by omega)
  exact tail_bound hL hD hδ0 hδ1

end V001Cert
