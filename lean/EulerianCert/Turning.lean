/-
# Proposition 3.7 of the V001 manuscript: the smooth turning of the Eulerian curve, Eq. (39)

For the polar curve `γ(θ) = r(θ)(cos θ, sin θ)` the signed curvature density with respect to `θ`
is `κ ds = k(θ) dθ` with
  `k = (r² + 2r'² − r r'') / (r² + r'²)`.
For `r = r_E` we prove `∫_{-π}^{π} k(θ) dθ = 2π + ϑ_E`, `ϑ_E = 2 arctan(1/π) = 2 arccot π`
(Eq. (39)): `k = d/dθ [θ − arctan(r'/r)]` on `θ ≠ 0`, the function `θ − arctan(r'/r)` extends
continuously to `θ = 0` (because `|r_E'(θ)| ≤ |θ|/8`), and `k > 0` (Eq. (40)), so `k` is integrable
and the fundamental theorem of calculus applies on `[-π, 0]` and `[0, π]`.  Hence the
turning-tangents relation of the proof of Proposition 3.7 holds with the single exterior angle
`−ϑ_E`: `(2π + ϑ_E) − ϑ_E = 2π`.  The derivatives `r', r''` are those of `Corner`.
-/
import EulerianCert.Corner
import EulerianCert.FourierModes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Real Set intervalIntegral

noncomputable section

namespace EulerianCert.Turning

open EulerianCert.Corner (rE' rE'' varthetaE)

local notation "R" => EulerianCert.Corner.rE
local notation "ρ" => EulerianCert.FourierModes.rE

/-- The curvature density `k = (r² + 2r'² − r r'')/(r² + r'²)` of the polar curve. -/
def k (θ : ℝ) : ℝ := (R θ ^ 2 + 2 * rE' θ ^ 2 - R θ * rE'' θ) / (R θ ^ 2 + rE' θ ^ 2)

/-- `r_E'` extended by `0` at `θ = 0`. -/
def rp (θ : ℝ) : ℝ := if θ = 0 then 0 else rE' θ

lemma R_neg (θ : ℝ) : R (-θ) = R θ := by
  unfold EulerianCert.Corner.rE; simp only [neg_div, Real.sin_neg, Real.cos_neg]; ring

lemma rE'_neg (θ : ℝ) : rE' (-θ) = -rE' θ := by
  unfold EulerianCert.Corner.rE'; simp only [neg_div, Real.sin_neg, Real.cos_neg]; ring

lemma rE''_neg (θ : ℝ) : rE'' (-θ) = rE'' θ := by
  unfold EulerianCert.Corner.rE''; simp only [neg_div, Real.sin_neg, Real.cos_neg]; ring

lemma R_eq_ρ {θ : ℝ} (hθ : θ ≠ 0) : R θ = ρ θ := by
  rw [EulerianCert.FourierModes.rE_of_ne_zero hθ]; rfl

lemma ρ_pos {θ : ℝ} (hθ : θ ∈ Icc (-π) π) : 0 < ρ θ := by
  apply sinc_pos
  rw [abs_lt]; constructor <;> linarith [hθ.1, hθ.2, pi_pos]

lemma R_pos {θ : ℝ} (hθ : θ ∈ Icc (-π) π) (h0 : θ ≠ 0) : 0 < R θ := by
  rw [R_eq_ρ h0]; exact ρ_pos hθ

/-- `|r_E'(θ)| ≤ θ/8` for `0 < θ < π`. -/
lemma rE'_bound_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) : |rE' θ| ≤ θ / 8 := by
  have hx : |θ / 2| < π / 2 := by rw [abs_of_pos (by positivity)]; linarith [pi_pos]
  have h1 := cos_le_sinc hx
  have h2 := sinc_le_one (θ / 2)
  have h3 := one_sub_sq_div_two_le_cos (x := θ / 2)
  have e : rE' θ = (Real.cos (θ / 2) - sinc (θ / 2)) / θ := by
    unfold EulerianCert.Corner.rE'
    rw [sinc_of_ne_zero (by positivity)]
    field_simp
  rw [e, abs_div, abs_of_pos h0, div_le_div_iff₀ h0 (by norm_num), abs_of_nonpos (by linarith)]
  nlinarith

lemma rE'_bound {θ : ℝ} (h0 : θ ≠ 0) (hπ : |θ| < π) : |rE' θ| ≤ |θ| / 8 := by
  rcases lt_or_gt_of_ne h0 with h | h
  · have := rE'_bound_pos (θ := -θ) (by linarith) (by rw [abs_of_neg h] at hπ; linarith)
    rw [rE'_neg, abs_neg] at this
    simpa [abs_of_neg h] using this
  · rw [abs_of_pos h] at hπ ⊢; exact rE'_bound_pos h hπ

lemma continuousAt_rE' {θ : ℝ} (h0 : θ ≠ 0) : ContinuousAt rE' θ :=
  (EulerianCert.Corner.hasDerivAt_rE' h0).continuousAt

lemma continuousOn_rp : ContinuousOn rp (Icc (-π) π) := by
  intro θ hθ
  rcases eq_or_ne θ 0 with rfl | h0
  · rw [Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨min (8 * ε) π, by positivity, fun x _ hd => ?_⟩
    rw [Real.dist_eq, sub_zero] at hd
    have hd1 : |x| < 8 * ε := lt_of_lt_of_le hd (min_le_left _ _)
    have hd2 : |x| < π := lt_of_lt_of_le hd (min_le_right _ _)
    simp only [rp, Real.dist_eq]
    split_ifs with hx0
    · simpa using hε
    · rw [sub_zero]
      calc |rE' x| ≤ |x| / 8 := rE'_bound hx0 hd2
        _ < ε := by linarith
  · apply ContinuousAt.continuousWithinAt
    have : rp =ᶠ[nhds θ] rE' := by
      filter_upwards [isOpen_ne.mem_nhds h0] with t ht
      simp [rp, ht]
    exact (continuousAt_rE' h0).congr this.symm

/-- `g(θ) = θ − arctan(r_E'(θ)/r_E(θ))`, a primitive of `k`. -/
def g (θ : ℝ) : ℝ := θ - Real.arctan (rp θ / ρ θ)

lemma continuousOn_g : ContinuousOn g (Icc (-π) π) := by
  apply continuousOn_id.sub
  apply Real.continuous_arctan.comp_continuousOn
  apply continuousOn_rp.div EulerianCert.FourierModes.continuous_rE.continuousOn
  intro θ hθ; exact (ρ_pos hθ).ne'

lemma hasDerivAt_g {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) (h0 : θ ≠ 0) : HasDerivAt g (k θ) θ := by
  have hθ' : θ ∈ Icc (-π) π := Ioo_subset_Icc_self hθ
  have hR := R_pos hθ' h0
  have heq : g =ᶠ[nhds θ] (fun t => t - Real.arctan (rE' t / R t)) := by
    filter_upwards [isOpen_ne.mem_nhds h0] with t ht
    simp [g, rp, ht, R_eq_ρ ht]
  have hq : HasDerivAt (fun t => rE' t / R t)
      ((rE'' θ * R θ - rE' θ * rE' θ) / R θ ^ 2) θ :=
    (EulerianCert.Corner.hasDerivAt_rE' h0).div (EulerianCert.Corner.hasDerivAt_rE h0) hR.ne'
  have h := (hasDerivAt_id' θ).sub hq.arctan
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  convert h using 1
  unfold k
  have hd : R θ ^ 2 + rE' θ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

lemma k_nonneg {θ : ℝ} (hθ : θ ∈ Icc (-π) π) (h0 : θ ≠ 0) : 0 ≤ k θ := by
  unfold k
  apply div_nonneg _ (by positivity)
  rcases lt_or_gt_of_ne h0 with h | h
  · have := EulerianCert.Corner.curvature_numerator_pos (θ := -θ) (by linarith)
    rw [R_neg, rE'_neg, rE''_neg] at this
    nlinarith
  · exact (EulerianCert.Corner.curvature_numerator_pos h).le

lemma g_pi : g π = π + Real.arctan (1 / π) := by
  have hπ : π ≠ 0 := pi_ne_zero
  simp only [g, rp, if_neg hπ]
  rw [← R_eq_ρ hπ, EulerianCert.Corner.rE'_pi, EulerianCert.Corner.rE_pi]
  have : -2 / π ^ 2 / (2 / π) = -(1 / π) := by field_simp
  rw [this, Real.arctan_neg]; ring

lemma g_neg_pi : g (-π) = -π - Real.arctan (1 / π) := by
  have hπ : -π ≠ 0 := neg_ne_zero.2 pi_ne_zero
  simp only [g, rp, if_neg hπ]
  rw [← R_eq_ρ hπ, rE'_neg, R_neg, EulerianCert.Corner.rE'_pi, EulerianCert.Corner.rE_pi]
  have : π ≠ 0 := pi_ne_zero
  have e : -(-2 / π ^ 2) / (2 / π) = 1 / π := by field_simp
  rw [e]

lemma g_zero : g 0 = 0 := by simp [g, rp]

lemma integral_half_pos : (∫ θ in (0 : ℝ)..π, k θ) = π + Real.arctan (1 / π) := by
  have hc : ContinuousOn g (Icc 0 π) :=
    continuousOn_g.mono (Icc_subset_Icc (by linarith [pi_pos]) le_rfl)
  have hd : ∀ x ∈ Ioo (0 : ℝ) π, HasDerivAt g (k x) x := fun x hx =>
    hasDerivAt_g ⟨by linarith [hx.1, pi_pos], hx.2⟩ hx.1.ne'
  have hint : IntervalIntegrable k MeasureTheory.volume 0 π :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le pi_pos.le).2
      (integrableOn_deriv_of_nonneg hc hd (fun x hx =>
        k_nonneg ⟨by linarith [hx.1, pi_pos], hx.2.le⟩ hx.1.ne'))
  rw [integral_eq_sub_of_hasDerivAt_of_le pi_pos.le hc hd hint, g_pi, g_zero, sub_zero]

lemma integral_half_neg : (∫ θ in (-π)..0, k θ) = π + Real.arctan (1 / π) := by
  have hle : -π ≤ 0 := by linarith [pi_pos]
  have hc : ContinuousOn g (Icc (-π) 0) :=
    continuousOn_g.mono (Icc_subset_Icc le_rfl pi_pos.le)
  have hd : ∀ x ∈ Ioo (-π) (0 : ℝ), HasDerivAt g (k x) x := fun x hx =>
    hasDerivAt_g ⟨hx.1, by linarith [hx.2, pi_pos]⟩ hx.2.ne
  have hint : IntervalIntegrable k MeasureTheory.volume (-π) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).2
      (integrableOn_deriv_of_nonneg hc hd (fun x hx =>
        k_nonneg ⟨hx.1.le, by linarith [hx.2, pi_pos]⟩ hx.2.ne))
  rw [integral_eq_sub_of_hasDerivAt_of_le hle hc hd hint, g_zero, g_neg_pi]
  ring

lemma intervalIntegrable_k_pos : IntervalIntegrable k MeasureTheory.volume 0 π := by
  have h := integral_half_pos
  by_contra hn
  rw [intervalIntegral.integral_undef hn] at h
  have := Real.arctan_pos.2 (show (0 : ℝ) < 1 / π by positivity)
  linarith [pi_pos]

lemma intervalIntegrable_k_neg : IntervalIntegrable k MeasureTheory.volume (-π) 0 := by
  have h := integral_half_neg
  by_contra hn
  rw [intervalIntegral.integral_undef hn] at h
  have := Real.arctan_pos.2 (show (0 : ℝ) < 1 / π by positivity)
  linarith [pi_pos]

/-- **Proposition 3.7, Eq. (39)**: the smooth turning of `Γ_E` is `2π + ϑ_E`. -/
theorem smooth_turning : (∫ θ in (-π)..π, k θ) = 2 * π + varthetaE := by
  rw [← integral_add_adjacent_intervals intervalIntegrable_k_neg intervalIntegrable_k_pos,
    integral_half_neg, integral_half_pos, EulerianCert.Corner.varthetaE]
  ring

/-- The density `k` is positive on the smooth arc (Eq. (40)). -/
theorem k_pos {θ : ℝ} (hθ : θ ∈ Icc (-π) π) (h0 : θ ≠ 0) : 0 < k θ := by
  unfold k
  apply div_pos _ (by have := R_pos hθ h0; positivity)
  rcases lt_or_gt_of_ne h0 with h | h
  · have := EulerianCert.Corner.curvature_numerator_pos (θ := -θ) (by linarith)
    rw [R_neg, rE'_neg, rE''_neg] at this
    nlinarith
  · exact EulerianCert.Corner.curvature_numerator_pos h

end EulerianCert.Turning
