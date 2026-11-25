import Manuscript16.QuarticPartitionSusceptibility20261125
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Manuscript 17, Proposition 10.1 and Corollary 10.2 (cross connections, 25 Nov 2026)

Source: `Cyclohedral.tex` of `Manuscript_17_20261125_CROSS_CONNECTIONS.zip`, Section 10,
labels `eq:cross-lemLength`, `eq:cross-lemAmp`, `eq:cross-lemF`, `eq:cross-lemVac`,
`eq:cross-area17`, `eq:cross-Q17`.

What is proved here, without premises:
* `Fcrit_zero`: `F_crit(0) = 40^{1/4} Γ(1/4) / (4√π)` (this is also `eq:cross-Fzero` of
  Manuscript 12, `12.tex` line 2647);
* `lemF_gamma`: `2 √(π/5) F_crit(0)² = Γ(1/4)² / (2√(2π))`, the new content of `eq:cross-lemF`;
* `arctan_z0` and `cross_area17`: the principal-branch value `arctan(i/√2) = i log(1+√2)` and
  `π (1 - arctan z₀ / (2 z₀)) = π (1 - log(1+√2)/√2)` (`eq:cross-area17`).

Published results cited, entering only as named premises (classical, not re-proved):
* `GaussLemniscate`: `2 ∫₀¹ dt/√(1-t⁴) = Γ(1/4)² / (2√(2π))` (Gauss's evaluation of the
  lemniscate constant); the polar arclength of the lemniscate lobe (`eq:cross-lemLength`) and
  `√2 K(1/√2)` (`eq:cross-lemAmp`) are classical as well and are not formalized.

Results of Manuscript 12 entering as named premises (unpublished; they are not certified here):
* `eq:cross-vaczero` and `eq:cross-Qzero` of `12.tex` (lines 2650 and 2700);
  `cross_lemVac` and `cross_Q17` are the scalar consequences stated in Manuscript 17.
-/

open Real MeasureTheory Filter Set
open scoped Topology

namespace Manuscript17.CrossConnections20261125

open Manuscript16.QuarticPartition20261125

/-- `ℓ₊ = 2 ∫₀¹ dt / √(1 - t⁴)`, the integral of `eq:cross-lemLength`. -/
noncomputable def ellPlus : ℝ := 2 * ∫ t in (0 : ℝ)..1, 1 / √(1 - t ^ 4)

/-- Gauss's evaluation of the lemniscate constant (classical; a published result cited). -/
def GaussLemniscate : Prop := ellPlus = Gamma (1 / 4) ^ 2 / (2 * √(2 * π))

lemma integral_exp_quartic : ∫ u, exp (-V 0 u) = 2 * ((1 / 40 : ℝ) ^ (-1 / 4 : ℝ) * Gamma (5 / 4)) := by
  have h := integral_exp_neg_mul_rpow (p := 4) (b := 1 / 40) (by norm_num) (by norm_num)
  have habs := integral_comp_abs (f := fun x : ℝ => exp (-(1 / 40) * x ^ (4 : ℝ)))
  have e : (fun u : ℝ => exp (-V 0 u)) = fun u => exp (-(1 / 40) * |u| ^ (4 : ℝ)) := by
    funext u
    unfold V
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show |u| ^ 4 = u ^ 4 from by rw [pow_abs]; exact abs_of_nonneg (by positivity)]
    ring_nf
  rw [e, habs, h]
  norm_num

/-- `F_crit(0) = 40^{1/4} Γ(1/4) / (4√π)`. -/
theorem Fcrit_zero : Fcrit 0 = (40 : ℝ) ^ (1 / 4 : ℝ) * Gamma (1 / 4) / (4 * √π) := by
  rw [Fcrit_eq]
  have hm : mom 0 0 = ∫ u, exp (-V 0 u) := by unfold mom; simp
  rw [hm, integral_exp_quartic]
  have hG : Gamma (5 / 4) = (1 / 4) * Gamma (1 / 4) := by
    rw [show (5 / 4 : ℝ) = 1 / 4 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
  have h40 : (1 / 40 : ℝ) ^ (-1 / 4 : ℝ) = (40 : ℝ) ^ (1 / 4 : ℝ) := by
    rw [show (-1 / 4 : ℝ) = -(1 / 4) by norm_num, Real.rpow_neg (by norm_num),
      Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow]
    field_simp
  rw [hG, h40]
  have : √π ≠ 0 := by positivity
  field_simp

/-- The new content of `eq:cross-lemF`: `2 √(π/5) F_crit(0)² = Γ(1/4)² / (2√(2π))`. -/
theorem lemF_gamma : 2 * √(π / 5) * Fcrit 0 ^ 2 = Gamma (1 / 4) ^ 2 / (2 * √(2 * π)) := by
  rw [Fcrit_zero]
  have h40 : ((40 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = √40 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.sqrt_eq_rpow]
    norm_num
  have hpi : 0 < π := pi_pos
  have hs5 : √(π / 5) * √40 = 2 * √(2 * π) := by
    rw [← Real.sqrt_mul (by positivity), show π / 5 * 40 = 2 ^ 2 * (2 * π) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hsq : √(2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have hspi : √π ^ 2 = π := Real.sq_sqrt hpi.le
  have h2pi : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hpos : 0 < √π := Real.sqrt_pos.mpr hpi
  rw [div_pow, mul_pow, h40, mul_pow, hspi]
  field_simp
  rw [show (2:ℝ) ^ 2 * √(π / 5) * √40 * √(2 * π) = 4 * (√(π / 5) * √40) * √(2 * π) by ring, hs5]
  linear_combination 8 * hsq

/-- `eq:cross-lemF`, with Gauss's evaluation as the only (cited) premise. -/
theorem cross_lemF (hGauss : GaussLemniscate) : ellPlus = 2 * √(π / 5) * Fcrit 0 ^ 2 := by
  rw [lemF_gamma]; exact hGauss

/-! ## `eq:cross-area17` -/

/-- `z₀ = i/√2`. -/
noncomputable def z0 : ℂ := Complex.I / (√2 : ℝ)

lemma sqrt2_facts : (1 : ℝ) < √2 ∧ √2 ^ 2 = 2 := by
  refine ⟨?_, Real.sq_sqrt (by norm_num)⟩
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- Principal branch: `arctan(i/√2) = i log(1 + √2)`. -/
theorem arctan_z0 : Complex.arctan z0 = Complex.I * (Real.log (1 + √2) : ℝ) := by
  obtain ⟨h1, h2⟩ := sqrt2_facts
  set r : ℝ := √2 with hr
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (by linarith : r ≠ 0)
  have hr1 : (r : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : r + 1 ≠ 0)
  have hzI : z0 * Complex.I = -1 / (r : ℂ) := by
    unfold z0
    rw [← hr, div_mul_eq_mul_div, Complex.I_mul_I]
  have hq : (1 + z0 * Complex.I) / (1 - z0 * Complex.I) = (((r - 1) / (r + 1) : ℝ) : ℂ) := by
    rw [hzI]
    push_cast
    rw [neg_div, sub_neg_eq_add, ← sub_eq_add_neg]
    rw [show (1 : ℂ) - 1 / r = (r - 1) / r by field_simp,
        show (1 : ℂ) + 1 / r = (r + 1) / r by field_simp]
    rw [div_div_div_cancel_right₀ hr0]
  have hlog : Real.log ((r - 1) / (r + 1)) = -2 * Real.log (1 + r) := by
    have hpos : 0 < 1 + r := by linarith
    have : (r - 1) / (r + 1) = ((1 + r) ^ 2)⁻¹ := by
      have hr1 : r + 1 ≠ 0 := by linarith
      field_simp
      nlinarith
    rw [this, Real.log_inv, Real.log_pow]
    push_cast; ring
  unfold Complex.arctan
  rw [hq, ← Complex.ofReal_log (by
      have : 0 < (r - 1) / (r + 1) := div_pos (by linarith) (by linarith)
      exact this.le), hlog]
  push_cast
  ring_nf

/-- `arctan(z₀) / (2 z₀) = log(1 + √2) / √2`. -/
theorem arctan_z0_div : Complex.arctan z0 / (2 * z0) = ((Real.log (1 + √2) / √2 : ℝ) : ℂ) := by
  obtain ⟨h1, h2⟩ := sqrt2_facts
  rw [arctan_z0]
  unfold z0
  have hr0 : ((√2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : √2 ≠ 0)
  push_cast
  field_simp
  ring_nf
  have : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast h2
  rw [this]

/-- **`eq:cross-area17`**: `π (1 - arctan z₀ / (2 z₀)) = π (1 - log(1+√2)/√2)`, the area value of
`thm:m17-curvature-area` (`eq:m17-area`). -/
theorem cross_area17 :
    (π : ℂ) * (1 - Complex.arctan z0 / (2 * z0)) = ((π * (1 - Real.log (1 + √2) / √2) : ℝ) : ℂ) := by
  rw [arctan_z0_div]; push_cast; ring

/-! ## Scalar consequences of Manuscript 12 (`eq:cross-lemVac`, `eq:cross-Q17`) -/

lemma sqrt_eq_rpow_sq (M : ℝ) (hM : 0 ≤ M) : √M = (M ^ (1 / 4 : ℝ)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hM, Real.sqrt_eq_rpow]; norm_num

/-- **`eq:cross-lemVac`**, from `eq:cross-vaczero` of Manuscript 12 and Gauss's evaluation.
`p M` stands for `p_{E,M}(M/12)`. -/
theorem cross_lemVac (hGauss : GaussLemniscate) (p : ℕ → ℝ)
    (h12 : Tendsto (fun M : ℕ => (M : ℝ) ^ (1 / 4 : ℝ) * p M) atTop (𝓝 (1 / Fcrit 0))) :
    Tendsto (fun M : ℕ => √(M : ℝ) * p M ^ 2) atTop (𝓝 (2 / ellPlus * √(π / 5))) := by
  have hF := Fcrit_pos 0
  have hlim : 2 / ellPlus * √(π / 5) = (1 / Fcrit 0) ^ 2 := by
    rw [cross_lemF hGauss]
    have : √(π / 5) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp
  rw [hlim]
  refine (h12.pow 2).congr fun M => ?_
  rw [sqrt_eq_rpow_sq _ (Nat.cast_nonneg M)]; ring

/-- **`eq:cross-Q17`**, from `eq:cross-Qzero` of Manuscript 12 and Gauss's evaluation.
`Q M` stands for `𝒬_M(1/12)`. -/
theorem cross_Q17 (hGauss : GaussLemniscate) (Q : ℕ → ℝ)
    (h12 : Tendsto (fun M : ℕ => (M : ℝ) ^ (1 / 4 : ℝ) * (Q M - 1)) atTop
      (𝓝 (1 / (2 * (π ^ 2 + 1) * Fcrit 0)))) :
    Tendsto (fun M : ℕ => √(M : ℝ) * (Q M - 1) ^ 2) atTop
      (𝓝 (√(π / 5) / (2 * (π ^ 2 + 1) ^ 2 * ellPlus))) := by
  have hF := Fcrit_pos 0
  have hlim : √(π / 5) / (2 * (π ^ 2 + 1) ^ 2 * ellPlus) = (1 / (2 * (π ^ 2 + 1) * Fcrit 0)) ^ 2 := by
    rw [cross_lemF hGauss]
    have : √(π / 5) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have : π ^ 2 + 1 ≠ 0 := by positivity
    field_simp
  rw [hlim]
  refine (h12.pow 2).congr fun M => ?_
  rw [sqrt_eq_rpow_sq _ (Nat.cast_nonneg M)]; ring

end Manuscript17.CrossConnections20261125

#print axioms Manuscript17.CrossConnections20261125.Fcrit_zero
#print axioms Manuscript17.CrossConnections20261125.lemF_gamma
#print axioms Manuscript17.CrossConnections20261125.cross_lemF
#print axioms Manuscript17.CrossConnections20261125.arctan_z0
#print axioms Manuscript17.CrossConnections20261125.arctan_z0_div
#print axioms Manuscript17.CrossConnections20261125.cross_area17
#print axioms Manuscript17.CrossConnections20261125.cross_lemVac
#print axioms Manuscript17.CrossConnections20261125.cross_Q17
