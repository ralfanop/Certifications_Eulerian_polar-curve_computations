import Mathlib

/-!
# Manuscript 14, Theorem 9.3 and Corollary 9.4: the measure part of the Bloch map

This module kernel-checks the measure-theoretic content of Theorem 9.3 and Corollary 9.4 of
manuscript 14 ("Eulerian Fourier profiles at the special point i/√2"), whose algebraic part
(`ω_B ∘ Θ = -ω_B`, `|ω_B| = 1`, the time reversal `Θ`) is in `Section89Certificate`.

In the affine coordinate `ζ = ψ₁/ψ₀` of `ℂP¹` (the point `ζ = ∞` is a null set), the
unitarily invariant probability measure of pure spin states is `μ = π⁻¹ (1 + |ζ|²)⁻² d²ζ`, and the
Bloch map is
`ω_B(ζ) = (2 Re ζ, 2 Im ζ, 1 - |ζ|²)/(1 + |ζ|²)`.

* `lintegral_bloch_coords`: for every measurable `g ≥ 0` on `ℝ × ℝ`,
  `∫ g(ω₃(ζ), arg ζ) dμ(ζ) = (4π)⁻¹ ∫_{-1}^{1} ∫_{-π}^{π} g(w, φ) dφ dw`;
  equivalently (`map_bloch_coords`) the image of `μ` under `ζ ↦ (ω₃(ζ), arg ζ)` is
  `(4π)⁻¹ dw dφ` on `(-1, 1) × (-π, π)`. By `azimuth_ω1`, `azimuth_ω2` these are the axial
  coordinate and the azimuth of `ω_B(ζ) ∈ S²`, in which the surface measure is `dΩ = dw dφ`
  (Archimedes; the first classical input of Section 2.2), so that `(ω_B)_* μ = dΩ/(4π)`, (131).
* `μFS_univ`: `μ` is a probability measure.
* `lintegral_axial`: the axial component `ω₃` is uniform on `(-1, 1)` under `μ`.
* `partition_function`, `partition_special`: Corollary 9.4, (132) and (133):
  `∫ exp(x ω₃) dμ = sinh x / x`, and at `x = -1/√8` this is `sinh(a)/a = r_E(z₀)`.
* `mean_axial`: the mean of `ω₃` under the weight `e^{x ω₃} dμ` is the Langevin function
  `L(x) = coth x - 1/x`.
* `ω3_Θ`, `axial_Θ_invariant`: time reversal `ζ ↦ -1/ζ̄` reverses `ω₃` and leaves its law
  under `μ` invariant.
* `bloch_sphere`, `ω3_gt`, `chartInv_bloch`, `bloch_chartInv`: the Bloch map sends `ℂ` onto the
  sphere minus the south pole, with inverse `(ω₁ + i ω₂)/(1 + ω₃)`.

The proof uses Mathlib's polar coordinates on `ℂ` and the one-dimensional change of variables
`r ↦ (1 - r²)/(1 + r²)` on `(0, ∞)`. Not formalised here: the extension of the Bloch map to
`ζ = ∞` and the compactness argument making it a homeomorphism `ℂP¹ → S²`, and Archimedes'
identification of the surface measure in the coordinates `(ω₃, φ)`; both are classical inputs.
-/

open MeasureTheory Set Filter
open scoped ENNReal Real

noncomputable section

namespace Manuscript14BlochMeasure

/-! ## The Bloch map in the affine coordinate -/

/-- First component `2 Re ζ/(1 + |ζ|²)`. -/
def ω1 (ζ : ℂ) : ℝ := 2 * ζ.re / (1 + ‖ζ‖ ^ 2)

/-- Second component `2 Im ζ/(1 + |ζ|²)`. -/
def ω2 (ζ : ℂ) : ℝ := 2 * ζ.im / (1 + ‖ζ‖ ^ 2)

/-- Axial component `(1 - |ζ|²)/(1 + |ζ|²)`, the expectation of `σ₃`. -/
def ω3 (ζ : ℂ) : ℝ := (1 - ‖ζ‖ ^ 2) / (1 + ‖ζ‖ ^ 2)

/-- The density `π⁻¹ (1 + |ζ|²)⁻²` of the unitarily invariant measure of pure states. -/
def dens (ζ : ℂ) : ℝ≥0∞ := ENNReal.ofReal (1 / (π * (1 + ‖ζ‖ ^ 2) ^ 2))

/-- The unitarily invariant (Fubini–Study) measure of pure spin states in the affine chart. -/
def μFS : Measure ℂ := volume.withDensity dens

/-- The radial profile of `ω₃`. -/
def w (r : ℝ) : ℝ := (1 - r ^ 2) / (1 + r ^ 2)

/-- Its derivative. -/
def w' (r : ℝ) : ℝ := -(4 * r) / (1 + r ^ 2) ^ 2

theorem norm_sq_eq (ζ : ℂ) : ζ.re ^ 2 + ζ.im ^ 2 = ‖ζ‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem continuous_ω3 : Continuous ω3 := by
  unfold ω3
  exact Continuous.div (by fun_prop) (by fun_prop) (fun ζ => by positivity)

theorem continuous_w : Continuous w := by
  unfold w
  exact Continuous.div (by fun_prop) (by fun_prop) (fun r => by positivity)

theorem measurable_dens : Measurable dens := by
  unfold dens
  refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
  exact Continuous.div continuous_const (by fun_prop) (fun ζ => by positivity)

/-- `ω_B(ζ)` lies on the unit sphere. -/
theorem bloch_sphere (ζ : ℂ) : ω1 ζ ^ 2 + ω2 ζ ^ 2 + ω3 ζ ^ 2 = 1 := by
  have hpos : 0 < 1 + ‖ζ‖ ^ 2 := by positivity
  have e : ω1 ζ ^ 2 + ω2 ζ ^ 2 + ω3 ζ ^ 2 =
      (4 * (ζ.re ^ 2 + ζ.im ^ 2) + (1 - ‖ζ‖ ^ 2) ^ 2) / (1 + ‖ζ‖ ^ 2) ^ 2 := by
    unfold ω1 ω2 ω3
    rw [div_pow, div_pow, div_pow]
    ring
  rw [e, norm_sq_eq, div_eq_one_iff_eq (by positivity)]
  ring

/-- `ω₃ > -1`: the affine chart misses only the south pole. -/
theorem ω3_gt (ζ : ℂ) : -1 < ω3 ζ := by
  have hpos : 0 < 1 + ‖ζ‖ ^ 2 := by positivity
  unfold ω3
  rw [lt_div_iff₀ hpos]
  linarith

theorem one_add_ω3 (ζ : ℂ) : 1 + ω3 ζ = 2 / (1 + ‖ζ‖ ^ 2) := by
  have hpos : (1 + ‖ζ‖ ^ 2) ≠ 0 := by positivity
  unfold ω3
  first
    | (field_simp; ring)
    | field_simp

/-- The inverse chart `(ω₁ + i ω₂)/(1 + ω₃)`. -/
def chartInv (v : ℝ × ℝ × ℝ) : ℂ := ⟨v.1 / (1 + v.2.2), v.2.1 / (1 + v.2.2)⟩

theorem chartInv_bloch (ζ : ℂ) : chartInv (ω1 ζ, ω2 ζ, ω3 ζ) = ζ := by
  have hpos : (1 + ‖ζ‖ ^ 2) ≠ 0 := by positivity
  apply Complex.ext
  · simp only [chartInv]
    rw [one_add_ω3]
    unfold ω1
    field_simp
  · simp only [chartInv]
    rw [one_add_ω3]
    unfold ω2
    field_simp

theorem bloch_chartInv (v : ℝ × ℝ × ℝ) (hv : v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = 1)
    (hs : v.2.2 ≠ -1) :
    ω1 (chartInv v) = v.1 ∧ ω2 (chartInv v) = v.2.1 ∧ ω3 (chartInv v) = v.2.2 := by
  obtain ⟨a, b, c⟩ := v
  simp only at hv hs ⊢
  have hc : 1 + c ≠ 0 := fun h => hs (by linarith)
  have hab : a ^ 2 + b ^ 2 = 1 - c ^ 2 := by linarith
  have hn : ‖chartInv (a, b, c)‖ ^ 2 = (1 - c) / (1 + c) := by
    rw [← norm_sq_eq]
    simp only [chartInv]
    rw [div_pow, div_pow, ← add_div, hab, div_eq_div_iff (pow_ne_zero 2 hc) hc]
    ring
  refine ⟨?_, ?_, ?_⟩
  · unfold ω1
    rw [hn]
    simp only [chartInv]
    first
      | (field_simp; ring)
      | field_simp
  · unfold ω2
    rw [hn]
    simp only [chartInv]
    first
      | (field_simp; ring)
      | field_simp
  · unfold ω3
    rw [hn]
    first
      | (field_simp; ring)
      | field_simp

/-- The azimuth of `ω_B(ζ)` is `arg ζ`: `ω₁ = √(1 - ω₃²) cos(arg ζ)`. -/
theorem azimuth_ω1 (ζ : ℂ) : ω1 ζ = Real.sqrt (1 - ω3 ζ ^ 2) * Real.cos (Complex.arg ζ) := by
  have hpos : 0 < 1 + ‖ζ‖ ^ 2 := by positivity
  have hs : 1 - ω3 ζ ^ 2 = (2 * ‖ζ‖ / (1 + ‖ζ‖ ^ 2)) ^ 2 := by
    unfold ω3
    rw [div_pow, div_pow, eq_div_iff (by positivity)]
    first
      | (field_simp; ring)
      | field_simp
  rw [hs, Real.sqrt_sq (by positivity), mul_comm, ← mul_div_assoc, mul_comm (Real.cos _),
    mul_assoc, Complex.norm_mul_cos_arg]
  unfold ω1
  ring

/-- `ω₂ = √(1 - ω₃²) sin(arg ζ)`. -/
theorem azimuth_ω2 (ζ : ℂ) : ω2 ζ = Real.sqrt (1 - ω3 ζ ^ 2) * Real.sin (Complex.arg ζ) := by
  have hpos : 0 < 1 + ‖ζ‖ ^ 2 := by positivity
  have hs : 1 - ω3 ζ ^ 2 = (2 * ‖ζ‖ / (1 + ‖ζ‖ ^ 2)) ^ 2 := by
    unfold ω3
    rw [div_pow, div_pow, eq_div_iff (by positivity)]
    first
      | (field_simp; ring)
      | field_simp
  rw [hs, Real.sqrt_sq (by positivity), mul_comm, ← mul_div_assoc, mul_comm (Real.sin _),
    mul_assoc, Complex.norm_mul_sin_arg]
  unfold ω2
  ring

/-! ## The radial change of variables -/

theorem hasDerivAt_w (r : ℝ) : HasDerivAt w (w' r) r := by
  have h1 : HasDerivAt (fun r : ℝ => 1 - r ^ 2) (-(2 * r)) r := by
    simpa using (hasDerivAt_pow 2 r).const_sub 1
  have h2 : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).const_add 1
  have hd : (1 + r ^ 2) ≠ 0 := by positivity
  have h := h1.div h2 hd
  unfold w w'
  convert h using 1
  first
    | (field_simp; ring)
    | field_simp

theorem abs_w' {r : ℝ} (hr : 0 < r) : |w' r| = 4 * r / (1 + r ^ 2) ^ 2 := by
  have hneg : w' r < 0 := by
    unfold w'
    apply div_neg_of_neg_of_pos (by linarith) (by positivity)
  rw [abs_of_neg hneg]
  unfold w'
  ring

theorem w_image : w '' Ioi 0 = Ioo (-1) 1 := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hr' : (0 : ℝ) < r := hr
    have hd : 0 < 1 + r ^ 2 := by positivity
    have hr2 : 0 < r ^ 2 := by positivity
    unfold w
    constructor
    · rw [lt_div_iff₀ hd]
      linarith
    · rw [div_lt_one hd]
      linarith
  · rintro ⟨h1, h2⟩
    have hq : 0 < (1 - y) / (1 + y) := div_pos (by linarith) (by linarith)
    refine ⟨Real.sqrt ((1 - y) / (1 + y)), Real.sqrt_pos.mpr hq, ?_⟩
    have h1y : (1 + y) ≠ 0 := by linarith
    unfold w
    rw [Real.sq_sqrt hq.le]
    first
      | (field_simp; ring)
      | field_simp

theorem w_injOn : InjOn w (Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have hda : (1 + a ^ 2) ≠ 0 := by positivity
  have hdb : (1 + b ^ 2) ≠ 0 := by positivity
  unfold w at hab
  rw [div_eq_div_iff hda hdb] at hab
  have hsq : a ^ 2 = b ^ 2 := by linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha' hb']

/-- On the polar target, `‖ζ‖ = r` and `arg ζ = θ`. -/
theorem polar_norm_arg {p : ℝ × ℝ} (hp : p ∈ polarCoord.target) :
    ‖Complex.polarCoord.symm p‖ = p.1 ∧ Complex.arg (Complex.polarCoord.symm p) = p.2 := by
  have h := Complex.polarCoord.right_inv (show p ∈ Complex.polarCoord.target from hp)
  rw [Complex.polarCoord_apply] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-! ## Theorem 9.3: the image of the invariant measure -/

/-- **Theorem 9.3**, (131), in the coordinates `(ω₃, φ)` of the sphere: for every measurable
`g ≥ 0`, `∫ g(ω₃(ζ), arg ζ) dμ = (4π)⁻¹ ∫_{-1}^{1} ∫_{-π}^{π} g(w, φ) dφ dw`. -/
theorem lintegral_bloch_coords (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ ζ, g (ω3 ζ, Complex.arg ζ) ∂μFS =
      ENNReal.ofReal (1 / (4 * π)) * ∫⁻ y in Ioo (-1 : ℝ) 1, ∫⁻ θ in Ioo (-π) π, g (y, θ) := by
  have hΦ : Measurable fun ζ : ℂ => g (ω3 ζ, Complex.arg ζ) :=
    hg.comp (continuous_ω3.measurable.prodMk Complex.measurable_arg)
  rw [μFS, lintegral_withDensity_eq_lintegral_mul _ measurable_dens hΦ,
    ← Complex.lintegral_comp_polarCoord_symm]
  have hT : MeasurableSet (polarCoord.target) := polarCoord.open_target.measurableSet
  have hcongr : EqOn (fun p : ℝ × ℝ => ENNReal.ofReal p.1 •
        (dens * fun ζ : ℂ => g (ω3 ζ, Complex.arg ζ)) (Complex.polarCoord.symm p))
      (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 / (π * (1 + p.1 ^ 2) ^ 2)) * g (w p.1, p.2))
      polarCoord.target := by
    intro p hp
    obtain ⟨h1, h2⟩ := polar_norm_arg hp
    have hr : 0 < p.1 := hp.1
    simp only [Pi.mul_apply, smul_eq_mul, dens, ω3, h1, h2]
    rw [← mul_assoc, ← ENNReal.ofReal_mul hr.le, mul_one_div]
    rfl
  rw [setLIntegral_congr_fun hT hcongr]
  have hF : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (p.1 / (π * (1 + p.1 ^ 2) ^ 2)) * g (w p.1, p.2) := by
    refine Measurable.mul ?_ ?_
    · refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
      exact Continuous.div (by fun_prop) (by fun_prop) (fun p => by positivity)
    · exact hg.comp ((continuous_w.measurable.comp measurable_fst).prodMk measurable_snd)
  rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ hF.aemeasurable]
  dsimp only
  have hinner : ∀ r : ℝ,
      (∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (r / (π * (1 + r ^ 2) ^ 2)) * g (w r, θ)) =
        ENNReal.ofReal (r / (π * (1 + r ^ 2) ^ 2)) * ∫⁻ θ in Ioo (-π) π, g (w r, θ) :=
    fun r => lintegral_const_mul _ (hg.comp (measurable_const.prodMk measurable_id))
  simp_rw [hinner]
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun r _ => (hasDerivAt_w r).hasDerivWithinAt) w_injOn
    (fun y => ∫⁻ θ in Ioo (-π) π, g (y, θ))
  rw [w_image] at hcv
  try dsimp only at hcv
  rw [hcv, ← lintegral_const_mul' (ENNReal.ofReal (1 / (4 * π))) _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hr' : (0 : ℝ) < r := hr
  dsimp only
  rw [abs_w' hr', ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  first
    | (field_simp; ring)
    | field_simp

/-- **Theorem 9.3**, (131): the image of `μ` under `ζ ↦ (ω₃(ζ), arg ζ)` is `(4π)⁻¹ dw dφ`. -/
theorem map_bloch_coords :
    Measure.map (fun ζ : ℂ => (ω3 ζ, Complex.arg ζ)) μFS =
      ENNReal.ofReal (1 / (4 * π)) • volume.restrict (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-π) π) := by
  have hΦ : Measurable fun ζ : ℂ => (ω3 ζ, Complex.arg ζ) :=
    continuous_ω3.measurable.prodMk Complex.measurable_arg
  ext s hs
  rw [Measure.map_apply hΦ hs, Measure.smul_apply, smul_eq_mul]
  have h := lintegral_bloch_coords (s.indicator 1) (measurable_one.indicator hs)
  have hR : (∫⁻ y in Ioo (-1 : ℝ) 1, ∫⁻ θ in Ioo (-π) π, s.indicator 1 (y, θ)) =
      (volume.restrict (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-π) π)) s := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
      ← lintegral_prod _ ((measurable_one.indicator hs).aemeasurable), lintegral_indicator_one hs]
  rw [← hR, ← h, ← lintegral_indicator_one (hΦ hs)]
  apply lintegral_congr
  intro ζ
  classical
  first
    | rfl
    | simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]

/-- `μ` is a probability measure. -/
theorem μFS_univ : μFS univ = 1 := by
  have h := lintegral_bloch_coords (fun _ => 1) measurable_const
  have e1 : (∫⁻ _θ in Ioo (-π) π, (1 : ℝ≥0∞)) = ENNReal.ofReal (2 * π) := by
    rw [setLIntegral_const, one_mul, Real.volume_Ioo]
    congr 1
    ring
  have e2 : (∫⁻ _y in Ioo (-1 : ℝ) 1, ENNReal.ofReal (2 * π)) =
      ENNReal.ofReal (2 * π) * ENNReal.ofReal 2 := by
    rw [setLIntegral_const, Real.volume_Ioo]
    congr 2
    ring
  have h4 : (1 : ℝ) / (4 * π) * (2 * π * 2) = 1 := by
    first
      | (field_simp; ring)
      | field_simp
  calc μFS univ = ∫⁻ _ζ, (1 : ℝ≥0∞) ∂μFS := (lintegral_one).symm
    _ = ENNReal.ofReal (1 / (4 * π)) *
        ∫⁻ _y in Ioo (-1 : ℝ) 1, ∫⁻ _θ in Ioo (-π) π, (1 : ℝ≥0∞) := h
    _ = ENNReal.ofReal (1 / (4 * π)) * (ENNReal.ofReal (2 * π) * ENNReal.ofReal 2) := by
        rw [e1, e2]
    _ = 1 := by
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * π by positivity),
          ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / (4 * π) by positivity), h4, ENNReal.ofReal_one]

instance : IsProbabilityMeasure μFS := ⟨μFS_univ⟩

/-- The axial component `ω₃` is uniform on `(-1, 1)` under `μ` (Archimedes' law). -/
theorem lintegral_axial (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ ζ, h (ω3 ζ) ∂μFS = ENNReal.ofReal (1 / 2) * ∫⁻ y in Ioo (-1 : ℝ) 1, h y := by
  have H := lintegral_bloch_coords (fun p => h p.1) (hh.comp measurable_fst)
  have e : ∀ y : ℝ, (∫⁻ _θ in Ioo (-π) π, h y) = h y * ENNReal.ofReal (2 * π) := by
    intro y
    rw [setLIntegral_const, Real.volume_Ioo]
    congr 2
    ring
  have h4 : (1 : ℝ) / (4 * π) * (2 * π) = 1 / 2 := by
    first
      | (field_simp; ring)
      | field_simp
  calc ∫⁻ ζ, h (ω3 ζ) ∂μFS =
        ENNReal.ofReal (1 / (4 * π)) * ∫⁻ y in Ioo (-1 : ℝ) 1, ∫⁻ _θ in Ioo (-π) π, h y := H
    _ = ENNReal.ofReal (1 / (4 * π)) * ∫⁻ y in Ioo (-1 : ℝ) 1, h y * ENNReal.ofReal (2 * π) := by
        simp_rw [e]
    _ = ENNReal.ofReal (1 / (4 * π)) * ((∫⁻ y in Ioo (-1 : ℝ) 1, h y) * ENNReal.ofReal (2 * π)) := by
        rw [lintegral_mul_const _ hh]
    _ = ENNReal.ofReal (1 / 2) * ∫⁻ y in Ioo (-1 : ℝ) 1, h y := by
        rw [mul_comm (∫⁻ y in Ioo (-1 : ℝ) 1, h y), ← mul_assoc,
          ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / (4 * π) by positivity), h4]

/-! ## Corollary 9.4: partition function and magnetisation as averages over pure states -/

theorem integral_exp_mul (x : ℝ) (hx : x ≠ 0) :
    ∫ y in Ioo (-1 : ℝ) 1, Real.exp (x * y) = 2 * Real.sinh x / x := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
  have hd : ∀ y ∈ uIcc (-1 : ℝ) 1,
      HasDerivAt (fun y => Real.exp (x * y) / x) (Real.exp (x * y)) y := by
    intro y _
    have h := ((hasDerivAt_id y).const_mul x).exp.div_const x
    simp only [id, mul_one] at h
    convert h using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun y => Real.exp (x * y)).intervalIntegrable _ _)]
  simp only [mul_one, mul_neg]
  rw [Real.sinh_eq]
  first
    | (field_simp; ring)
    | field_simp

theorem integral_one_add_mul_exp (x : ℝ) (hx : x ≠ 0) :
    ∫ y in Ioo (-1 : ℝ) 1, (1 + y) * Real.exp (x * y) =
      2 * (Real.sinh x / x + Real.cosh x / x - Real.sinh x / x ^ 2) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
  have hd : ∀ y ∈ uIcc (-1 : ℝ) 1,
      HasDerivAt (fun y => Real.exp (x * y) * ((1 + y) / x - 1 / x ^ 2))
        ((1 + y) * Real.exp (x * y)) y := by
    intro y _
    have h1 := ((hasDerivAt_id y).const_mul x).exp
    have h2 : HasDerivAt (fun y : ℝ => (1 + y) / x - 1 / x ^ 2) (1 / x) y := by
      have := (((hasDerivAt_id y).const_add 1).div_const x).sub_const (1 / x ^ 2)
      simpa using this
    have h := h1.mul h2
    simp only [id, mul_one] at h
    convert h using 1
    first
      | (field_simp; ring)
      | field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun y => (1 + y) * Real.exp (x * y)).intervalIntegrable _ _)]
  simp only [mul_one, mul_neg]
  rw [Real.sinh_eq, Real.cosh_eq]
  first
    | (field_simp; ring)
    | field_simp

/-- **Corollary 9.4**, (132): `∫ exp(x ω₃) dμ = sinh x / x`. -/
theorem partition_function (x : ℝ) (hx : x ≠ 0) :
    ∫⁻ ζ, ENNReal.ofReal (Real.exp (x * ω3 ζ)) ∂μFS = ENNReal.ofReal (Real.sinh x / x) := by
  have hm : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (x * y)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun y : ℝ => Real.exp (x * y)).measurable
  rw [lintegral_axial _ hm]
  have hint : IntegrableOn (fun y : ℝ => Real.exp (x * y)) (Ioo (-1) 1) :=
    ((by fun_prop : Continuous fun y : ℝ => Real.exp (x * y)).integrableOn_Icc).mono_set
      Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall (fun y => (Real.exp_pos _).le)), integral_exp_mul x hx,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  field_simp

/-- **Corollary 9.4**, (133): at `x = -1/√8` the average is `sinh(a)/a = r_E(z₀)`, `a = 1/√8`. -/
theorem partition_special :
    ∫⁻ ζ, ENNReal.ofReal (Real.exp (-(ω3 ζ / Real.sqrt 8))) ∂μFS =
      ENNReal.ofReal (Real.sinh (1 / Real.sqrt 8) / (1 / Real.sqrt 8)) := by
  have h8 : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hx : (-(1 / Real.sqrt 8)) ≠ 0 := by
    have : 0 < 1 / Real.sqrt 8 := by positivity
    linarith
  have h := partition_function (-(1 / Real.sqrt 8)) hx
  have e : ∀ ζ : ℂ, -(ω3 ζ / Real.sqrt 8) = -(1 / Real.sqrt 8) * ω3 ζ := by
    intro ζ
    ring
  simp_rw [e]
  rw [h, Real.sinh_neg, neg_div_neg_eq]

/-- The Langevin function `L(x) = coth x - 1/x`. -/
def L (x : ℝ) : ℝ := Real.cosh x / Real.sinh x - 1 / x

/-- **Corollary 9.4**: under the weight `e^{x ω₃} dμ` the mean of `ω₃` is `L(x)`; in the form
`∫ (1 + ω₃) e^{x ω₃} dμ = (1 + L(x)) ∫ e^{x ω₃} dμ`, with both sides positive. -/
theorem mean_axial (x : ℝ) (hx : x ≠ 0) :
    ∫⁻ ζ, ENNReal.ofReal ((1 + ω3 ζ) * Real.exp (x * ω3 ζ)) ∂μFS =
      ENNReal.ofReal ((1 + L x) * (Real.sinh x / x)) := by
  have hm : Measurable fun y : ℝ => ENNReal.ofReal ((1 + y) * Real.exp (x * y)) :=
    ENNReal.measurable_ofReal.comp
      (by fun_prop : Continuous fun y : ℝ => (1 + y) * Real.exp (x * y)).measurable
  rw [lintegral_axial _ hm]
  have hint : IntegrableOn (fun y : ℝ => (1 + y) * Real.exp (x * y)) (Ioo (-1) 1) :=
    ((by fun_prop : Continuous fun y : ℝ => (1 + y) * Real.exp (x * y)).integrableOn_Icc).mono_set
      Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] fun y : ℝ => (1 + y) * Real.exp (x * y) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun y hy => ?_)
    have : 0 < 1 + y := by linarith [hy.1]
    exact (mul_pos this (Real.exp_pos _)).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_one_add_mul_exp x hx,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  have hs : Real.sinh x ≠ 0 := by
    intro h
    exact hx (Real.sinh_eq_zero.mp h)
  unfold L
  first
    | (field_simp; ring)
    | field_simp

/-! ## Time reversal and the axial law -/

/-- Time reversal on the affine coordinate, `ζ ↦ -1/ζ̄` (Lemma 9.2). -/
def Θc (ζ : ℂ) : ℂ := -1 / (starRingEnd ℂ ζ)

theorem ω3_Θ (ζ : ℂ) (hζ : ζ ≠ 0) : ω3 (Θc ζ) = -ω3 ζ := by
  have hn : ‖Θc ζ‖ = 1 / ‖ζ‖ := by
    unfold Θc
    rw [norm_div, norm_neg, norm_one, Complex.norm_conj]
  have h0 : ‖ζ‖ ≠ 0 := norm_ne_zero_iff.mpr hζ
  have hpos : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  unfold ω3
  rw [hn]
  have hd1 : (1 + ‖ζ‖ ^ 2) ≠ 0 := by positivity
  first
    | (field_simp; ring)
    | field_simp

theorem μFS_ae_ne_zero : ∀ᵐ ζ ∂μFS, ζ ≠ 0 := by
  have h0 : μFS {0} = 0 :=
    (withDensity_absolutelyContinuous _ _) (measure_singleton 0)
  rw [ae_iff]
  convert h0 using 2
  ext ζ
  simp

theorem lintegral_Ioo_neg (h : ℝ → ℝ≥0∞) :
    ∫⁻ y in Ioo (-1 : ℝ) 1, h (-y) = ∫⁻ y in Ioo (-1 : ℝ) 1, h y := by
  have himg : Neg.neg '' Ioo (-1 : ℝ) 1 = Ioo (-1 : ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
    · intro hy
      exact ⟨-y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, neg_neg y⟩
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul
    (measurableSet_Ioo : MeasurableSet (Ioo (-1 : ℝ) 1))
    (fun y _ => (hasDerivAt_neg y).hasDerivWithinAt) neg_injective.injOn h
  rw [himg] at hcv
  rw [hcv]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro y _
  simp

/-- **Corollary 9.4**: time reversal leaves the law of `ω₃` under `μ` invariant. -/
theorem axial_Θ_invariant (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ ζ, h (ω3 (Θc ζ)) ∂μFS = ∫⁻ ζ, h (ω3 ζ) ∂μFS := by
  have hneg : Measurable fun y : ℝ => h (-y) := hh.comp measurable_neg
  calc ∫⁻ ζ, h (ω3 (Θc ζ)) ∂μFS = ∫⁻ ζ, h (-ω3 ζ) ∂μFS := by
        apply lintegral_congr_ae
        filter_upwards [μFS_ae_ne_zero] with ζ hζ
        rw [ω3_Θ ζ hζ]
    _ = ENNReal.ofReal (1 / 2) * ∫⁻ y in Ioo (-1 : ℝ) 1, h (-y) := lintegral_axial _ hneg
    _ = ENNReal.ofReal (1 / 2) * ∫⁻ y in Ioo (-1 : ℝ) 1, h y := by rw [lintegral_Ioo_neg]
    _ = ∫⁻ ζ, h (ω3 ζ) ∂μFS := (lintegral_axial _ hh).symm

/-! ## Axiom audit -/

#print axioms bloch_sphere
#print axioms ω3_gt
#print axioms chartInv_bloch
#print axioms bloch_chartInv
#print axioms azimuth_ω1
#print axioms azimuth_ω2
#print axioms lintegral_bloch_coords
#print axioms map_bloch_coords
#print axioms μFS_univ
#print axioms lintegral_axial
#print axioms partition_function
#print axioms partition_special
#print axioms mean_axial
#print axioms ω3_Θ
#print axioms axial_Θ_invariant

end Manuscript14BlochMeasure
