/-
# V001 Proposition 3.7: the curvature measures of the Eulerian curve, Eqs. (37)–(38)

Parameter circle `ℝ/2πℤ`, fundamental domain `(−π, π]`; the corner `p_E` is `θ = π ≡ −π`.
With `k` the smooth curvature density of `Turning` (`κ_E ds = k dθ`, `k > 0` off `θ = 0`),
`g = θ − β_E`, `β_E = arctan(r_E'/r_E)`, and the unit tangent `T_E = i e^{i g}` (which equals
`γ_E'/|γ_E'|` for `θ ≠ 0`), we prove:

* **signed tangent-angle measure** `dτ_E = κ_E ds − ϑ_E δ_{p_E}`: the signed measure
  `τ_E = k dθ − ϑ_E δ_π` on `(−π, π]` acts on every `C¹` periodic `φ` as the distributional
  derivative `dθ − dβ_E` of the tangent angle:
  `∫ φ dτ_E = ∫ φ dθ + ∫ φ' β_E dθ` (the corner turn `β_E(π⁻) − β_E(−π⁺) = −ϑ_E`);
* **scalar total-curvature measure** `dμ_TC = κ_E ds + ϑ_E δ_{p_E}`: `μ_TC` is the total variation
  `|τ_E|` (Mathlib's Jordan decomposition: `k dθ ⟂ δ_π`);
* **Sullivan's vector curvature measure** `dK_E = κ_E N ds + (T₊ − T₋) δ_{p_E}`: `K_E` is the
  distributional derivative `dT_E` on the circle,
  `−∫ φ' T_E dθ = ∫ φ T_E' dθ + φ(π)(T₊ − T₋)`, with `T_E' = i k T_E = κ_E N |γ_E'|`;
  `K_E` is also built as a `ℂ`-valued vector measure;
* **Eq. (38)**: `T₋ = T_E(π) = (1 − iπ)/√(1+π²)`, `T₊ = T_E(−π) = (−1 − iπ)/√(1+π²)`,
  `K_E{p_E} = −2/√(1+π²)`, `‖K_E{p_E}‖ = 2/√(1+π²) = 2 sin(ϑ_E/2)`; `τ_E{p_E} = −ϑ_E`,
  `μ_TC{p_E} = ϑ_E`.
-/
import EulerianCert.Turning
import EulerianCert.CurvatureGrowth
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open Real Set MeasureTheory intervalIntegral
open scoped ENNReal NNReal

noncomputable section

namespace EulerianCert.CurvatureMeasures

open EulerianCert.Corner (varthetaE rE')

local notation "ρ" => EulerianCert.FourierModes.rE
local notation "kE" => EulerianCert.Turning.k
local notation "gE" => EulerianCert.Turning.g

/-- `β_E = arctan(r_E'/r_E)` (with `r_E'(0) = 0`). -/
def β (θ : ℝ) : ℝ := Real.arctan (EulerianCert.Turning.rp θ / ρ θ)

lemma β_eq (θ : ℝ) : β θ = θ - gE θ := by unfold β EulerianCert.Turning.g; ring

lemma β_pi : β π = -Real.arctan (1 / π) := by rw [β_eq, EulerianCert.Turning.g_pi]; ring

lemma β_neg_pi : β (-π) = Real.arctan (1 / π) := by
  rw [β_eq, EulerianCert.Turning.g_neg_pi]; ring

lemma varthetaE_eq : varthetaE = 2 * Real.arctan (1 / π) := rfl

lemma varthetaE_nonneg : 0 ≤ varthetaE := by
  rw [varthetaE_eq]
  have := Real.arctan_pos.2 (show (0 : ℝ) < 1 / π by positivity); linarith

lemma intervalIntegrable_k : IntervalIntegrable kE volume (-π) π :=
  EulerianCert.Turning.intervalIntegrable_k_neg.trans EulerianCert.Turning.intervalIntegrable_k_pos

lemma mem_of_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) π) : x ∈ Ioo (-π) π :=
  ⟨by linarith [hx.1, pi_pos], hx.2⟩

lemma mem_of_neg {x : ℝ} (hx : x ∈ Ioo (-π) (0 : ℝ)) : x ∈ Ioo (-π) π :=
  ⟨hx.1, by linarith [hx.2, pi_pos]⟩

/-! ### The signed turning measure as a distribution -/

/-- `∫_{−π}^{π} (φ' g + φ k) = φ(π) g(π) − φ(−π) g(−π)` (FTC on the two smooth halves). -/
lemma product_ftc (φ φ' : ℝ → ℝ) (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ' : Continuous φ') :
    ∫ θ in (-π)..π, (φ' θ * gE θ + φ θ * kE θ) = φ π * gE π - φ (-π) * gE (-π) := by
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr (fun x => (hφ x).continuousAt)
  have hle : -π ≤ 0 := by linarith [pi_pos]
  have hgc := EulerianCert.Turning.continuousOn_g
  have hpos : ∫ θ in (0 : ℝ)..π, (φ' θ * gE θ + φ θ * kE θ) = φ π * gE π - φ 0 * gE 0 := by
    have hsub : Icc 0 π ⊆ Icc (-π) π := Icc_subset_Icc (by linarith [pi_pos]) le_rfl
    apply integral_eq_sub_of_hasDerivAt_of_le pi_pos.le (hφc.continuousOn.mul (hgc.mono hsub))
    · intro x hx
      exact (hφ x).mul (EulerianCert.Turning.hasDerivAt_g (mem_of_pos hx) hx.1.ne')
    · refine IntervalIntegrable.add ?_ ?_
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le pi_pos.le]; exact hφ'.continuousOn.mul (hgc.mono hsub)
      · exact EulerianCert.Turning.intervalIntegrable_k_pos.continuousOn_mul hφc.continuousOn
  have hneg : ∫ θ in (-π)..0, (φ' θ * gE θ + φ θ * kE θ) = φ 0 * gE 0 - φ (-π) * gE (-π) := by
    have hsub : Icc (-π) 0 ⊆ Icc (-π) π := Icc_subset_Icc le_rfl pi_pos.le
    apply integral_eq_sub_of_hasDerivAt_of_le hle (hφc.continuousOn.mul (hgc.mono hsub))
    · intro x hx
      exact (hφ x).mul (EulerianCert.Turning.hasDerivAt_g (mem_of_neg hx) hx.2.ne)
    · refine IntervalIntegrable.add ?_ ?_
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hle]; exact hφ'.continuousOn.mul (hgc.mono hsub)
      · exact EulerianCert.Turning.intervalIntegrable_k_neg.continuousOn_mul hφc.continuousOn
  have hi : ∀ a b, a ∈ Icc (-π) π → b ∈ Icc (-π) π →
      IntervalIntegrable (fun θ => φ' θ * gE θ + φ θ * kE θ) volume a b := by
    intro a b ha hb
    refine IntervalIntegrable.add ?_ ?_
    · apply ContinuousOn.intervalIntegrable
      exact hφ'.continuousOn.mul (hgc.mono (uIcc_subset_Icc ha hb))
    · exact (intervalIntegrable_k.mono_set (uIcc_subset_uIcc (by
        rw [uIcc_of_le (by linarith [pi_pos])]; exact ha) (by
        rw [uIcc_of_le (by linarith [pi_pos])]; exact hb))).continuousOn_mul hφc.continuousOn
  have hm : (0 : ℝ) ∈ Icc (-π) π := ⟨hle, pi_pos.le⟩
  have hl : -π ∈ Icc (-π) π := ⟨le_rfl, by linarith [pi_pos]⟩
  have hr : π ∈ Icc (-π) π := ⟨by linarith [pi_pos], le_rfl⟩
  rw [← integral_add_adjacent_intervals (hi _ _ hl hm) (hi _ _ hm hr), hneg, hpos]
  ring

/-- **Eq. (37), signed part, distributional form**: for `C¹` `φ` with `φ(−π) = φ(π)`,
`⟨dθ − dβ_E, φ⟩ = ∫ φ k dθ − ϑ_E φ(π)`. -/
theorem turning_distribution (φ φ' : ℝ → ℝ) (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : Continuous φ') (hper : φ (-π) = φ π) :
    (∫ θ in (-π)..π, φ θ) + (∫ θ in (-π)..π, φ' θ * β θ) =
      (∫ θ in (-π)..π, φ θ * kE θ) - varthetaE * φ π := by
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr (fun x => (hφ x).continuousAt)
  have hgc := EulerianCert.Turning.continuousOn_g
  have h1 := product_ftc φ φ' hφ hφ'
  have hg_int : IntervalIntegrable (fun θ => φ' θ * gE θ) volume (-π) π := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith [pi_pos])]; exact hφ'.continuousOn.mul hgc
  have hk_int : IntervalIntegrable (fun θ => φ θ * kE θ) volume (-π) π :=
    intervalIntegrable_k.continuousOn_mul hφc.continuousOn
  rw [intervalIntegral.integral_add hg_int hk_int] at h1
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -π) (b := π)
    (u := fun θ => θ) (u' := fun _ => 1) (v := φ) (v' := φ')
    (fun x _ => hasDerivAt_id' x) (fun x _ => hφ x) intervalIntegrable_const
    (hφ'.intervalIntegrable _ _)
  simp only [one_mul] at h2
  have h3 : ∫ θ in (-π)..π, φ' θ * β θ =
      (∫ θ in (-π)..π, θ * φ' θ) - ∫ θ in (-π)..π, φ' θ * gE θ := by
    have hid : IntervalIntegrable (fun θ : ℝ => θ * φ' θ) volume (-π) π :=
      (continuous_id.mul hφ').intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub hid hg_int]
    congr 1; funext θ; rw [β_eq]; ring
  rw [h3, h2]
  rw [EulerianCert.Turning.g_pi, EulerianCert.Turning.g_neg_pi, hper] at h1
  rw [hper, varthetaE_eq]
  linarith

/-! ### The measures `τ_E` and `μ_TC = |τ_E|` -/

lemma measurable_k : Measurable kE := by
  unfold EulerianCert.Turning.k EulerianCert.Corner.rE EulerianCert.Corner.rE'
    EulerianCert.Corner.rE''
  fun_prop

/-- The smooth part `κ_E ds = k dθ` on `(−π, π]`. -/
def κds : Measure ℝ := (volume.restrict (Ioc (-π) π)).withDensity (fun θ => ENNReal.ofReal (kE θ))

instance : IsFiniteMeasure κds :=
  isFiniteMeasure_withDensity_ofReal intervalIntegrable_k.1.2

/-- `ϑ_E` as a non-negative real. -/
def ϑ : ℝ≥0 := ⟨varthetaE, varthetaE_nonneg⟩

/-- The corner atom `ϑ_E δ_{p_E}`. -/
def atom : Measure ℝ := ϑ • Measure.dirac π

instance : IsFiniteMeasure atom := by unfold atom; infer_instance

/-- **Eq. (37)**: the signed tangent-angle measure `τ_E = κ_E ds − ϑ_E δ_{p_E}`. -/
def τE : SignedMeasure ℝ := κds.toSignedMeasure - atom.toSignedMeasure

/-- **Eq. (37)**: the scalar total-curvature measure `μ_TC = κ_E ds + ϑ_E δ_{p_E}`. -/
def μTC : Measure ℝ := κds + atom

lemma κds_singleton : κds {π} = 0 := by
  unfold κds
  rw [withDensity_apply _ (measurableSet_singleton π)]
  have h0 : (volume.restrict (Ioc (-π) π)) {π} = 0 :=
    nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le _ _).trans (by simp))
  rw [Measure.restrict_eq_zero.mpr h0, lintegral_zero_measure]

lemma atom_compl : atom {π}ᶜ = 0 := by
  simp [atom]

/-- The Jordan decomposition `(κ_E ds, ϑ_E δ_{p_E})`. -/
def jE : JordanDecomposition ℝ where
  posPart := κds
  negPart := atom
  mutuallySingular := ⟨{π}, measurableSet_singleton π, κds_singleton, atom_compl⟩

/-- **Eq. (37)**: `μ_TC` is the total variation of `τ_E`. -/
theorem totalVariation_τE : τE.totalVariation = μTC := by
  have h : τE.toJordanDecomposition = jE := SignedMeasure.toJordanDecomposition_eq (by rfl)
  unfold SignedMeasure.totalVariation
  rw [h]
  rfl

/-- **Eq. (37)–(38)**, the scalar atoms: `τ_E{p_E} = −ϑ_E` and `μ_TC{p_E} = ϑ_E`. -/
theorem atoms_scalar : τE {π} = -varthetaE ∧ μTC {π} = ENNReal.ofReal varthetaE := by
  have ha : atom {π} = ENNReal.ofReal varthetaE := by
    simp only [atom, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_singleton π)]
    rw [ENNReal.ofReal_eq_coe_nnreal varthetaE_nonneg, ENNReal.smul_def, smul_eq_mul, mul_one]
    rfl
  constructor
  · unfold τE
    rw [VectorMeasure.sub_apply, Measure.toSignedMeasure_apply_measurable (measurableSet_singleton π),
      Measure.toSignedMeasure_apply_measurable (measurableSet_singleton π), measureReal_def,
      measureReal_def, κds_singleton, ha, ENNReal.toReal_ofReal varthetaE_nonneg]
    simp
  · unfold μTC
    rw [Measure.add_apply, κds_singleton, ha, zero_add]

/-- The smooth part integrates `φ` as `∫_{−π}^{π} φ k dθ`. -/
theorem integral_κds (φ : ℝ → ℝ) : ∫ θ, φ θ ∂κds = ∫ θ in (-π)..π, φ θ * kE θ := by
  unfold κds
  have hm : Measurable (fun θ => (kE θ).toNNReal) := measurable_k.real_toNNReal
  have e : (fun θ => ENNReal.ofReal (kE θ)) = fun θ => (((kE θ).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [e, integral_withDensity_eq_integral_smul hm, intervalIntegral.integral_of_le
    (by linarith [pi_pos])]
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  have h0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h0] with x hx hmem
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _
    (EulerianCert.Turning.k_nonneg (Ioc_subset_Icc_self hmem) hx)]
  ring

lemma integral_atom (φ : ℝ → ℝ) : ∫ θ, φ θ ∂atom = varthetaE * φ π := by
  unfold atom
  rw [integral_smul_nnreal_measure, integral_dirac]
  rfl

/-- **Eq. (37), signed part**: `τ_E` integrates every `C¹` periodic `φ` as the distributional
derivative `dθ − dβ_E` of the tangent angle. -/
theorem τE_integral (φ φ' : ℝ → ℝ) (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ' : Continuous φ')
    (hper : φ (-π) = φ π) :
    (∫ θ, φ θ ∂κds) - ∫ θ, φ θ ∂atom =
      (∫ θ in (-π)..π, φ θ) + ∫ θ in (-π)..π, φ' θ * β θ := by
  rw [integral_κds, integral_atom, turning_distribution φ φ' hφ hφ' hper]

/-! ### The unit tangent and Sullivan's vector measure -/

/-- The unit tangent `T_E = i e^{i g}`. -/
def TE (θ : ℝ) : ℂ := Complex.I * Complex.exp ((gE θ : ℂ) * Complex.I)

/-- The polar curve `γ_E(θ) = r_E(θ) e^{iθ}` and its velocity. -/
def γE (θ : ℝ) : ℂ := (ρ θ : ℂ) * Complex.exp (θ * Complex.I)

def γE' (θ : ℝ) : ℂ := ((rE' θ : ℂ) + ρ θ * Complex.I) * Complex.exp (θ * Complex.I)

lemma hasDerivAt_ρ {θ : ℝ} (h0 : θ ≠ 0) : HasDerivAt (fun t => ρ t) (rE' θ) θ := by
  have heq : (fun t => ρ t) =ᶠ[nhds θ] EulerianCert.Corner.rE := by
    filter_upwards [isOpen_ne.mem_nhds h0] with t ht
    exact (EulerianCert.Turning.R_eq_ρ ht).symm
  exact (EulerianCert.Corner.hasDerivAt_rE h0).congr_of_eventuallyEq heq

lemma hasDerivAt_γE {θ : ℝ} (h0 : θ ≠ 0) : HasDerivAt γE (γE' θ) θ := by
  have := (hasDerivAt_ρ h0).ofReal_comp.mul (EulerianCert.CurvatureGrowth.hasDerivAt_cexp θ)
  exact this.congr_deriv (by unfold γE'; ring)

/-- `T_E = γ_E'/|γ_E'|` on the closed parameter interval minus `θ = 0`. -/
theorem TE_unit_tangent {θ : ℝ} (hθ : θ ∈ Icc (-π) π) (h0 : θ ≠ 0) :
    TE θ = γE' θ / (‖γE' θ‖ : ℂ) := by
  have hρ := EulerianCert.Turning.ρ_pos hθ
  have hn : ‖γE' θ‖ = √(ρ θ ^ 2 + rE' θ ^ 2) := by
    unfold γE'
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_def, Complex.normSq_apply]
    congr 1; simp; ring
  rw [hn]
  unfold TE γE'
  rw [EulerianCert.CurvatureGrowth.unit_vec _ _ _ hρ]
  congr 3
  simp [EulerianCert.Turning.g, EulerianCert.Turning.rp, h0]

/-- The Frenet relation `T_E' = i k T_E` (`= κ_E N |γ_E'|`, `N = i T_E`). -/
theorem hasDerivAt_TE {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) (h0 : θ ≠ 0) :
    HasDerivAt TE (Complex.I * kE θ * TE θ) θ := by
  have := (((EulerianCert.Turning.hasDerivAt_g hθ h0).ofReal_comp.mul_const
    Complex.I).cexp).const_mul Complex.I
  unfold TE
  convert this using 1
  ring

lemma norm_TE (θ : ℝ) : ‖TE θ‖ = 1 := by
  rw [TE, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma continuousOn_TE : ContinuousOn TE (Icc (-π) π) := by
  unfold TE
  exact continuousOn_const.mul (Complex.continuous_exp.comp_continuousOn
    ((Complex.continuous_ofReal.comp_continuousOn EulerianCert.Turning.continuousOn_g).mul
      continuousOn_const))

/-- The one-sided unit tangents of Eq. (36): `T₋ = T_E(π)`, `T₊ = T_E(−π)`. -/
theorem TE_pi : TE π = (1 - π * Complex.I) / ((√(1 + π ^ 2) : ℝ) : ℂ) ∧
    TE (-π) = (-1 - π * Complex.I) / ((√(1 + π ^ 2) : ℝ) : ℂ) := by
  set a := Real.arctan (1 / π)
  have hπ := pi_pos
  set s := √(1 + π ^ 2)
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hsq : √(1 + (1 / π) ^ 2) = s / π := by
    rw [show (1 : ℝ) + (1 / π) ^ 2 = (1 + π ^ 2) / π ^ 2 by field_simp; ring]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hπ.le]
  have hcos : Real.cos a = π / s := by rw [Real.cos_arctan, hsq]; field_simp
  have hsin : Real.sin a = 1 / s := by rw [Real.sin_arctan, hsq]; field_simp
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hexpπ : Complex.exp ((π : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
  have hexpa : Complex.exp ((a : ℂ) * Complex.I) = (π / s : ℝ) + ((1 / s : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin]
  have hexpa' : Complex.exp ((-a : ℂ) * Complex.I) =
      (π / s : ℝ) - ((1 / s : ℝ) : ℂ) * Complex.I := by
    rw [show (-a : ℂ) = ((-a : ℝ) : ℂ) by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, hcos, hsin]
    push_cast; ring
  constructor
  · unfold TE
    rw [EulerianCert.Turning.g_pi]
    push_cast
    rw [add_mul, Complex.exp_add, hexpπ, hexpa]
    push_cast
    field_simp
    linear_combination (-1 : ℂ) * Complex.I_sq
  · unfold TE
    rw [EulerianCert.Turning.g_neg_pi]
    push_cast
    rw [show (-(π : ℂ) - (a : ℂ)) * Complex.I = -((π : ℂ) * Complex.I) + (-a : ℂ) * Complex.I by
      ring, Complex.exp_add, Complex.exp_neg, hexpπ, hexpa']
    push_cast
    field_simp
    linear_combination Complex.I_sq

/-- **Eq. (38)**: the tangent jump `T₊ − T₋ = −2/√(1+π²)` and `|T₊ − T₋| = 2 sin(ϑ_E/2)`. -/
theorem tangent_jump :
    TE (-π) - TE π = ((-2 / √(1 + π ^ 2) : ℝ) : ℂ) ∧
      ‖TE (-π) - TE π‖ = 2 * Real.sin (varthetaE / 2) := by
  obtain ⟨h1, h2⟩ := TE_pi
  have hs : 0 < √(1 + π ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hj : TE (-π) - TE π = ((-2 / √(1 + π ^ 2) : ℝ) : ℂ) := by
    rw [h1, h2]; push_cast; ring
  refine ⟨hj, ?_⟩
  rw [hj, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_two, abs_of_pos hs]
  exact (EulerianCert.Corner.sullivan_atom).2

/-- **Eq. (37), vector part, distributional form**: `dK_E = dT_E` on the parameter circle:
for `C¹` `φ` with `φ(−π) = φ(π)`, `−∫ φ' T_E = ∫ φ (i k T_E) + φ(π)(T₊ − T₋)`. -/
theorem vector_distribution (φ φ' : ℝ → ℝ) (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : Continuous φ') (hper : φ (-π) = φ π) :
    -(∫ θ in (-π)..π, (φ' θ : ℂ) * TE θ) =
      (∫ θ in (-π)..π, (φ θ : ℂ) * (Complex.I * kE θ * TE θ)) + (φ π : ℂ) * (TE (-π) - TE π) := by
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr (fun x => (hφ x).continuousAt)
  have hle : -π ≤ 0 := by linarith [pi_pos]
  set F' : ℝ → ℂ := fun θ => (φ' θ : ℂ) * TE θ + (φ θ : ℂ) * (Complex.I * kE θ * TE θ)
  have hint1 : ∀ a b, a ∈ Icc (-π) π → b ∈ Icc (-π) π →
      IntervalIntegrable (fun θ => (φ' θ : ℂ) * TE θ) volume a b := fun a b ha hb =>
    ContinuousOn.intervalIntegrable ((Complex.continuous_ofReal.comp hφ').continuousOn.mul
      (continuousOn_TE.mono (uIcc_subset_Icc ha hb)))
  have hint2 : ∀ a b, a ∈ Icc (-π) π → b ∈ Icc (-π) π →
      IntervalIntegrable (fun θ => (φ θ : ℂ) * (Complex.I * kE θ * TE θ)) volume a b := by
    intro a b ha hb
    have hk : IntervalIntegrable kE volume a b :=
      intervalIntegrable_k.mono_set (uIcc_subset_uIcc (by
        rw [uIcc_of_le (by linarith [pi_pos])]; exact ha) (by
        rw [uIcc_of_le (by linarith [pi_pos])]; exact hb))
    have := hk.smul_continuousOn (g := fun θ => (φ θ : ℂ) * Complex.I * TE θ)
      (((Complex.continuous_ofReal.comp hφc).continuousOn.mul continuousOn_const).mul
        (continuousOn_TE.mono (uIcc_subset_Icc ha hb)))
    refine this.congr (fun θ _ => ?_)
    simp only [Complex.real_smul]; ring
  have hm : (0 : ℝ) ∈ Icc (-π) π := ⟨hle, pi_pos.le⟩
  have hl : -π ∈ Icc (-π) π := ⟨le_rfl, by linarith [pi_pos]⟩
  have hr : π ∈ Icc (-π) π := ⟨by linarith [pi_pos], le_rfl⟩
  have hTc := continuousOn_TE
  have hpos : ∫ θ in (0 : ℝ)..π, F' θ = (φ π : ℂ) * TE π - (φ 0 : ℂ) * TE 0 := by
    have hsub : Icc 0 π ⊆ Icc (-π) π := Icc_subset_Icc (by linarith [pi_pos]) le_rfl
    apply integral_eq_sub_of_hasDerivAt_of_le pi_pos.le
      ((Complex.continuous_ofReal.comp hφc).continuousOn.mul (hTc.mono hsub))
    · intro x hx
      exact (hφ x).ofReal_comp.mul (hasDerivAt_TE (mem_of_pos hx) hx.1.ne')
    · exact (hint1 _ _ hm hr).add (hint2 _ _ hm hr)
  have hneg : ∫ θ in (-π)..0, F' θ = (φ 0 : ℂ) * TE 0 - (φ (-π) : ℂ) * TE (-π) := by
    have hsub : Icc (-π) 0 ⊆ Icc (-π) π := Icc_subset_Icc le_rfl pi_pos.le
    apply integral_eq_sub_of_hasDerivAt_of_le hle
      ((Complex.continuous_ofReal.comp hφc).continuousOn.mul (hTc.mono hsub))
    · intro x hx
      exact (hφ x).ofReal_comp.mul (hasDerivAt_TE (mem_of_neg hx) hx.2.ne)
    · exact (hint1 _ _ hl hm).add (hint2 _ _ hl hm)
  have hall : ∫ θ in (-π)..π, F' θ = (φ π : ℂ) * TE π - (φ (-π) : ℂ) * TE (-π) := by
    rw [← integral_add_adjacent_intervals ((hint1 _ _ hl hm).add (hint2 _ _ hl hm))
      ((hint1 _ _ hm hr).add (hint2 _ _ hm hr)), hneg, hpos]
    ring
  rw [intervalIntegral.integral_add (hint1 _ _ hl hr) (hint2 _ _ hl hr), hper] at hall
  linear_combination -hall

lemma measurable_TE : Measurable TE := by
  have hrp : Measurable EulerianCert.Turning.rp := by
    unfold EulerianCert.Turning.rp
    exact Measurable.ite (measurableSet_singleton 0) measurable_const
      (by unfold EulerianCert.Corner.rE'; fun_prop)
  have hg : Measurable gE := by
    unfold EulerianCert.Turning.g
    exact measurable_id.sub (Real.continuous_arctan.measurable.comp
      (hrp.div EulerianCert.FourierModes.continuous_rE.measurable))
  unfold TE
  fun_prop

lemma integrable_smooth :
    Integrable (fun θ => Complex.I * kE θ * TE θ) (volume.restrict (Ioc (-π) π)) := by
  refine Integrable.mono' intervalIntegrable_k.1.norm ?_ (Filter.Eventually.of_forall (fun θ => ?_))
  · have := measurable_k; have := measurable_TE
    exact (by fun_prop : Measurable (fun θ => Complex.I * (kE θ : ℂ) * TE θ)).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Complex.norm_I, one_mul, norm_TE, mul_one, Complex.norm_real]

/-- **Eq. (37)**: Sullivan's vector curvature measure
`K_E = κ_E N ds + (T₊ − T₋) δ_{p_E}` (`κ_E N ds = i k T_E dθ`), a `ℂ`-valued vector measure. -/
def KE : VectorMeasure ℝ ℂ :=
  (volume.restrict (Ioc (-π) π)).withDensityᵥ (fun θ => Complex.I * kE θ * TE θ) +
    (Measure.dirac π).withDensityᵥ (fun _ => TE (-π) - TE π)

/-- **Eq. (38)**: `K_E{p_E} = (−2/√(1+π²), 0)` and `‖K_E{p_E}‖ = 2 sin(ϑ_E/2)`. -/
theorem KE_atom : KE {π} = ((-2 / √(1 + π ^ 2) : ℝ) : ℂ) ∧
    ‖KE {π}‖ = 2 * Real.sin (varthetaE / 2) := by
  have hval : KE {π} = TE (-π) - TE π := by
    unfold KE
    rw [VectorMeasure.add_apply, withDensityᵥ_apply integrable_smooth (measurableSet_singleton π),
      withDensityᵥ_apply (integrable_const _) (measurableSet_singleton π)]
    have h0 : (volume.restrict (Ioc (-π) π)) {π} = 0 :=
      nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le _ _).trans (by simp))
    rw [setIntegral_measure_zero _ h0, setIntegral_const]
    simp
  rw [hval]
  exact tangent_jump

end EulerianCert.CurvatureMeasures
