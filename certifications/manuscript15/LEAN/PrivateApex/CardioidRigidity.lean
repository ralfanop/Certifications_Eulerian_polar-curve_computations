import PrivateApex.CardioidProbability
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
PRIVATE.  Manuscript 15: Eulerian Fourier reconstruction of the Mandelbrot cardioid.
Rigidity of the centred uniform law.

For a Borel probability measure `μ` on `ℝ` put `Reconstructs μ θ` for the identity
`c(θ) - 1/4 = (θ^2 / 4) (charFun μ θ)^2 e^{iθ}`.

* `uniform_reconstructs`: the uniform law on `[-1/2, 1/2]` satisfies it for every real `θ`;
* `rigidity_local`: if `μ` is supported in a bounded interval and the identity holds for
  `|θ| < δ`, for some `δ > 0`, then `μ` is the uniform law on `[-1/2, 1/2]`;
* `rigidity_global`: if the identity holds for every real `θ`, no support hypothesis is needed;
* `rigidity_iff`: the resulting characterisation.

The proof of `rigidity_local` follows the classical route: compact support makes the
characteristic function the restriction of an entire function (`analytic_cf`, from Mathlib's
`analyticOnNhd_complexMGF`); the hypothesis gives `(f - g)(f + g) = 0` on a real interval, hence
everywhere by the identity theorem; the ring of entire functions has no zero divisors, and
`f(0) + g(0) = 2` excludes the second factor; uniqueness of characteristic functions
(`Measure.ext_of_charFun`) concludes.  In `rigidity_global` the support is recovered from
`μ ∗ μ = unifLaw ∗ unifLaw` (`conv_tail_right`, `conv_tail_left`).
-/

namespace PrivateApex
namespace Cardioid
open Complex MeasureTheory ProbabilityTheory Filter
open scoped Real Topology

/-- The reconstruction identity for the law `μ` at the parameter `θ`. -/
def Reconstructs (μ : Measure ℝ) (θ : ℝ) : Prop :=
  cardioid θ - 1 / 4 = (θ : ℂ) ^ 2 / 4 * charFun μ θ ^ 2 * exp ((θ : ℂ) * I)

/-- The centred uniform law reconstructs the cardioid. -/
theorem uniform_reconstructs (θ : ℝ) : Reconstructs unifLaw θ := by
  rw [Reconstructs, charFun_unifLaw, cardioid_eulerian]

/-- For `θ ≠ 0` the reconstruction identity is `(charFun μ θ)^2 = r_E(θ)^2`. -/
theorem reconstructs_iff {μ : Measure ℝ} {θ : ℝ} (hθ : θ ≠ 0) :
    Reconstructs μ θ ↔ charFun μ θ ^ 2 = (rE θ : ℂ) ^ 2 := by
  have h1 : (θ : ℂ) ^ 2 / 4 ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 (by exact_mod_cast hθ)) (by norm_num)
  rw [Reconstructs, cardioid_eulerian]
  constructor
  · intro h
    exact (mul_left_cancel₀ h1 (mul_right_cancel₀ (Complex.exp_ne_zero _) h)).symm
  · intro h; rw [h]

theorem unifLaw_supp : unifLaw (Set.Icc (-(1 / 2) : ℝ) (1 / 2))ᶜ = 0 := by
  rw [unifLaw, Measure.restrict_apply measurableSet_Icc.compl]; simp

/-- A measure carried by a bounded interval has finite exponential moments of every order. -/
theorem integrableExpSet_of_bdd (μ : Measure ℝ) [IsFiniteMeasure μ] (R : ℝ)
    (hsupp : μ (Set.Icc (-R) R)ᶜ = 0) : integrableExpSet id μ = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  show Integrable (fun x : ℝ => Real.exp (t * id x)) μ
  have hae : ∀ᵐ x ∂μ, x ∈ Set.Icc (-R) R := by
    rw [ae_iff]; exact hsupp
  refine Integrable.mono' (integrable_const (Real.exp (|t| * R)))
    (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [hae] with x hx
  rw [Real.norm_eq_abs, Real.abs_exp]
  apply Real.exp_le_exp.mpr
  calc t * id x ≤ |t * x| := le_abs_self _
    _ = |t| * |x| := abs_mul t x
    _ ≤ |t| * R := mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hx.1, hx.2⟩) (abs_nonneg t)

/-- The characteristic function of a measure carried by a bounded interval is the restriction to
the real axis of an entire function. -/
theorem analytic_cf (μ : Measure ℝ) [IsFiniteMeasure μ] (R : ℝ)
    (hsupp : μ (Set.Icc (-R) R)ᶜ = 0) :
    AnalyticOnNhd ℂ (fun w : ℂ => complexMGF id μ (w * I)) Set.univ := by
  have h := analyticOnNhd_complexMGF (X := id) (μ := μ)
  rw [integrableExpSet_of_bdd μ R hsupp] at h
  intro w _
  have hw : AnalyticAt ℂ (complexMGF id μ) (w * I) := h (w * I) (by simp)
  have hlin : AnalyticAt ℂ (fun z : ℂ => z * I) w := by fun_prop
  exact AnalyticAt.comp (g := complexMGF id μ) (f := fun z : ℂ => z * I) hw hlin

/-- Rigidity, local form: among the probability laws carried by a bounded interval, the
reconstruction identity on a neighbourhood of `θ = 0` characterises the uniform law on
`[-1/2, 1/2]`. -/
theorem rigidity_local (μ : Measure ℝ) [IsProbabilityMeasure μ] (R : ℝ)
    (hsupp : μ (Set.Icc (-R) R)ᶜ = 0) (δ : ℝ) (hδ : 0 < δ)
    (h : ∀ θ : ℝ, |θ| < δ → Reconstructs μ θ) : μ = unifLaw := by
  let f : ℂ → ℂ := fun w => complexMGF id μ (w * I)
  let g : ℂ → ℂ := fun w => complexMGF id unifLaw (w * I)
  have hf : AnalyticOnNhd ℂ f Set.univ := analytic_cf μ R hsupp
  have hg : AnalyticOnNhd ℂ g Set.univ := analytic_cf unifLaw (1 / 2) unifLaw_supp
  have hfr : ∀ θ : ℝ, f θ = charFun μ θ := fun θ => complexMGF_id_mul_I θ
  have hgr : ∀ θ : ℝ, g θ = (rE θ : ℂ) := fun θ => by
    rw [← charFun_unifLaw]; exact complexMGF_id_mul_I θ
  -- the product `(f - g)(f + g)` vanishes on the real interval `(0, δ)`
  have hsq : ∀ θ : ℝ, 0 < θ → θ < δ → ((f - g) * (f + g)) (θ : ℂ) = 0 := by
    intro θ h0 h1
    have h' := (reconstructs_iff h0.ne').mp (h θ (by rw [abs_of_pos h0]; exact h1))
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, hfr, hgr]
    linear_combination h'
  -- these zeros accumulate at the origin
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), ((f - g) * (f + g)) z = 0 := by
    have hx : Tendsto (fun n : ℕ => ((δ / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have h0 : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop
            (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
        have h1 := (Complex.continuous_ofReal.tendsto 0).comp h0
        rw [Complex.ofReal_zero] at h1
        exact h1
      · refine Eventually.of_forall fun n => ?_
        have hpos : (0 : ℝ) < δ / ((n : ℝ) + 2) := by positivity
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact_mod_cast hpos.ne'
    refine hx.frequently (Frequently.of_forall fun n => ?_)
    have hpos : (0 : ℝ) < δ / ((n : ℝ) + 2) := by positivity
    have hlt : δ / ((n : ℝ) + 2) < δ := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    exact hsq _ hpos hlt
  -- identity theorem
  have hzero : Set.EqOn ((f - g) * (f + g)) 0 Set.univ :=
    ((hf.sub hg).mul (hf.add hg)).eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ 0) hfreq
  have hprod : ∀ z ∈ (Set.univ : Set ℂ), (f - g) z * (f + g) z = 0 := fun z hz => hzero hz
  rcases (hf.sub hg).eq_zero_or_eq_zero_of_mul_eq_zero (hf.add hg) hprod isPreconnected_univ
    with h1 | h2
  · -- `f = g`: the characteristic functions coincide
    apply Measure.ext_of_charFun
    ext θ
    have h3 := h1 (θ : ℂ) (Set.mem_univ _)
    rw [Pi.sub_apply, hfr, hgr, sub_eq_zero] at h3
    rw [h3, charFun_unifLaw]
  · -- `f + g = 0` is excluded by the normalisation at the origin
    exfalso
    have h3 := h2 ((0 : ℝ) : ℂ) (Set.mem_univ _)
    rw [Pi.add_apply, hfr, hgr] at h3
    simp [rE_zero] at h3

/-! ### The global form: the support is automatic -/

theorem conv_tail_right (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] (a b : ℝ) :
    μ (Set.Ici a) * ν (Set.Ici b) ≤ (μ ∗ ν) (Set.Ici (a + b)) := by
  rw [Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Ici, ← Measure.prod_prod]
  apply measure_mono
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  simp only [Set.mem_preimage, Set.mem_Ici] at *
  exact add_le_add hx hy

theorem conv_tail_left (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] (a b : ℝ) :
    μ (Set.Iic a) * ν (Set.Iic b) ≤ (μ ∗ ν) (Set.Iic (a + b)) := by
  rw [Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Iic, ← Measure.prod_prod]
  apply measure_mono
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  simp only [Set.mem_preimage, Set.mem_Iic] at *
  exact add_le_add hx hy

private theorem prod_unif_compl :
    (unifLaw.prod unifLaw)
      (Set.Icc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Set.Icc (-(1 / 2) : ℝ) (1 / 2))ᶜ = 0 := by
  rw [unifLaw, Measure.prod_restrict,
    Measure.restrict_apply (measurableSet_Icc.prod measurableSet_Icc).compl]
  simp

theorem conv_unif_tail_right {a : ℝ} (ha : 1 < a) : (unifLaw ∗ unifLaw) (Set.Ici a) = 0 := by
  rw [Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Ici]
  refine measure_mono_null ?_ prod_unif_compl
  rintro ⟨x, y⟩ hxy ⟨hx, hy⟩
  simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Icc] at *
  linarith

theorem conv_unif_tail_left {a : ℝ} (ha : a < -1) : (unifLaw ∗ unifLaw) (Set.Iic a) = 0 := by
  rw [Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Iic]
  refine measure_mono_null ?_ prod_unif_compl
  rintro ⟨x, y⟩ hxy ⟨hx, hy⟩
  simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Icc] at *
  linarith

/-- Rigidity, global form: a Borel probability measure on `ℝ` whose characteristic function
reconstructs the cardioid for every real `θ` is the uniform law on `[-1/2, 1/2]`.  No support or
symmetry hypothesis is made. -/
theorem rigidity_global (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ∀ θ : ℝ, Reconstructs μ θ) : μ = unifLaw := by
  have hconv : μ ∗ μ = unifLaw ∗ unifLaw := by
    apply Measure.ext_of_charFun
    ext θ
    rw [charFun_conv, charFun_conv, charFun_unifLaw]
    by_cases h0 : θ = 0
    · subst h0; simp [rE_zero]
    · have h' := (reconstructs_iff h0).mp (h θ)
      linear_combination h'
  have hR : μ (Set.Ici 1) = 0 := by
    have h1 := conv_tail_right μ μ 1 1
    rw [hconv, conv_unif_tail_right (by norm_num)] at h1
    exact mul_self_eq_zero.mp (le_antisymm h1 zero_le)
  have hL : μ (Set.Iic (-1)) = 0 := by
    have h1 := conv_tail_left μ μ (-1) (-1)
    rw [hconv, conv_unif_tail_left (by norm_num)] at h1
    exact mul_self_eq_zero.mp (le_antisymm h1 zero_le)
  have hsupp : μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
    refine measure_mono_null ?_ (measure_union_null hL hR)
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact Or.inl hx.le
    · exact Or.inr hx.le
  exact rigidity_local μ 1 hsupp 1 one_pos (fun θ _ => h θ)

/-- Characterisation of the centred uniform law by the reconstruction of the cardioid. -/
theorem rigidity_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∀ θ : ℝ, Reconstructs μ θ) ↔ μ = unifLaw :=
  ⟨rigidity_global μ, fun h => h ▸ uniform_reconstructs⟩

end Cardioid
end PrivateApex
