import Mathlib

/-! Actual L² cutoffs for M14 §7.4 (114), consolidated source 2026-11-17.
TeX SHA256 5eaa4b4c760b8bf347385ecde00033f9a38ba13ed8b60a9b648eaabb69fee662.
The full-space cutoff is a continuous linear contraction and its difference
from the identity has the exact exterior integral norm. This supplies an
actual L² identity for the separate compact-cutoff bridge. -/
open MeasureTheory Filter
open scoped InnerProductSpace
noncomputable section
namespace Manuscript14.L2Cutoff

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Actual square norm as a Bochner integral. -/
theorem norm_sq_integral (u : Lp ℂ 2 μ) :
    ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  have h : (↑(‖u‖^2) : ℂ) = ∫ x, (↑(‖u x‖^2) : ℂ) ∂μ := by
    simpa only [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow] using L2.inner_def (𝕜 := ℂ) u u
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

theorem integrable_sq_norm (u : Lp ℂ 2 μ) :
    Integrable (fun x => ‖u x‖^2) μ :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)

/-- Zero extension of the restriction to a measurable spatial region. -/
def cutoff (s : Set X) (hs : MeasurableSet s) (u : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (MemLp.indicator hs.nullMeasurableSet (Lp.memLp u)).toLp (s.indicator u)

theorem cutoff_ae (s : Set X) (hs : MeasurableSet s) (u : Lp ℂ 2 μ) :
    ⇑(cutoff s hs u) =ᵐ[μ] s.indicator u :=
  MemLp.coeFn_toLp (MemLp.indicator hs.nullMeasurableSet (Lp.memLp u))

theorem cutoff_norm_sq (s : Set X) (hs : MeasurableSet s) (u : Lp ℂ 2 μ) :
    ‖cutoff s hs u‖^2 = ∫ x in s, ‖u x‖^2 ∂μ := by
  rw [norm_sq_integral, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [cutoff_ae s hs u] with x hx
  rw [hx]
  by_cases h : x ∈ s
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- Exact exterior norm identity, with no approximation or abstract axiom. -/
theorem cutoff_sub_norm_sq (s : Set X) (hs : MeasurableSet s) (u : Lp ℂ 2 μ) :
    ‖cutoff s hs u - u‖^2 = ∫ x in sᶜ, ‖u x‖^2 ∂μ := by
  rw [norm_sq_integral, ← integral_indicator hs.compl]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (cutoff s hs u) u, cutoff_ae s hs u] with x hx hy
  rw [hx]
  change ‖cutoff s hs u x - u x‖^2 =
    sᶜ.indicator (fun y => ‖u y‖^2) x
  rw [hy]
  by_cases h : x ∈ s
  · simp [Set.indicator_of_mem h, Set.indicator_of_notMem (show x ∉ sᶜ by simpa using h)]
  · simp [Set.indicator_of_notMem h, Set.indicator_of_mem (show x ∈ sᶜ from h)]

theorem cutoff_norm_le (s : Set X) (hs : MeasurableSet s) (u : Lp ℂ 2 μ) :
    ‖cutoff s hs u‖ ≤ ‖u‖ := by
  have hsq : ‖cutoff s hs u‖^2 ≤ ‖u‖^2 := by
    rw [cutoff_norm_sq, norm_sq_integral u]
    exact setIntegral_le_integral (integrable_sq_norm u)
      (Eventually.of_forall fun x => sq_nonneg _)
  by_contra! h
  have hp := mul_pos (sub_pos.mpr h)
    (show 0 < ‖cutoff s hs u‖ + ‖u‖ by linarith [norm_nonneg u])
  nlinarith

def cutoffLinear (s : Set X) (hs : MeasurableSet s) :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := cutoff s hs
  map_add' u v := by
    apply Lp.ext
    filter_upwards [cutoff_ae s hs (u+v), Lp.coeFn_add u v,
      cutoff_ae s hs u, cutoff_ae s hs v, Lp.coeFn_add (cutoff s hs u) (cutoff s hs v)]
      with x h1 h2 h3 h4 h5
    change cutoff s hs (u+v) x = (cutoff s hs u + cutoff s hs v) x
    rw [h1,h5]
    by_cases h : x ∈ s
    · simp only [Pi.add_apply, h3, h4, Set.indicator_of_mem h, h2]
    · simp only [Pi.add_apply, h3, h4, Set.indicator_of_notMem h, add_zero]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [cutoff_ae s hs (c • u), Lp.coeFn_smul c u,
      cutoff_ae s hs u, Lp.coeFn_smul c (cutoff s hs u)] with x h1 h2 h3 h4
    change cutoff s hs (c • u) x = (c • cutoff s hs u) x
    rw [h1,h4]
    by_cases h : x ∈ s
    · simp only [Pi.smul_apply, h3, Set.indicator_of_mem h, h2]
    · simp only [Pi.smul_apply, h3, Set.indicator_of_notMem h, smul_zero]

/-- The actual bounded continuous linear cutoff P_s. -/
def cutoffCLM (s : Set X) (hs : MeasurableSet s) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (cutoffLinear s hs).mkContinuous 1 (fun u => by
    change ‖cutoff s hs u‖ ≤ 1 * ‖u‖
    simpa only [one_mul] using cutoff_norm_le s hs u)

theorem cutoffCLM_apply (s : Set X) (hs : MeasurableSet s) (u : Lp ℂ 2 μ) :
    cutoffCLM s hs u = cutoff s hs u := rfl

theorem cutoffCLM_norm_le (s : Set X) (hs : MeasurableSet s) :
    ‖(cutoffCLM s hs : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [cutoffCLM_apply, one_mul]
  exact cutoff_norm_le s hs u

theorem cutoffCLM_exterior (s : Set X) (hs : MeasurableSet s) (u : Lp ℂ 2 μ) :
    ‖cutoffCLM s hs u - u‖^2 = ∫ x in sᶜ, ‖u x‖^2 ∂μ := by
  rw [cutoffCLM_apply, cutoff_sub_norm_sq]

#print axioms norm_sq_integral
#print axioms integrable_sq_norm
#print axioms cutoff_ae
#print axioms cutoff_norm_sq
#print axioms cutoff_sub_norm_sq
#print axioms cutoff_norm_le
#print axioms cutoffCLM_apply
#print axioms cutoffCLM_norm_le
#print axioms cutoffCLM_exterior

end Manuscript14.L2Cutoff
