import Mathlib

/-! Manuscript 14, consolidated 2026-11-17, §7.4, confinement (114).
Source ZIP SHA256 0614abafe7e9e9a82098278741559bd082028e9d97787f8e0aa4db17e064971d.
TeX SHA256 5eaa4b4c760b8bf347385ecde00033f9a38ba13ed8b60a9b648eaabb69fee662.
Actual Bochner integrals and compact continuous linear maps. The magnetic
energy estimate, identification of cutoffs in L² and local Rellich
compactness must still be established for the concrete magnetic operator. -/

open MeasureTheory Filter Topology
noncomputable section
namespace Manuscript14.ConfinementCutoff

/-- The confining weight controls the actual integral over the exterior. -/
theorem weighted_tail {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f w : X → ℝ) (s : Set X) (hs : MeasurableSet s)
    (R : ℝ) (hR : 0 < R)
    (hf : Integrable f μ) (hwf : Integrable (fun x => w x * f x) μ)
    (hf0 : ∀ x, 0 ≤ f x) (hw0 : ∀ x, 0 ≤ w x)
    (hout : ∀ x ∈ s, R^2 ≤ w x) :
    (∫ x in s, f x ∂μ) ≤ (∫ x, w x * f x ∂μ) / R^2 := by
  have hscaled : Integrable (fun x => R^2 * f x) μ := hf.const_mul _
  apply (le_div_iff₀ (sq_pos_of_pos hR)).2
  calc
    (∫ x in s, f x ∂μ) * R^2 = ∫ x in s, R^2 * f x ∂μ := by
      rw [integral_const_mul, mul_comm]
    _ ≤ ∫ x in s, w x * f x ∂μ :=
      setIntegral_mono_on hscaled.integrableOn hwf.integrableOn hs
        (fun x hx => mul_le_mul_of_nonneg_right (hout x hx) (hf0 x))
    _ ≤ ∫ x, w x * f x ∂μ :=
      setIntegral_le_integral hwf (Eventually.of_forall fun x => mul_nonneg (hw0 x) (hf0 x))

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Convert a squared tail estimate to the ordinary operator-norm estimate. -/
theorem norm_from_square (J K : V →L[ℂ] H) (r : ℝ) (hr : 0 ≤ r)
    (ht : ∀ u : V, ‖K u - J u‖^2 ≤ (r * ‖u‖)^2) :
    ‖K - J‖ ≤ r := by
  apply ContinuousLinearMap.opNorm_le_bound _ hr
  intro u
  change ‖K u - J u‖ ≤ r * ‖u‖
  by_contra! h
  have hpos : 0 < ‖K u - J u‖ + r * ‖u‖ := by
    have hn := mul_nonneg hr (norm_nonneg u)
    linarith
  have hp := mul_pos (sub_pos.mpr h) hpos
  nlinarith [ht u]

/-- Local compactness plus a uniform vanishing exterior gives compactness
    of the global inclusion in operator norm. -/
theorem compact_of_cutoffs (J : V →L[ℂ] H) (K : ℕ → V →L[ℂ] H)
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hK : ∀ n, IsCompactOperator (K n))
    (htail : ∀ n u, ‖K n u - J u‖^2 ≤ (r n * ‖u‖)^2) :
    IsCompactOperator J := by
  have hb : ∀ n, ‖K n - J‖ ≤ r n :=
    fun n => norm_from_square J (K n) (r n) (hr n) (htail n)
  have ht : Tendsto (fun n => ‖K n - J‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) hb hrlim
  have hk : Tendsto K atTop (𝓝 J) :=
    tendsto_iff_dist_tendsto_zero.2 (by simpa only [dist_eq_norm] using ht)
  exact isCompactOperator_of_tendsto hk (Eventually.of_forall hK)

/-- Connect the Bochner weighted-tail estimate to the actual form-space norm.
    The given equality is the cutoff L² norm identity. -/
theorem weighted_cutoff_norm_sq {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (J K : V →L[ℂ] H) (f : V → X → ℝ) (w : X → ℝ)
    (s : Set X) (hs : MeasurableSet s) (R A : ℝ)
    (hR : 0 < R) (hA : 0 ≤ A)
    (hf : ∀ u, Integrable (f u) μ)
    (hwf : ∀ u, Integrable (fun x => w x * f u x) μ)
    (hf0 : ∀ u x, 0 ≤ f u x) (hw0 : ∀ x, 0 ≤ w x)
    (hout : ∀ x ∈ s, R^2 ≤ w x)
    (henergy : ∀ u, (∫ x, w x * f u x ∂μ) ≤ A * ‖u‖^2)
    (hid : ∀ u, ‖K u - J u‖^2 = ∫ x in s, f u x ∂μ) (u : V) :
    ‖K u - J u‖^2 ≤ (Real.sqrt A / R * ‖u‖)^2 := by
  rw [hid u]
  calc
    _ ≤ (∫ x, w x * f u x ∂μ) / R^2 :=
      weighted_tail μ (f u) w s hs R hR (hf u) (hwf u) (hf0 u) hw0 hout
    _ ≤ (A * ‖u‖^2) / R^2 :=
      div_le_div_of_nonneg_right (henergy u) (sq_nonneg R)
    _ = (Real.sqrt A / R * ‖u‖)^2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt hA]
      ring

/-- Full abstract cutoff-to-Friedrichs-resolvent bridge, on actual Hilbert spaces.
    Local compactness of the cutoffs is the only compactness assumption. -/
theorem weighted_resolvent_compact {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (J : V →L[ℂ] H) (K : ℕ → V →L[ℂ] H)
    (f : V → X → ℝ) (w : X → ℝ) (s : ℕ → Set X) (R : ℕ → ℝ) (A : ℝ)
    (hs : ∀ n, MeasurableSet (s n)) (hR : ∀ n, 0 < R n) (hA : 0 ≤ A)
    (hrlim : Tendsto (fun n => Real.sqrt A / R n) atTop (𝓝 0))
    (hf : ∀ u, Integrable (f u) μ)
    (hwf : ∀ u, Integrable (fun x => w x * f u x) μ)
    (hf0 : ∀ u x, 0 ≤ f u x) (hw0 : ∀ x, 0 ≤ w x)
    (hout : ∀ n x, x ∈ s n → (R n)^2 ≤ w x)
    (henergy : ∀ u, (∫ x, w x * f u x ∂μ) ≤ A * ‖u‖^2)
    (hid : ∀ n u, ‖K n u - J u‖^2 = ∫ x in s n, f u x ∂μ)
    (hK : ∀ n, IsCompactOperator (K n)) :
    IsCompactOperator (J.comp J.adjoint) := by
  have hJ : IsCompactOperator J :=
    compact_of_cutoffs J K (fun n => Real.sqrt A / R n)
      (fun n => div_nonneg (Real.sqrt_nonneg A) (hR n).le) hrlim hK
      (fun n u => weighted_cutoff_norm_sq μ J (K n) f w (s n) (hs n)
        (R n) A (hR n) hA hf hwf hf0 hw0 (hout n) henergy (hid n) u)
  exact hJ.comp_clm J.adjoint

#print axioms weighted_tail
#print axioms norm_from_square
#print axioms compact_of_cutoffs
#print axioms weighted_cutoff_norm_sq
#print axioms weighted_resolvent_compact

end Manuscript14.ConfinementCutoff
