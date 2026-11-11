import Mathlib

/-!
# Priority 3 — uniform-in-index complex spectral equicontinuity
# from the asymmetric spectral exponential perturbation estimate

For arbitrary F_n: ℂ→ℂ, a common bound
  |F_n(z)-F_n(w)| ≤ |z-w| r exp((|w|+|z-w|)r)
with r≥0 yields equicontinuity of the entire indexed family
for ALL complex spectral points. No global uniform continuity
is asserted; the modulus may depend on the base point z.
This is the exact topological step from the compression parameter
estimate to compact Ascoli and entire Fredholm holomorphy.
-/

noncomputable section

namespace Manuscript14Priority3.SpectralExpEquicontinuity

open Filter Topology

/-- The dimension-free asymmetric exponential bound is enough for
genuine equicontinuity of arbitrary ℕ-indexed entire functions.
We do not assume entire holomorphy in this theorem. -/
theorem equicontinuity_of_asymmetric_exponential_norm_bound
    (D : ℕ → ℂ → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ (n : ℕ) (z w : ℂ),
      ‖D n z - D n w‖ ≤
        (‖z-w‖ * r) * Real.exp ((‖w‖ + ‖z-w‖) * r)) :
    Equicontinuous D := by
  intro z
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  let φ : ℂ → ℝ := fun w =>
    (‖z-w‖ * r) * Real.exp ((‖w‖ + ‖z-w‖) * r)
  have hdist : Continuous (fun w : ℂ => ‖z-w‖) :=
    continuous_norm.comp (continuous_const.sub continuous_id)
  have hsum : Continuous (fun w : ℂ => ‖w‖ + ‖z-w‖) :=
    continuous_norm.add hdist
  have hExp : Continuous (fun w : ℂ =>
      Real.exp ((‖w‖ + ‖z-w‖) * r)) :=
    Real.continuous_exp.comp (hsum.mul continuous_const)
  have hφ : Continuous φ :=
    (hdist.mul continuous_const).mul hExp
  have hzero : φ z = 0 := by simp [φ]
  have hopen : IsOpen {w : ℂ | φ w < ε} :=
    isOpen_lt hφ continuous_const
  have hz : z ∈ {w : ℂ | φ w < ε} := by
    change φ z < ε
    rw [hzero]
    exact hε
  obtain ⟨δ, hδ, hball⟩ := (Metric.isOpen_iff.mp hopen) z hz
  refine ⟨δ, hδ, ?_⟩
  intro w hw n
  have hwball : w ∈ Metric.ball z δ := by
    change dist w z < δ
    exact hw
  have hφw : φ w < ε := hball hwball
  calc
    dist (D n z) (D n w) = ‖D n z - D n w‖ :=
      dist_eq_norm (D n z) (D n w)
    _ ≤ (‖z-w‖ * r) * Real.exp ((‖w‖ + ‖z-w‖) * r) :=
      hbound n z w
    _ < ε := hφw

#print axioms Manuscript14Priority3.SpectralExpEquicontinuity.equicontinuity_of_asymmetric_exponential_norm_bound

end Manuscript14Priority3.SpectralExpEquicontinuity
