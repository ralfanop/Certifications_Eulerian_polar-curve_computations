import Mathlib

/-!
# Priority 3 — exponential trace-norm perturbation implies
# uniform-in-compression-index equicontinuity

If D_n:E→ℂ satisfy, with a fixed real r≥0,
  |D_n(T)-D_n(S)| ≤ r‖T-S‖ exp(r(‖T‖+‖S‖))
for ALL n and ALL T,S in a normed additive group E, they are
equicontinuous at every T, with one neighborhood working for every n.
This is the exact topological implication needed to combine the
unconditional true CFC-S₁ finite Hilbert compression estimate and
the dense-to-global Cauchy convergence lemma, without asserting
unproved global uniform continuity of unweighted determinants.
-/

noncomputable section
namespace Manuscript14Priority3.ExpTraceNormEquicont

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E]

/-- A single dimension-independent exponential perturbation
majorant gives genuine pointwise equicontinuity simultaneously
for an arbitrary sequence of complex scalar functionals. -/
theorem equicontinuity_of_exponential_norm_perturbation
    (D : ℕ → E → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ n : ℕ, ∀ x y : E,
      ‖D n x - D n y‖ ≤
        (r * ‖x-y‖) *
          Real.exp (r * (‖x‖ + ‖y‖))) :
    ∀ x : E, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ y : E, dist x y < δ →
          ∀ n : ℕ, dist (D n x) (D n y) < ε := by
  intro x ε hε
  let φ : E → ℝ := fun y =>
    (r * ‖x-y‖) * Real.exp (r * (‖x‖ + ‖y‖))
  have hdist : Continuous (fun y : E => ‖x-y‖) :=
    continuous_norm.comp (continuous_const.sub continuous_id)
  have hsum : Continuous (fun y : E => ‖x‖ + ‖y‖) :=
    continuous_const.add continuous_norm
  have hexp : Continuous (fun y : E =>
      Real.exp (r * (‖x‖ + ‖y‖))) :=
    Real.continuous_exp.comp (continuous_const.mul hsum)
  have hφ : Continuous φ :=
    (continuous_const.mul hdist).mul hexp
  have hφx : φ x = 0 := by simp [φ]
  have hopen : IsOpen {y : E | φ y < ε} :=
    isOpen_lt hφ continuous_const
  have hx : x ∈ {y : E | φ y < ε} := by
    change φ x < ε
    rw [hφx]
    exact hε
  obtain ⟨δ, hδ, hball⟩ :=
    (Metric.isOpen_iff.mp hopen) x hx
  refine ⟨δ, hδ, ?_⟩
  intro y hy n
  have hyball : y ∈ Metric.ball x δ := by
    change dist y x < δ
    simpa only [dist_comm y x] using hy
  have hyφ : φ y < ε := hball hyball
  calc
    dist (D n x) (D n y) = ‖D n x - D n y‖ := dist_eq_norm (D n x) (D n y)
    _ ≤ (r * ‖x-y‖) * Real.exp (r * (‖x‖ + ‖y‖)) :=
      hbound n x y
    _ < ε := hyφ

#print axioms Manuscript14Priority3.ExpTraceNormEquicont.equicontinuity_of_exponential_norm_perturbation

end Manuscript14Priority3.ExpTraceNormEquicont
