import Manuscript15.PantographDyadicUniqueContinuation
import Mathlib.Topology.MetricSpace.Basic

/-!
# Manuscript 15 — global rigidity of nonlinear pantograph solutions from one germ

Any two GLOBAL differentiable real solutions of the exact Eulerian
nonlinear pantograph equation
  y'(t) = 1 - 2*(y(t/2))^2
that coincide on some neighborhood of the origin must agree at ALL
real arguments.

Unlike a premise requiring a chosen symmetric closed interval, the
hypothesis is the natural local-germ equality in the neighborhood filter
(𝓝 0). This is the topological uniqueness statement used to bridge
subsequent local analytic rigidity with global cycloidal uniqueness.

We do not claim that the mere equality y(0)=0 proves equality of germs.
That local Cauchy uniqueness remains a separate issue.
-/

noncomputable section
namespace Manuscript15

open Set Filter Topology

/-- Identity of germs at the origin is sufficient for GLOBAL
uniqueness of nonlinear pantograph solutions on all real t. -/
theorem pantograph_eq_of_germ_eq_zero
    (f g : ℝ → ℝ)
    (hf : SolvesEulerianPantograph f)
    (hg : SolvesEulerianPantograph g)
    (hlocal : f =ᶠ[𝓝 (0 : ℝ)] g) :
    f = g := by
  have hnhds : {t : ℝ | f t = g t} ∈ 𝓝 (0 : ℝ) := hlocal
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hnhds
  have hR : (0 : ℝ) < ε / 2 := by linarith
  have hclosed : EqOn f g (Icc (-(ε / 2)) (ε / 2)) := by
    intro t ht
    have hhalf : |t| ≤ ε / 2 :=
      abs_le.mpr ⟨ht.1, ht.2⟩
    have htε : |t| < ε := lt_of_le_of_lt hhalf (by linarith)
    apply hsub
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using htε
  exact pantograph_eq_of_eqOn_near_zero f g hf hg
    (ε / 2) hR hclosed

/-- Sine is the unique global real pantograph solution with the same
LOCAL GERM at t=0, without presupposing an explicit radius. -/
theorem pantograph_eq_sine_of_germ_eq_zero
    (f : ℝ → ℝ)
    (hf : SolvesEulerianPantograph f)
    (hlocal : f =ᶠ[𝓝 (0 : ℝ)] Real.sin) :
    f = Real.sin :=
  pantograph_eq_of_germ_eq_zero f Real.sin hf
    (fun t => sine_pantograph_hasDerivAt t) hlocal

#print axioms Manuscript15.pantograph_eq_of_germ_eq_zero
#print axioms Manuscript15.pantograph_eq_sine_of_germ_eq_zero

end Manuscript15
