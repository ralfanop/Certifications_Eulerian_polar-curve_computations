import GegenbauerFock.UltrasphericalSturmLiouvilleActualComplexHeatFullC0

/-!
# V007 — strong right continuity at every nonnegative time of actual complex heat

From the independently kernel-checked exact complex operator semigroup
law and strong continuity at time zero, the full complex-valued
weighted L² heat orbit is continuous from the right at every t >= 0.

This is proved on the ACTUAL complex Gegenbauer probability-weighted
L², not an auxiliary coefficient space. The argument composes the
strongly convergent zero-time orbit with the bounded complex operator
H^C_t, and uses the exact nonnegative-time semigroup identity.

It is compatible with but distinct from the unrelated complex Fock Gram.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev HC (lam : ℝ) := Lp ℂ 2 (measure lam)

/-- For every t>=0 and f in actual complex weighted L²,
H_(t+h) f tends to H_t f as h decreases to zero through nonnegative
increments (represented by max 0 h for a total family). -/
theorem sturmActualComplexHeatCLM_tendsto_at_nonnegative_time_right
    (lam : ℝ) (hlam : 0 < lam)
    (t : ℝ) (ht : 0 ≤ t) (f : HC lam) :
    Tendsto
      (fun h : ℝ =>
        sturmActualComplexHeatCLM lam hlam
          (t + max (0 : ℝ) h)
          (add_nonneg ht (le_max_left (0 : ℝ) h)) f)
      (𝓝[≥] (0 : ℝ))
      (𝓝 (sturmActualComplexHeatCLM lam hlam t ht f)) := by
  let T := sturmActualComplexHeatCLM lam hlam t ht
  have hzero :=
    sturmActualComplexHeatNonnegativeExtended_allL2_tendsto_zero
      lam hlam f
  have hcomposed :
      Tendsto
        (fun h : ℝ =>
          T (sturmActualComplexHeatNonnegativeExtended lam hlam h f))
        (𝓝[≥] (0 : ℝ)) (𝓝 (T f)) :=
    (T.continuous.tendsto f).comp hzero
  have hpoint (h : ℝ) :
      sturmActualComplexHeatCLM lam hlam
          (t + max (0 : ℝ) h)
          (add_nonneg ht (le_max_left (0 : ℝ) h)) f =
      T (sturmActualComplexHeatNonnegativeExtended lam hlam h f) := by
    change sturmActualComplexHeatCLM lam hlam
        (t + max (0 : ℝ) h)
        (add_nonneg ht (le_max_left (0 : ℝ) h)) f =
      sturmActualComplexHeatCLM lam hlam t ht
        (sturmActualComplexHeatCLM lam hlam
          (max (0 : ℝ) h) (le_max_left (0 : ℝ) h) f)
    rw [sturmActualComplexHeatCLM_add lam hlam t (max (0 : ℝ) h)
      ht (le_max_left (0 : ℝ) h)]
    rfl
  have hfun :
      (fun h : ℝ =>
        sturmActualComplexHeatCLM lam hlam
          (t + max (0 : ℝ) h)
          (add_nonneg ht (le_max_left (0 : ℝ) h)) f) =
      (fun h : ℝ =>
        T (sturmActualComplexHeatNonnegativeExtended lam hlam h f)) := by
    funext h
    exact hpoint h
  rw [hfun]
  exact hcomposed

#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeatCLM_tendsto_at_nonnegative_time_right

end GegenbauerFock.Ultraspherical
