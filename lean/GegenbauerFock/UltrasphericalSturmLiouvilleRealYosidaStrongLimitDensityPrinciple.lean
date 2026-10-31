import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
# V007 — extension of uniformly contractive strong limits from a dense set

If a sequence of bounded real-linear operators on a Banach space is
contractive uniformly in its index, and the orbits converge on a
dense subset, then its orbits converge strongly at every vector.

This is the exact completeness-and-density argument needed for the
Gegenbauer Yosida semigroup limit; it does NOT postulate an
extension of the differential operator or a limiting semigroup.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

/-- A uniformly contractive family of actual bounded linear maps
which converges strongly on a dense set converges strongly everywhere.
The limit is constructed from completeness, not assumed. -/
theorem strongLimit_of_uniform_contractions_on_dense
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℕ → E →L[ℝ] E)
    (hT : ∀ k : ℕ, ‖T k‖ ≤ 1)
    (D : Set E) (hD : Dense D)
    (hconv : ∀ d ∈ D, ∃ y : E,
      Tendsto (fun k : ℕ => T k d) Filter.atTop (nhds y))
    (x : E) :
    ∃ y : E, Tendsto (fun k : ℕ => T k x) Filter.atTop (nhds y) := by
  apply CompleteSpace.complete
  apply Metric.cauchySeq_iff.mpr
  intro eps heps
  obtain ⟨d, hd, hdclose⟩ :=
    hD.exists_dist_lt x (show 0 < eps / 4 by positivity)
  obtain ⟨y, hy⟩ := hconv d hd
  have hc : CauchySeq (fun k : ℕ => T k d) := hy.cauchySeq
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hc)
    (eps / 2) (by positivity)
  have hcontract (k : ℕ) :
      dist (T k x) (T k d) ≤ dist x d := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    calc
      ‖T k (x - d)‖ ≤ ‖T k‖ * ‖x - d‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖x - d‖ :=
        mul_le_mul_of_nonneg_right (hT k) (norm_nonneg _)
      _ = ‖x - d‖ := one_mul _
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hmd := hcontract m
  have hnd := hcontract n
  have hdn : dist (T n d) (T n x) ≤ dist x d := by
    simpa only [dist_comm] using hnd
  have hmiddle : dist (T m d) (T n d) < eps / 2 :=
    hN m hm n hn
  calc
    dist (T m x) (T n x) ≤
        dist (T m x) (T m d) + dist (T m d) (T n x) :=
      dist_triangle _ _ _
    _ ≤ dist (T m x) (T m d) +
        (dist (T m d) (T n d) + dist (T n d) (T n x)) :=
      add_le_add_left (dist_triangle _ _ _) _
    _ < eps := by linarith

#print axioms GegenbauerFock.Ultraspherical.strongLimit_of_uniform_contractions_on_dense

end GegenbauerFock.Ultraspherical
