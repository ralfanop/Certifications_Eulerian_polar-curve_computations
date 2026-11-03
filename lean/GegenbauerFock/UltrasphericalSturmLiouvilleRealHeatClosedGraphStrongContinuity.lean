import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatClosedGraphNormContraction
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitFullC0

/-!
# V007 — strong right continuity of the genuine Gegenbauer heat orbit in graph norm

The actual strongly constructed heat semigroup is contractive on the full
weighted real L², preserves the domain of the canonical closure of the
polynomial Sturm differential operator and commutes with its action.

For each f in the genuine closed Sturm domain, the sum of the L² increments
of H_s f and H_s (closure A) f converges to zero as s decreases to zero.
Domain invariance and commutation identify this sum with the graph-norm
increment of the genuine closed differential operator (not a coefficient
model), hence the restricted semigroup is strongly continuous in graph norm.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- For arbitrary data in the *actual canonical closed Sturm domain*, the
full heat orbit converges strongly at zero in the canonical sum graph norm.
The domain invariance/commutation theorem identifies the second summand
with the closed Sturm action on the evolved vector for nonnegative time. -/
theorem sturmRealHeatLimit_closed_graph_norm_tendsto_zero
    (lam : ℝ) (hlam : 0 < lam)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    Tendsto
      (fun s : ℝ =>
        ‖sturmRealHeatLimitNonnegativeExtended lam hlam s
          (x : SturmH lam) - (x : SturmH lam)‖ +
        ‖sturmRealHeatLimitNonnegativeExtended lam hlam s
          ((sturmRealPartialOperator lam hlam).closure x) -
          (sturmRealPartialOperator lam hlam).closure x‖)
      (𝓝[≥] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  let A := (sturmRealPartialOperator lam hlam).closure
  have hfirst :
      Tendsto
        (fun s : ℝ =>
          sturmRealHeatLimitNonnegativeExtended lam hlam s
            (x : SturmH lam) - (x : SturmH lam))
        (𝓝[≥] (0 : ℝ)) (𝓝 (0 : SturmH lam)) := by
    simpa only [sub_self] using
      (sturmRealHeatLimitNonnegativeExtended_allL2_tendsto_zero
        lam hlam (x : SturmH lam)).sub
        (tendsto_const_nhds (x := (x : SturmH lam)))
  have hsecond :
      Tendsto
        (fun s : ℝ =>
          sturmRealHeatLimitNonnegativeExtended lam hlam s (A x) - A x)
        (𝓝[≥] (0 : ℝ)) (𝓝 (0 : SturmH lam)) := by
    simpa only [sub_self] using
      (sturmRealHeatLimitNonnegativeExtended_allL2_tendsto_zero
        lam hlam (A x)).sub (tendsto_const_nhds (x := A x))
  have hn1 :
      Tendsto
        (fun s : ℝ =>
          ‖sturmRealHeatLimitNonnegativeExtended lam hlam s
            (x : SturmH lam) - (x : SturmH lam)‖)
        (𝓝[≥] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using hfirst.norm
  have hn2 :
      Tendsto
        (fun s : ℝ =>
          ‖sturmRealHeatLimitNonnegativeExtended lam hlam s (A x) - A x‖)
        (𝓝[≥] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using hsecond.norm
  simpa only [add_zero] using hn1.add hn2

/-- For each nonnegative time the evolved vector lies in the true closed
Sturm domain, and its closed Sturm image is the evolved image. Together with
the preceding limit this is strong continuity in the graph topology. -/
theorem sturmRealHeatLimit_closed_graph_continuity_and_invariance
    (lam : ℝ) (hlam : 0 < lam)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    (∀ s : ℝ, 0 ≤ s →
      ∃ z : (sturmRealPartialOperator lam hlam).closure.domain,
        (z : SturmH lam) =
          sturmRealHeatLimitNonnegativeExtended lam hlam s
            (x : SturmH lam) ∧
        (sturmRealPartialOperator lam hlam).closure z =
          sturmRealHeatLimitNonnegativeExtended lam hlam s
            ((sturmRealPartialOperator lam hlam).closure x)) ∧
    Tendsto
      (fun s : ℝ =>
        ‖sturmRealHeatLimitNonnegativeExtended lam hlam s
          (x : SturmH lam) - (x : SturmH lam)‖ +
        ‖sturmRealHeatLimitNonnegativeExtended lam hlam s
          ((sturmRealPartialOperator lam hlam).closure x) -
          (sturmRealPartialOperator lam hlam).closure x‖)
      (𝓝[≥] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  refine ⟨?_, sturmRealHeatLimit_closed_graph_norm_tendsto_zero lam hlam x⟩
  intro s hs
  obtain ⟨z, hz, hAz⟩ :=
    sturmRealHeatLimitCLM_closed_domain_invariant_commutes lam hlam s hs x
  refine ⟨z, ?_, ?_⟩
  · simpa [sturmRealHeatLimitNonnegativeExtended, max_eq_right hs] using hz
  · simpa [sturmRealHeatLimitNonnegativeExtended, max_eq_right hs] using hAz

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimit_closed_graph_norm_tendsto_zero
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimit_closed_graph_continuity_and_invariance

end GegenbauerFock.Ultraspherical
