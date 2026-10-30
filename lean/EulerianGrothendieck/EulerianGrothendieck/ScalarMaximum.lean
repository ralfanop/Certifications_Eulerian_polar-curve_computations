import EulerianGrothendieck.ProjectionScalarNorm
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact

noncomputable section
namespace EulerianGrothendieck
set_option maxHeartbeats 1000000

theorem torusPoint_compact : IsCompact {u : FourSpace | IsTorusPoint u} := by
  have hc : IsClosed {u : FourSpace | IsTorusPoint u} := by
    change IsClosed {u : FourSpace | ∀ i, ‖u i‖=1}
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_eq (by fun_prop) continuous_const
  have hb : Bornology.IsBounded {u : FourSpace | IsTorusPoint u} := by
    apply (Metric.isBounded_closedBall (x:=(0:FourSpace)) (r:=2)).subset
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := torusPoint_norm_sq u hu
    nlinarith [norm_nonneg u]
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hc,hb⟩

theorem projectionScalarNorm_attained (U : Submodule ℂ FourSpace) :
    ∃ u : FourSpace, IsTorusPoint u ∧ projectionScalarNorm U=‖U.starProjection u‖^2 := by
  have hne : Set.Nonempty {u : FourSpace | IsTorusPoint u} :=
    ⟨WithLp.toLp 2 (fun _ => (1:ℂ)), by intro i; norm_num⟩
  have hc : Continuous (fun u : FourSpace => ‖U.starProjection u‖^2) := by fun_prop
  obtain ⟨u,hu,hmax⟩ := torusPoint_compact.exists_isMaxOn hne hc.continuousOn
  refine ⟨u,hu,le_antisymm ?_ (projectionScalarNorm_ge U u hu)⟩
  apply csSup_le (projectionScalarValues_nonempty U)
  rintro r ⟨v,hv,rfl⟩
  exact hmax hv

end EulerianGrothendieck
