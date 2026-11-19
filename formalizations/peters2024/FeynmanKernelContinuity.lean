import WoodhouseContinuity
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! Sufficient analytic hypotheses for §§5.4–5.6. Compact time-sliced
integrals are genuine Bochner integrals. Their uniform convergence is a
separate hypothesis, not a claimed construction of a physical propagator. -/
namespace Peters2024
open Set MeasureTheory Filter
noncomputable section

variable {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
  [LocallyCompactSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y] [SecondCountableTopologyEither Y ℂ]
  {μ : Measure Y} [IsLocallyFiniteMeasure μ]

/-- Each compactly truncated finite-dimensional integral is continuous
if its integrand is jointly continuous. -/
theorem continuous_feynman_slice (F : X × Y → ℂ) (hF : Continuous F)
    (s : Set Y) (hs : IsCompact s) :
    Continuous (fun p : X => ∫ y in s, F (p, y) ∂μ) :=
  continuous_parametric_integral_of_continuous (μ := μ) (f := fun p y => F (p, y)) hF hs

/-- A uniform limit of continuous compactly truncated approximations is
continuous. The convergence assumption must be proved for any chosen
discretization of the formal physical path integral. -/
theorem continuous_feynman_limit (F : ℕ → X × Y → ℂ) (hF : ∀ n, Continuous (F n))
    (s : ℕ → Set Y) (hs : ∀ n, IsCompact (s n)) (K : X → ℂ)
    (hlim : TendstoUniformly (fun n p => ∫ y in s n, F n (p, y) ∂μ) K atTop) :
    Continuous K := by
  apply hlim.continuous
  exact (Eventually.of_forall fun n => continuous_feynman_slice (F n) (hF n) (s n) (hs n)).frequently

end
end Peters2024

#print axioms Peters2024.continuous_feynman_slice
#print axioms Peters2024.continuous_feynman_limit
