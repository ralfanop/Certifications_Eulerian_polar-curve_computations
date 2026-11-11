import SpecialImaginaryPoint.V14119Priority3UniversalFredholmExistence

/-!
# Priority 3 — continuity of the actual universal Fredholm determinant in true CFC-S₁ norm

The unconditional, dimension-free trace-norm perturbation inequality
already established for the universal determinant immediately yields
continuity of the map T ↦ det(I + z T) for every fixed z∈ℂ,
throughout the ENTIRE infinite-dimensional CFC trace-class ideal.

The proof explicitly constructs the local epsilon-delta modulus
from the norm of the actual Schatten-S₁ operator difference and
the exponential majorant; it does not assume uniform continuity of
the unweighted determinant on the unbounded ideal.
No normality, positivity, selfadjointness or invertibility is needed.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalTraceNormContinuity

open Filter Topology
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence

/-- The genuine universal Fredholm determinant is continuous
in the TRUE CFC Schatten-S₁ trace norm on ALL operators, for
every fixed spectral parameter. This is not global uniform
continuity on the unbounded ideal. -/
theorem fredholmDet_continuous_traceNorm (z : ℂ) :
    Continuous (fun T : ProbabilisticTheory.TraceClass H =>
      fredholmDet T z) := by
  apply continuous_iff_continuousAt.mpr
  intro T
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let φ : ProbabilisticTheory.TraceClass H → ℝ := fun S =>
    (‖z‖ * ‖S - T‖) *
      Real.exp (‖z‖ * (‖T‖ + ‖S - T‖))
  have hnorm : Continuous (fun S : ProbabilisticTheory.TraceClass H =>
      ‖S - T‖) :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  have hexp : Continuous (fun S : ProbabilisticTheory.TraceClass H =>
      Real.exp (‖z‖ * (‖T‖ + ‖S - T‖))) :=
    Real.continuous_exp.comp
      (continuous_const.mul (continuous_const.add hnorm))
  have hφ : Continuous φ :=
    (continuous_const.mul hnorm).mul hexp
  have hφzero : φ T = 0 := by simp [φ]
  have hopen : IsOpen {S : ProbabilisticTheory.TraceClass H | φ S < ε} :=
    isOpen_lt hφ continuous_const
  have hT : T ∈ {S : ProbabilisticTheory.TraceClass H | φ S < ε} := by
    change φ T < ε
    rw [hφzero]
    exact hε
  obtain ⟨δ, hδ, hball⟩ :=
    (Metric.isOpen_iff.mp hopen) T hT
  refine ⟨δ, hδ, ?_⟩
  intro S hS
  have hSball : S ∈ Metric.ball T δ := by
    change dist S T < δ
    first
    | exact hS
    | simpa only [dist_comm] using hS
  have hsmall : φ S < ε := hball hSball
  have hbase := fredholmDet_add_traceNorm_bound T (S - T) z
  have hadd : T + (S - T) = S := by abel
  rw [hadd] at hbase
  change ‖fredholmDet S z - fredholmDet T z‖ ≤ φ S at hbase
  calc
    dist (fredholmDet S z) (fredholmDet T z) =
        ‖fredholmDet S z - fredholmDet T z‖ :=
      dist_eq_norm (fredholmDet S z) (fredholmDet T z)
    _ ≤ φ S := hbase
    _ < ε := hsmall

#print axioms Manuscript14Priority3.UniversalTraceNormContinuity.fredholmDet_continuous_traceNorm

end Manuscript14Priority3.UniversalTraceNormContinuity
