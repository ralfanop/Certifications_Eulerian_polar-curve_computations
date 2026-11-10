import SpecialImaginaryPoint.V14119Priority3UniversalContinuousUniqueness
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Manuscript 14.119 Priority 3 — existence and uniqueness by dense uniform extension

The subset of genuine CFC-S₁ operators admitting a finite nuclear
rank-one sum is dense in the full CFC-S₁ Banach space. We prove that
EVERY uniformly continuous complex functional on this actual dense
operator sector extends uniquely to a continuous functional on all S₁.

This closes the purely functional-analytic EXTENSION STEP, under the
explicit hypothesis that the finite-nuclear functional is uniformly
continuous in the true trace norm.

**Critical missing input:** proving this uniform continuity for the
particular intrinsic finite Fredholm determinant requires a
dimension-free determinant perturbation bound. Neither is introduced
as an axiom. No universal determinant is asserted yet.
-/

noncomputable section

namespace Manuscript14Priority3.DenseUniformExtension

open Filter Topology
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.NuclearRankOne
open Manuscript14Priority3.UniversalContinuousUniqueness

/-- The actual finite nuclear CFC-S₁ operator sector, defined by
genuine finite sums of rank-one trace-class maps. -/
def finiteNuclearSet : Set (ProbabilisticTheory.TraceClass H) :=
  {T | ∃ (w : Set H) (s : Finset w) (u v : w → H),
      T = ∑ i ∈ s, rankOneS1 (u i) (v i)}

/-- Every actual CFC-S₁ element lies in the trace-norm closure
of the genuine finite nuclear rank-one sector. -/
theorem finiteNuclearSet_dense : Dense finiteNuclearSet := by
  apply dense_iff_closure_eq.mpr
  apply Set.eq_univ_iff_forall.mpr
  intro T
  obtain ⟨w, u, v, hlim⟩ := traceClass_finiteRank_dense T
  apply mem_closure_of_tendsto hlim
  exact Filter.Eventually.of_forall
    (fun s : Finset w => (⟨w, s, u, v, rfl⟩ :
       (∑ i ∈ s, rankOneS1 (u i) (v i)) ∈ finiteNuclearSet))

/-- The canonical uniformly continuous extension of any function
from the genuinely dense finite-nuclear sector into complete ℂ. -/
def extendFiniteFunctional (f : finiteNuclearSet → ℂ) :
    ProbabilisticTheory.TraceClass H → ℂ :=
  finiteNuclearSet_dense.extend f

/-- The extension agrees with the original finite-nuclear values. -/
theorem extendFiniteFunctional_eq (f : finiteNuclearSet → ℂ)
    (hf : UniformContinuous f) (x : finiteNuclearSet) :
    extendFiniteFunctional f x = f x :=
  finiteNuclearSet_dense.extend_of_ind hf x

/-- The extension is uniformly continuous in true CFC trace norm,
not merely pointwise or in the strong operator topology. -/
theorem extendFiniteFunctional_uniformContinuous
    (f : finiteNuclearSet → ℂ) (hf : UniformContinuous f) :
    UniformContinuous (extendFiniteFunctional f) :=
  finiteNuclearSet_dense.uniformContinuous_extend hf

/-- A finite-nuclear functional that is uniformly continuous in
genuine Schatten-S₁ norm has a UNIQUE continuous extension to ALL
CFC-S₁ Hilbert operators. This is an existence-uniqueness theorem
with the still-to-be-proved perturbation/continuity hypothesis. -/
theorem continuous_extension_existsUnique
    (f : finiteNuclearSet → ℂ) (hf : UniformContinuous f) :
    ∃ F : ProbabilisticTheory.TraceClass H → ℂ,
      Continuous F ∧
      (∀ x : finiteNuclearSet, F x = f x) ∧
      (∀ G : ProbabilisticTheory.TraceClass H → ℂ,
        Continuous G →
        (∀ x : finiteNuclearSet, G x = f x) →
        G = F) := by
  refine ⟨extendFiniteFunctional f,
    (extendFiniteFunctional_uniformContinuous f hf).continuous,
    extendFiniteFunctional_eq f hf, ?_⟩
  intro G hG hGfinite
  apply continuous_functionals_ext_of_finiteNuclear
    G (extendFiniteFunctional f) hG
    (extendFiniteFunctional_uniformContinuous f hf).continuous
  intro w s u v
  let x : finiteNuclearSet :=
    ⟨∑ i ∈ s, rankOneS1 (u i) (v i),
      ⟨w, s, u, v, rfl⟩⟩
  exact (hGfinite x).trans (extendFiniteFunctional_eq f hf x).symm

#print axioms Manuscript14Priority3.DenseUniformExtension.finiteNuclearSet_dense
#print axioms Manuscript14Priority3.DenseUniformExtension.extendFiniteFunctional_eq
#print axioms Manuscript14Priority3.DenseUniformExtension.extendFiniteFunctional_uniformContinuous
#print axioms Manuscript14Priority3.DenseUniformExtension.continuous_extension_existsUnique

end Manuscript14Priority3.DenseUniformExtension
