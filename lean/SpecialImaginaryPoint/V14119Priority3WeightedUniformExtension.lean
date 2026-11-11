import SpecialImaginaryPoint.V14119Priority3DenseUniformExtension

/-!
# Priority 3 — weighted uniform extension theorem for the genuine CFC S₁ Fredholm sector

The unweighted Fredholm determinant is NOT uniformly continuous
on unbounded Schatten-S₁(H); thus the unconditional use of the
uniform-extension theorem of PR #113 would be incorrect.

Instead, for any finite-nuclear scalar functional f and parameter
r∈ℝ, define the exponentially weighted scalar functional

    g(T) = exp(-2 r ‖T‖₁) • f(T)

on the actual dense finite-nuclear CFC-S₁ subset. If THIS weighted
function is uniformly continuous, PR #113 constructs its continuous
extension. Multiplication by exp(+2 r ‖T‖₁) yields a unique continuous
extension F of the ORIGINAL finite-nuclear functional f.

This is a precisely conditional theorem: proving weighted uniform
continuity for the actual determinant requires the missing true
S₁ perturbation inequality, not merely a presentation-cost bound.
No new norm inequality is assumed as an axiom, and no holomorphy
claim is made.
-/

noncomputable section

namespace Manuscript14Priority3.WeightedUniformExtension

open Filter Topology
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.NuclearRankOne
open Manuscript14Priority3.DenseUniformExtension
open Manuscript14Priority3.UniversalContinuousUniqueness

/-- Exponentially renormalize a finite-nuclear functional using
the actual CFC-S₁ trace norm. -/
def weightedFiniteFunctional
    (f : finiteNuclearSet → ℂ) (r : ℝ) :
    finiteNuclearSet → ℂ :=
  fun x => Real.exp (-(2 * r * ‖(x : ProbabilisticTheory.TraceClass H)‖)) • f x

/-- Recover an extension of the ORIGINAL unweighted functional by
undoing the scalar weight on the full actual CFC-S₁ Banach space. -/
def restoreFiniteFunctional
    (f : finiteNuclearSet → ℂ) (r : ℝ) :
    ProbabilisticTheory.TraceClass H → ℂ :=
  fun T => Real.exp (2 * r * ‖T‖) •
    extendFiniteFunctional (weightedFiniteFunctional f r) T

/-- Given uniform continuity of the weighted finite-sector
functional, the restored original determinant-like functional is
continuous on ALL CFC-S₁(H). -/
theorem restoreFiniteFunctional_continuous
    (f : finiteNuclearSet → ℂ) (r : ℝ)
    (hf : UniformContinuous (weightedFiniteFunctional f r)) :
    Continuous (restoreFiniteFunctional f r) := by
  have hc :
      Continuous (fun T : ProbabilisticTheory.TraceClass H =>
        Real.exp (2 * r * ‖T‖)) := by
    exact Real.continuous_exp.comp
      (continuous_const.mul continuous_norm)
  have hext :
      Continuous (extendFiniteFunctional (weightedFiniteFunctional f r)) :=
    (extendFiniteFunctional_uniformContinuous (weightedFiniteFunctional f r) hf).continuous
  exact hc.smul hext

/-- The restored extension agrees EXACTLY with the original
finite-nuclear functional, with no assumption of global
uniform continuity for f itself. -/
theorem restoreFiniteFunctional_eq
    (f : finiteNuclearSet → ℂ) (r : ℝ)
    (hf : UniformContinuous (weightedFiniteFunctional f r))
    (x : finiteNuclearSet) :
    restoreFiniteFunctional f r x = f x := by
  unfold restoreFiniteFunctional
  rw [extendFiniteFunctional_eq (weightedFiniteFunctional f r) hf x]
  change Real.exp (2 * r * ‖(x : ProbabilisticTheory.TraceClass H)‖) •
      (Real.exp (-(2 * r * ‖(x : ProbabilisticTheory.TraceClass H)‖)) • f x) =
    f x
  rw [smul_smul]
  have he : Real.exp (2 * r * ‖(x : ProbabilisticTheory.TraceClass H)‖) *
      Real.exp (-(2 * r * ‖(x : ProbabilisticTheory.TraceClass H)‖)) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [he, one_smul]

/-- UNIQUENESS and EXISTENCE on the ENTIRE genuine CFC S₁ Banach space,
conditional on uniform continuity of the exponentially NORMALIZED
finite-nuclear determinant, not of the unweighted determinant.

The missing finite trace-norm perturbation estimate is needed
to discharge `hf` for the actual Fredholm determinant. -/
theorem continuous_extension_of_weighted_uniform
    (f : finiteNuclearSet → ℂ) (r : ℝ)
    (hf : UniformContinuous (weightedFiniteFunctional f r)) :
    ∃ F : ProbabilisticTheory.TraceClass H → ℂ,
      Continuous F ∧
      (∀ x : finiteNuclearSet, F x = f x) ∧
      (∀ G : ProbabilisticTheory.TraceClass H → ℂ,
        Continuous G →
        (∀ x : finiteNuclearSet, G x = f x) →
        G = F) := by
  refine ⟨restoreFiniteFunctional f r,
    restoreFiniteFunctional_continuous f r hf,
    restoreFiniteFunctional_eq f r hf, ?_⟩
  intro G hG hGfinite
  apply continuous_functionals_ext_of_finiteNuclear
    G (restoreFiniteFunctional f r)
      hG (restoreFiniteFunctional_continuous f r hf)
  intro w s u v
  let x : finiteNuclearSet :=
    ⟨∑ i ∈ s, rankOneS1 (u i) (v i),
      ⟨w, s, u, v, rfl⟩⟩
  exact (hGfinite x).trans (restoreFiniteFunctional_eq f r hf x).symm

#print axioms Manuscript14Priority3.WeightedUniformExtension.restoreFiniteFunctional_continuous
#print axioms Manuscript14Priority3.WeightedUniformExtension.restoreFiniteFunctional_eq
#print axioms Manuscript14Priority3.WeightedUniformExtension.continuous_extension_of_weighted_uniform

end Manuscript14Priority3.WeightedUniformExtension
