import SpecialImaginaryPoint.V14119Priority3UniversalNuclearDensity

/-!
# Manuscript 14.119 Priority 3 — uniqueness of any continuous universal determinant

Finite nuclear rank-one operators are dense in the genuine CFC
Schatten-S₁ Banach space. Thus any two complex-valued functionals
that are continuous at an arbitrary trace-class operator T and
agree on ALL genuine finite nuclear truncations must agree at T.

As a global corollary, two continuous functionals that agree on
every finite nuclear sum are equal everywhere in true CFC-S₁.

This closes the **uniqueness** obligation for a putative continuous
Fredholm determinant, not its existence. The operatorial determinant
perturbation inequality is required to construct such a functional.
No determinant continuity is assumed as an axiom.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalContinuousUniqueness

open Filter Topology
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.NuclearRankOne

/-- At any individual genuine CFC-S₁ operator T, two continuous-at-T
functionals agreeing on all finite nuclear rank-one sums must coincide.
No self-adjointness, positivity, diagonality, or basis restriction. -/
theorem continuousAt_functionals_unique_of_finiteNuclear
    (F G : ProbabilisticTheory.TraceClass H → ℂ)
    (T : ProbabilisticTheory.TraceClass H)
    (hF : ContinuousAt F T)
    (hG : ContinuousAt G T)
    (hfinite : ∀ (w : Set H) (s : Finset w) (u v : w → H),
      F (∑ i ∈ s, rankOneS1 (u i) (v i)) =
        G (∑ i ∈ s, rankOneS1 (u i) (v i))) :
    F T = G T := by
  obtain ⟨w, u, v, hT⟩ := traceClass_finiteRank_dense T
  have hFt :
      Tendsto
        (fun s : Finset w => F (∑ i ∈ s, rankOneS1 (u i) (v i)))
        atTop (𝓝 (F T)) :=
    hF.tendsto.comp hT
  have hGt :
      Tendsto
        (fun s : Finset w => G (∑ i ∈ s, rankOneS1 (u i) (v i)))
        atTop (𝓝 (G T)) :=
    hG.tendsto.comp hT
  have hfun :
      (fun s : Finset w => F (∑ i ∈ s, rankOneS1 (u i) (v i))) =
      (fun s : Finset w => G (∑ i ∈ s, rankOneS1 (u i) (v i))) := by
    funext s
    exact hfinite w s u v
  rw [hfun] at hFt
  exact tendsto_nhds_unique hFt hGt

/-- An extension of the finite nuclear determinant, if continuous
throughout genuine CFC-S₁, is unique as a functional. -/
theorem continuous_functionals_ext_of_finiteNuclear
    (F G : ProbabilisticTheory.TraceClass H → ℂ)
    (hF : Continuous F)
    (hG : Continuous G)
    (hfinite : ∀ (w : Set H) (s : Finset w) (u v : w → H),
      F (∑ i ∈ s, rankOneS1 (u i) (v i)) =
        G (∑ i ∈ s, rankOneS1 (u i) (v i))) :
    F = G := by
  funext T
  exact continuousAt_functionals_unique_of_finiteNuclear
    F G T (hF.continuousAt) (hG.continuousAt) hfinite

#print axioms Manuscript14Priority3.UniversalContinuousUniqueness.continuousAt_functionals_unique_of_finiteNuclear
#print axioms Manuscript14Priority3.UniversalContinuousUniqueness.continuous_functionals_ext_of_finiteNuclear

end Manuscript14Priority3.UniversalContinuousUniqueness
