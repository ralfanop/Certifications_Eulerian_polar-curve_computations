import SpecialImaginaryPoint.V14119Priority3MultiIndexGramPerturb
import SpecialImaginaryPoint.V14119Priority3FiniteIntrinsicFunctional

/-!
# Priority 3 — multi-term nuclear perturbation of the ACTUAL intrinsic CFC-S₁ finite Fredholm functional

Combine the dimension-free multi-index determinant telescoping theorem
with the previously certified representation-independent intrinsic
Fredholm determinant of genuine finite nuclear trace-class operators.

For arbitrary complex z and arbitrary finite sets of nuclear indices,
the difference between two actual CFC-S₁ operator determinant values
has a uniform-in-dimension bound by the omitted nuclear MASS times
an exponential envelope of the original full finite presentation.

This is not yet an S₁-norm Lipschitz theorem for arbitrary finite-rank
differences: the omitted presentation mass remains to be optimised
to the exact norm of the difference. The full infinite S₁ determinant
still needs the locally uniform/ball-wise continuous extension.
-/

noncomputable section

namespace Manuscript14Priority3.IntrinsicFiniteS1MultitermBound

open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.FiniteNuclearFredholm
open Manuscript14Priority3.MultiIndexGramPerturb

/-- Dimension-independent nuclear-cost estimate for TWO actual
finite-nuclear complex CFC-S₁ Fredholm determinant values, after
erasing any finite set s of nuclear terms. -/
theorem detFinite_zeroOut_nuclear_cost_norm_le_exp
    {m : ℕ} (u v : Fin m → H) (z : ℂ) (s : Finset (Fin m)) :
    ‖detFinite (finiteNuclear m u v)
        ⟨canonicalPresentation m u v⟩ z -
      detFinite (finiteNuclear m (zeroOut u s) v)
        ⟨canonicalPresentation m (zeroOut u s) v⟩ z‖ ≤
      (∑ i ∈ s, ‖z‖ * (‖u i‖ * ‖v i‖)) *
        Real.exp (∑ i : Fin m, ‖z‖ * (‖u i‖ * ‖v i‖)) := by
  rw [detFinite_finiteNuclear, detFinite_finiteNuclear]
  exact det_sub_det_zeroOut_norm_le_exp u v z s

/-- Independence of presentation witnesses: the same multi-index
perturbation estimate holds for arbitrary proofs that each genuine
CFC-S₁ finite-rank operator has a finite nuclear presentation. -/
theorem detFinite_zeroOut_any_proof_norm_le_exp
    {m : ℕ} (u v : Fin m → H) (z : ℂ) (s : Finset (Fin m))
    (h₁ : HasFinitePresentation (finiteNuclear m u v))
    (h₂ : HasFinitePresentation (finiteNuclear m (zeroOut u s) v)) :
    ‖detFinite (finiteNuclear m u v) h₁ z -
      detFinite (finiteNuclear m (zeroOut u s) v) h₂ z‖ ≤
      (∑ i ∈ s, ‖z‖ * (‖u i‖ * ‖v i‖)) *
        Real.exp (∑ i : Fin m, ‖z‖ * (‖u i‖ * ‖v i‖)) := by
  rw [detFinite_independent_of_proof (finiteNuclear m u v)
        h₁ ⟨canonicalPresentation m u v⟩ z,
      detFinite_independent_of_proof
        (finiteNuclear m (zeroOut u s) v)
        h₂ ⟨canonicalPresentation m (zeroOut u s) v⟩ z]
  exact detFinite_zeroOut_nuclear_cost_norm_le_exp u v z s

#print axioms Manuscript14Priority3.IntrinsicFiniteS1MultitermBound.detFinite_zeroOut_nuclear_cost_norm_le_exp
#print axioms Manuscript14Priority3.IntrinsicFiniteS1MultitermBound.detFinite_zeroOut_any_proof_norm_le_exp

end Manuscript14Priority3.IntrinsicFiniteS1MultitermBound
