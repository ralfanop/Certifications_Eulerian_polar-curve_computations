import SpecialImaginaryPoint.V14119Priority3ExactGramPrincipalExpansion

/-!
# Priority 3 — true complex Gram determinant one-step perturbation estimate

This bridges the exact determinant/principal-minor identity of PR #118
to the inserted-nuclear-term estimate of PR #117.  For every finite
complex mixed Gram family and every index a, the full genuine
determinant differs from the expansion over all indices other than a
by at most the nuclear cost of that single term, times a
dimension-independent exponential factor.

It remains to identify the restricted expansion over the indices other
than a with the finite intrinsic Fredholm determinant of the
corresponding shorter nuclear presentation.  Consequently, this
module does not yet assert the operatorial Schatten-S₁ perturbation
inequality or the universal S₁ extension.
-/

noncomputable section

namespace Manuscript14Priority3.FiniteGramOneStepDet

open Matrix
open scoped InnerProductSpace Ring
open Manuscript14Priority3.MinorExpansionIncrement
open Manuscript14Priority3.WeightedGramMinorStep
open Manuscript14Priority3.ExactGramPrincipalExpansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Dimension-free first-order perturbation control for an ACTUAL
complex mixed-Gram determinant (not just an abstract subset sum):
removing one nuclear index a changes the full Fredholm expansion by
at most its nuclear cost times the exponential mass of the rest.
Arbitrary complex z and singular, nonnormal G are allowed. -/
theorem full_det_sub_omitted_index_expansion_norm_le {m : ℕ}
    (u v : Fin m → E) (z : ℂ) (a : Fin m) :
    ‖(1 + z •
        Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).det -
      principalExpansion (weightedGramMinor u v z)
        (Finset.univ.erase a)‖ ≤
      (‖z‖ * (‖u a‖ * ‖v a‖)) *
        Real.exp (∑ i ∈ Finset.univ.erase a,
          ‖z‖ * (‖u i‖ * ‖v i‖)) := by
  have ha : a ∉ (Finset.univ.erase a : Finset (Fin m)) :=
    Finset.not_mem_erase a Finset.univ
  have hfull :
      insert a (Finset.univ.erase a : Finset (Fin m)) = Finset.univ :=
    Finset.insert_erase (Finset.mem_univ a)
  have hbound :=
    weightedGramMinor_expansion_insert_norm_le_exp u v z
      (Finset.univ.erase a) a ha
  rw [hfull, weightedGram_full_expansion_eq_det] at hbound
  exact hbound

#print axioms Manuscript14Priority3.FiniteGramOneStepDet.full_det_sub_omitted_index_expansion_norm_le

end Manuscript14Priority3.FiniteGramOneStepDet
