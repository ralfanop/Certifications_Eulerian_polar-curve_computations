import SpecialImaginaryPoint.V14119Priority3FiniteTwoFamilyDet

/-!
# Priority 3 — sharp finite trace-norm determinant perturbation,
# precisely conditional on optimal finite nuclear presentations

The previously kernel-certified two-family Fredholm determinant bound
holds for chosen nuclear representation costs. The following theorems
identify the exact remaining obligation, without confusing an upper
bound for the actual CFC-S₁ norm with equality.

If the perturbing finite nuclear representation has cost exactly
its true CFC Schatten-S₁ trace norm, the perturbation factor in
the genuine Fredholm determinant inequality is exactly that norm.
If both finite presentations are optimal, the exponential envelope
also uses the two true CFC-S₁ norms, with dimension-independent
constant and arbitrary nonnormal complex operators.

These hypotheses are EXPLICIT theorem arguments, not Lean axioms.
The existence of such optimal finite presentations for all
finite-rank CFC-S₁ operators remains a distinct unproved step.
-/

noncomputable section

namespace Manuscript14Priority3.SharpFiniteTraceNormConditional

open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.FiniteNuclearFredholm
open Manuscript14Priority3.FiniteTwoFamilyDet

/-- Correct exact S₁ perturbation factor, conditional ONLY on the
given finite representation of the perturbation being nuclear-optimal.
The exponential may still use the base operator's presentation cost. -/
theorem detFinite_add_traceNorm_of_optimal_perturbation
    (m n : ℕ) (u v : Fin m → H) (a b : Fin n → H)
    (z : ℂ)
    (hoptimal :
      (∑ j : Fin n, ‖a j‖ * ‖b j‖) =
        ‖finiteNuclear n a b‖) :
    ‖detFinite
        (finiteNuclear m u v + finiteNuclear n a b)
        ⟨sumPresentation m n u v a b⟩ z -
      detFinite (finiteNuclear m u v)
        ⟨canonicalPresentation m u v⟩ z‖ ≤
      (‖z‖ * ‖finiteNuclear n a b‖) *
        Real.exp (‖z‖ * ((∑ i : Fin m, ‖u i‖ * ‖v i‖) +
          ‖finiteNuclear n a b‖)) := by
  simpa only [hoptimal] using
    detFinite_add_nuclear_cost_norm_le_exp m n u v a b z

/-- The fully sharp, dimension-free two-operator finite Fredholm
perturbation estimate, conditional on EXACT finite nuclear
optimality for both actual CFC Schatten-S₁ operators. -/
theorem detFinite_add_true_traceNorms_of_both_optimal
    (m n : ℕ) (u v : Fin m → H) (a b : Fin n → H)
    (z : ℂ)
    (hbase :
      (∑ i : Fin m, ‖u i‖ * ‖v i‖) =
        ‖finiteNuclear m u v‖)
    (hperturb :
      (∑ j : Fin n, ‖a j‖ * ‖b j‖) =
        ‖finiteNuclear n a b‖) :
    ‖detFinite
        (finiteNuclear m u v + finiteNuclear n a b)
        ⟨sumPresentation m n u v a b⟩ z -
      detFinite (finiteNuclear m u v)
        ⟨canonicalPresentation m u v⟩ z‖ ≤
      (‖z‖ * ‖finiteNuclear n a b‖) *
        Real.exp (‖z‖ * (‖finiteNuclear m u v‖ +
          ‖finiteNuclear n a b‖)) := by
  simpa only [hbase, hperturb] using
    detFinite_add_nuclear_cost_norm_le_exp m n u v a b z

#print axioms Manuscript14Priority3.SharpFiniteTraceNormConditional.detFinite_add_traceNorm_of_optimal_perturbation
#print axioms Manuscript14Priority3.SharpFiniteTraceNormConditional.detFinite_add_true_traceNorms_of_both_optimal

end Manuscript14Priority3.SharpFiniteTraceNormConditional
