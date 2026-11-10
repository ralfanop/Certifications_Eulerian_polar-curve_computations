import SpecialImaginaryPoint.V14119Priority3MinorExpansionIncrement
import SpecialImaginaryPoint.V14119Priority3UnrestrictedMixedGramHadamard

/-!
# Priority 3 — sharp incremental bound for actual complex mixed Gram principal minors

Specialize the abstract principal-subset increment certificate to
the actual determinant of EVERY principal submatrix of a genuinely
complex mixed-Gram matrix G_ij = ⟪v_i,u_j⟫.

For arbitrary complex z, finite s of nuclear indices, and a ∉ s,
the difference between the weighted principal-minor expansions for
s ∪ {a} and s has the sharp first-order dimension-free envelope

  |Δ| ≤ |z| ‖u_a‖‖v_a‖ exp(|z| Σ_{i∈s} ‖u_i‖‖v_i‖).

This no longer assumes a generic hminor: it uses the kernel-certified
unrestricted Gram–Hadamard sharp theorem on the actual complex
Gram minors. The remaining bridge is identifying these weighted
expansions with the *intrinsic finite-rank Fredholm determinants*
for the corresponding rank-one sums, including differing lengths.
-/

noncomputable section

namespace Manuscript14Priority3.WeightedGramMinorStep

open Matrix Polynomial
open scoped InnerProductSpace Ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Weighted determinant of a true complex mixed-Gram principal minor. -/
def weightedGramMinor {m : ℕ} (u v : Fin m → E)
    (z : ℂ) (s : Finset (Fin m)) : ℂ :=
  z ^ s.card *
    ((Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).submatrix
      (Subtype.val : s → Fin m) (Subtype.val : s → Fin m)).det

/-- Removing an index from a subset containing it yields an exact
first-order bound from unrestricted mixed-Gram Hadamard, without
dimension-dependent combinatorial factors. -/
theorem weightedGramMinor_insert_norm_le {m : ℕ}
    (u v : Fin m → E) (z : ℂ)
    (s : Finset (Fin m)) (a : Fin m) (ha : a ∉ s)
    (t : Finset (Fin m)) (ht : t ∈ s.powerset) :
    ‖weightedGramMinor u v z (insert a t)‖ ≤
      (‖z‖ * (‖u a‖ * ‖v a‖)) *
        ∏ i ∈ t, (‖z‖ * (‖u i‖ * ‖v i‖)) := by
  have hat : a ∉ t := by
    intro h
    exact ha ((Finset.mem_powerset.mp ht) h)
  let st : Finset (Fin m) := insert a t
  have hcard : st.card = t.card + 1 := by
    exact Finset.card_insert_of_notMem hat
  have hdet :=
    Manuscript14Priority3.UnrestrictedMixedGramHadamard.mixedGram_principal_minor_norm_le_sharp
      u v st
  change ‖weightedGramMinor u v z st‖ ≤ _
  calc
    ‖weightedGramMinor u v z st‖ =
        ‖z‖ ^ (t.card + 1) *
          ‖((Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).submatrix
            (Subtype.val : st → Fin m)
            (Subtype.val : st → Fin m)).det‖ := by
      simp only [weightedGramMinor, norm_mul, norm_pow, hcard]
    _ ≤ ‖z‖ ^ (t.card + 1) *
          (∏ i ∈ st, ‖u i‖ * ‖v i‖) :=
      mul_le_mul_of_nonneg_left hdet (pow_nonneg (norm_nonneg z) _)
    _ = (‖z‖ * (‖u a‖ * ‖v a‖)) *
          (∏ i ∈ t, ‖z‖ * (‖u i‖ * ‖v i‖)) := by
      change ‖z‖ ^ (t.card + 1) *
          (∏ i ∈ insert a t, ‖u i‖ * ‖v i‖) = _
      rw [Finset.prod_insert hat]
      simp only [Finset.prod_mul_distrib, Finset.prod_const]
      rw [pow_succ]
      ring

/-- The first-order exponential perturbation control for the
ACTUAL weighted complex Gram principal-minor expansion, without
any assumptions on positivity, normality or vector independence. -/
theorem weightedGramMinor_expansion_insert_norm_le_exp {m : ℕ}
    (u v : Fin m → E) (z : ℂ)
    (s : Finset (Fin m)) (a : Fin m) (ha : a ∉ s) :
    ‖Manuscript14Priority3.MinorExpansionIncrement.principalExpansion
        (weightedGramMinor u v z) (insert a s) -
      Manuscript14Priority3.MinorExpansionIncrement.principalExpansion
        (weightedGramMinor u v z) s‖ ≤
      (‖z‖ * (‖u a‖ * ‖v a‖)) *
        Real.exp (∑ i ∈ s, ‖z‖ * (‖u i‖ * ‖v i‖)) := by
  exact Manuscript14Priority3.MinorExpansionIncrement.principalExpansion_insert_norm_le_exp
    (weightedGramMinor u v z) s a ha
    (fun i => ‖z‖ * (‖u i‖ * ‖v i‖))
    (fun i hi => by positivity)
    (weightedGramMinor_insert_norm_le u v z s a ha)

#print axioms Manuscript14Priority3.WeightedGramMinorStep.weightedGramMinor_insert_norm_le
#print axioms Manuscript14Priority3.WeightedGramMinorStep.weightedGramMinor_expansion_insert_norm_le_exp

end Manuscript14Priority3.WeightedGramMinorStep
