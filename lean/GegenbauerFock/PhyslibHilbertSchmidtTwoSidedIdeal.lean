import GegenbauerFock.PhyslibHilbertSchmidtAdditive

/-!
# V007 — abstract two-sided Hilbert--Schmidt operator ideal

The source-compatible Physlib S₂ predicate is stable under multiplication
by any bounded endomorphism on either side, for an arbitrary complete
complex Hilbert space. Unlike V007's earlier Fock-specific row argument,
this is the general, basis-independent endomorphism statement.

The right-ideal law uses the already checked HS-adjoint basis transfer.
These lemmas are prerequisites for S₂*S₂ ⊆ S₁ and eventual S₁
two-sided ideal closure; none of those stronger claims is made here.
-/

noncomputable section
namespace ProbabilisticTheory.HilbertSchmidt

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Adjoints of genuinely Hilbert--Schmidt endomorphisms remain S₂.
The proof uses the established complete-basis Parseval transfer. -/
theorem isHilbertSchmidt_adjoint
    (S : H →L[ℂ] H) (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt S.adjoint := by
  obtain ⟨w, b, hs⟩ := hS
  exact ⟨w, b, summable_norm_sq_adjoint_of_summable_norm_sq b hs⟩

/-- Left multiplication by any bounded endomorphism preserves S₂. -/
theorem isHilbertSchmidt_comp_left
    (S : H →L[ℂ] H) (hS : IsHilbertSchmidt S)
    (A : H →L[ℂ] H) :
    IsHilbertSchmidt (A.comp S) := by
  obtain ⟨w, b, hs⟩ := hS
  refine ⟨w, b, ?_⟩
  have hbnd (i : w) :
      ‖(A.comp S) (b i)‖ ^ 2 ≤
        ‖A‖ ^ 2 * ‖S (b i)‖ ^ 2 := by
    change ‖A (S (b i))‖ ^ 2 ≤
      ‖A‖ ^ 2 * ‖S (b i)‖ ^ 2
    calc
      ‖A (S (b i))‖ ^ 2 ≤ (‖A‖ * ‖S (b i)‖) ^ 2 := by
        exact (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
            (ContinuousLinearMap.le_opNorm A (S (b i)))
      _ = ‖A‖ ^ 2 * ‖S (b i)‖ ^ 2 := by ring
  apply Summable.of_nonneg_of_le
  · intro i
    exact sq_nonneg _
  · exact hbnd
  · exact hs.mul_left (‖A‖ ^ 2)

/-- Right multiplication preserves S₂, with no common-basis
hypothesis: pass to adjoints, apply the left-ideal law, and return. -/
theorem isHilbertSchmidt_comp_right
    (S : H →L[ℂ] H) (hS : IsHilbertSchmidt S)
    (B : H →L[ℂ] H) :
    IsHilbertSchmidt (S.comp B) := by
  have hstar : IsHilbertSchmidt S.adjoint :=
    isHilbertSchmidt_adjoint S hS
  have hleft : IsHilbertSchmidt (B.adjoint.comp S.adjoint) :=
    isHilbertSchmidt_comp_left S.adjoint hstar B.adjoint
  have hresult : IsHilbertSchmidt
      (B.adjoint.comp S.adjoint).adjoint :=
    isHilbertSchmidt_adjoint (B.adjoint.comp S.adjoint) hleft
  simpa only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint] using hresult

/-- General two-sided ideal law for arbitrary Hilbert endomorphisms. -/
theorem isHilbertSchmidt_twoSided
    (S : H →L[ℂ] H) (hS : IsHilbertSchmidt S)
    (A B : H →L[ℂ] H) :
    IsHilbertSchmidt (A.comp (S.comp B)) :=
  isHilbertSchmidt_comp_left (S.comp B)
    (isHilbertSchmidt_comp_right S hS B) A

#print axioms ProbabilisticTheory.HilbertSchmidt.isHilbertSchmidt_adjoint
#print axioms ProbabilisticTheory.HilbertSchmidt.isHilbertSchmidt_comp_left
#print axioms ProbabilisticTheory.HilbertSchmidt.isHilbertSchmidt_comp_right
#print axioms ProbabilisticTheory.HilbertSchmidt.isHilbertSchmidt_twoSided

end ProbabilisticTheory.HilbertSchmidt
