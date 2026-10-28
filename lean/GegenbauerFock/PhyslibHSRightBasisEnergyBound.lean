import GegenbauerFock.PhyslibHilbertSchmidtTwoSidedIdeal

/-!
# V007 — sharp quantitative right-ideal Hilbert–Schmidt energy bound

For arbitrary complete complex Hilbert H and its genuine basis-defined
Physlib-compatible S₂ predicate, precomposition by B has squared HS
energy at most ‖B‖² times the original squared HS energy. The proof
transports both sums through the Hilbert adjoint, where composition
on the right becomes bounded composition on the left.

No trace-norm triangle inequality, finite-rank restriction or new axiom.
-/

noncomputable section
namespace ProbabilisticTheory.HilbertSchmidt

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Sharp quantitative right-composition S₂ ideal inequality,
computed on an arbitrary complete Hilbert basis. -/
theorem right_basis_energy_le
    (S : H →L[ℂ] H) (hS : IsHilbertSchmidt S)
    (B : H →L[ℂ] H)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    (∑' i : w, ‖(S.comp B) (b i)‖ ^ 2) ≤
      ‖B‖ ^ 2 * (∑' i : w, ‖S (b i)‖ ^ 2) := by
  have hs : Summable (fun i : w => ‖S (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hS
  have hsSB : Summable (fun i : w => ‖(S.comp B) (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b
      (isHilbertSchmidt_comp_right S hS B)
  have hsStar : Summable (fun i : w => ‖S.adjoint (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b
      (isHilbertSchmidt_adjoint S hS)
  have hSBstar :
      (∑' i : w, ‖(S.comp B) (b i)‖ ^ 2) =
        ∑' i : w, ‖(B.adjoint.comp S.adjoint) (b i)‖ ^ 2 := by
    have h := (hasSum_norm_sq_apply_eq_adjoint b b hsSB).tsum_eq
    simpa only [ContinuousLinearMap.adjoint_comp] using h.symm
  have hpoint (i : w) :
      ‖(B.adjoint.comp S.adjoint) (b i)‖ ^ 2 ≤
        ‖B.adjoint‖ ^ 2 * ‖S.adjoint (b i)‖ ^ 2 := by
    change ‖B.adjoint (S.adjoint (b i))‖ ^ 2 ≤ _
    calc
      ‖B.adjoint (S.adjoint (b i))‖ ^ 2 ≤
          (‖B.adjoint‖ * ‖S.adjoint (b i)‖) ^ 2 := by
            exact (sq_le_sq₀ (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
                (ContinuousLinearMap.le_opNorm B.adjoint (S.adjoint (b i)))
      _ = ‖B.adjoint‖ ^ 2 * ‖S.adjoint (b i)‖ ^ 2 := by ring
  have hSBstarSummable :
      Summable (fun i : w =>
        ‖(B.adjoint.comp S.adjoint) (b i)‖ ^ 2) := by
    apply Summable.of_nonneg_of_le
    · intro i
      exact sq_nonneg _
    · exact hpoint
    · exact hsStar.mul_left (‖B.adjoint‖ ^ 2)
  have hnorm : ‖B.adjoint‖ = ‖B‖ := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact norm_star B
  calc
    (∑' i : w, ‖(S.comp B) (b i)‖ ^ 2) =
        ∑' i : w, ‖(B.adjoint.comp S.adjoint) (b i)‖ ^ 2 := hSBstar
    _ ≤ ∑' i : w,
        ‖B.adjoint‖ ^ 2 * ‖S.adjoint (b i)‖ ^ 2 :=
      hSBstarSummable.tsum_le_tsum hpoint
        (hsStar.mul_left (‖B.adjoint‖ ^ 2))
    _ = ‖B.adjoint‖ ^ 2 *
        (∑' i : w, ‖S.adjoint (b i)‖ ^ 2) := tsum_mul_left
    _ = ‖B‖ ^ 2 * (∑' i : w, ‖S (b i)‖ ^ 2) := by
      rw [hnorm]
      congr 1
      exact (hasSum_norm_sq_apply_eq_adjoint b b hs).tsum_eq

#print axioms ProbabilisticTheory.HilbertSchmidt.right_basis_energy_le

end ProbabilisticTheory.HilbertSchmidt
