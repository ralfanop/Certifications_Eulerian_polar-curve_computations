import GegenbauerFock.PhyslibTraceBasisIndependence

/-!
# V007 — unrestricted-basis addition of arbitrary positive S₁ operators

Given two positive trace-class bounded endomorphisms of an arbitrary
complete complex Hilbert space, their CFC-absolute S₁ witnesses
may initially be on unrelated Hilbert bases. Basis invariance of
the absolute-value diagonal proves summability on a COMMON Hilbert
basis. Thus the sum is trace class and the TRUE CFC trace norm is
additive, without finite dimensionality, commutativity or a priori
common-basis assumptions.

This is closure and exact trace additivity of the positive S₁ cone,
NOT the general additive closure or triangle inequality for
non-selfadjoint class S₁, and not a Banach completion.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every positive trace-class operator has a summable ordinary
diagonal on ANY complete Hilbert basis, not only on its witness basis. -/
theorem positive_diagonal_summable_any_basis
    (T : H →L[ℂ] H) (hpos : 0 ≤ T) (hT : IsTraceClass T)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    Summable (fun i : w => (inner ℂ (b i) (T (b i))).re) := by
  have habs := summable_inner_abs_of_hilbertBasis hT b
  simpa only [CFC.abs_of_nonneg T hpos] using habs

/-- Arbitrary positive S₁ summands can have entirely different
initial witnessing bases; their sum still lies in CFC-based S₁. -/
theorem isTraceClass_add_of_nonneg
    (A B : H →L[ℂ] H)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAc : IsTraceClass A) (hBc : IsTraceClass B) :
    IsTraceClass (A + B) := by
  let w : Set H := hAc.choose
  let b : HilbertBasis w ℂ H := hAc.choose_spec.choose
  have hsA : Summable (fun i : w =>
      (inner ℂ (b i) (A (b i))).re) :=
    positive_diagonal_summable_any_basis A hA hAc b
  have hsB : Summable (fun i : w =>
      (inner ℂ (b i) (B (b i))).re) :=
    positive_diagonal_summable_any_basis B hB hBc b
  have hdiag : Summable (fun i : w =>
      (inner ℂ (b i) ((A + B) (b i))).re) := by
    simpa only [ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
      using hsA.add hsB
  exact isTraceClass_of_nonneg_of_summable
    (A + B) (add_nonneg hA hB) b hdiag

/-- Exact additivity of the REAL, CFC-absolute trace norm for any
pair of positive class S₁ operators, with no shared-basis premise.
In particular noncommuting positive summands are allowed. -/
theorem traceNorm_add_of_nonneg
    (A B : H →L[ℂ] H)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAc : IsTraceClass A) (hBc : IsTraceClass B) :
    traceNorm (A + B)
        (isTraceClass_add_of_nonneg A B hA hB hAc hBc) =
      traceNorm A hAc + traceNorm B hBc := by
  let hAB := isTraceClass_add_of_nonneg A B hA hB hAc hBc
  let b := hAc.choose_spec.choose
  have hsA := positive_diagonal_summable_any_basis A hA hAc b
  have hsB := positive_diagonal_summable_any_basis B hB hBc b
  change traceNorm (A + B) hAB = _
  rw [traceNorm_eq_of_hilbertBasis hAB b,
      traceNorm_eq_of_hilbertBasis hAc b,
      traceNorm_eq_of_hilbertBasis hBc b]
  simp only [CFC.abs_of_nonneg (A + B) (add_nonneg hA hB),
    CFC.abs_of_nonneg A hA, CFC.abs_of_nonneg B hB]
  calc
    (∑' i : hAc.choose,
        (inner ℂ (b i) ((A + B) (b i))).re) =
      ∑' i : hAc.choose,
        ((inner ℂ (b i) (A (b i))).re +
          (inner ℂ (b i) (B (b i))).re) := by
      apply tsum_congr
      intro i
      simp only [ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
    _ = (∑' i : hAc.choose, (inner ℂ (b i) (A (b i))).re) +
        (∑' i : hAc.choose, (inner ℂ (b i) (B (b i))).re) :=
      hsA.tsum_add hsB

#print axioms ProbabilisticTheory.positive_diagonal_summable_any_basis
#print axioms ProbabilisticTheory.isTraceClass_add_of_nonneg
#print axioms ProbabilisticTheory.traceNorm_add_of_nonneg

end ProbabilisticTheory
