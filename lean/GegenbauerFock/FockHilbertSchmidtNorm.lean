import GegenbauerFock.HSOperatorIdealTwoSided

/-!
# V007: basis-independent Hilbert–Schmidt norm for Fock-target maps

For an arbitrary complete complex Hilbert source E, any bounded map
T : E → ℓ² with summable canonical coordinate-row norms has a genuine
finite S₂ norm. The value is identified with the norm computed on
*every* complete Hilbert basis of the source.

This is not a finite-dimensional surrogate and does not assume a
basis-invariant norm as an axiom. The row/source-basis equality used
below was certified independently by Parseval and a nonnegative
double-series Fubini argument.
-/

noncomputable section

namespace GegenbauerFock.FockEnergy

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The genuine Hilbert–Schmidt norm of a row-summable bounded map into
the infinite Fock coefficient Hilbert space. The summability witness
is explicit: the value is never used to assign a fictitious Schatten
norm to a non-Hilbert–Schmidt operator. -/
noncomputable def s2Norm
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (_hrows : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row T n‖ ^ 2)) : ℝ :=
  Real.sqrt (∑' n : ℕ, ‖SummableRowsCompact.row T n‖ ^ 2)

/-- Positivity of the actual Hilbert–Schmidt norm. -/
theorem s2Norm_nonneg
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row T n‖ ^ 2)) :
    0 ≤ s2Norm T hrows := by
  exact Real.sqrt_nonneg _

/-- Its square is the complete infinite-dimensional row energy. -/
theorem s2Norm_sq_eq_rowEnergy
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row T n‖ ^ 2)) :
    (s2Norm T hrows) ^ 2 =
      ∑' n : ℕ, ‖SummableRowsCompact.row T n‖ ^ 2 := by
  unfold s2Norm
  exact Real.sq_sqrt (tsum_nonneg fun n => sq_nonneg _)

/-- On EVERY complete Hilbert basis of the input Hilbert space,
the canonical S₂ norm is the square root of the basis energy. -/
theorem s2Norm_eq_sourceBasis
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row T n‖ ^ 2))
    {ι : Type*} (b : HilbertBasis ι ℂ E) :
    s2Norm T hrows =
      Real.sqrt (∑' i : ι, ‖T (b i)‖ ^ 2) := by
  unfold s2Norm
  rw [(summableRows_iff_sourceBasis_energy T hrows b).2]

/-- Invariance of the genuine Hilbert–Schmidt squared norm under
two arbitrarily indexed complete input Hilbert bases. -/
theorem s2BasisEnergy_independent
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row T n‖ ^ 2))
    {ι κ : Type*} (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E) :
    (∑' i : ι, ‖T (b i)‖ ^ 2) =
      ∑' j : κ, ‖T (c j)‖ ^ 2 := by
  exact (summableRows_iff_sourceBasis_energy T hrows b).2.trans
    (summableRows_iff_sourceBasis_energy T hrows c).2.symm

#print axioms GegenbauerFock.FockEnergy.s2Norm_nonneg
#print axioms GegenbauerFock.FockEnergy.s2Norm_sq_eq_rowEnergy
#print axioms GegenbauerFock.FockEnergy.s2Norm_eq_sourceBasis
#print axioms GegenbauerFock.FockEnergy.s2BasisEnergy_independent

end GegenbauerFock.FockEnergy
