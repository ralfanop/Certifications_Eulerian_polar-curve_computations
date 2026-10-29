import GegenbauerFock.PhyslibTraceBasisIndependence

/-!
# V007 — basis-independent positive trace diagonal and spectral summability bridge

For a genuinely CFC trace-class positive operator on an arbitrary complete
complex Hilbert space, the diagonal in EVERY Hilbert basis is absolutely
summable and its sum is the genuine trace norm.

If the diagonal of a chosen complete Hilbert basis is identified with a
real eigenvalue function (as happens for an orthonormal eigenbasis), that
function is summable and its sum equals the true trace norm.

This does not assume or prove that a particular compact Gram admits the
required complete eigenbasis; that spectral realization is a separate
obligation. No finite-dimensional approximation is used.
-/

noncomputable section

namespace GegenbauerFock.HilbertSchmidtBasis

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The diagonal of every positive, truly trace-class bounded operator
is summable in any complete complex Hilbert basis. -/
theorem positiveTrace_diagonal_summable
    (T : H →L[ℂ] H) (hT : ProbabilisticTheory.IsTraceClass T)
    (hpos : 0 ≤ T) {w : Type*} (b : HilbertBasis w ℂ H) :
    Summable (fun i : w => (inner ℂ (b i) (T (b i))).re) := by
  simpa only [CFC.abs_of_nonneg T hpos] using
    (ProbabilisticTheory.summable_inner_abs_of_hilbertBasis hT b)

/-- The basis-independent genuine trace norm equals the positive diagonal
sum in every Hilbert basis, without selecting a preferred basis. -/
theorem positiveTrace_traceNorm_eq_diagonal_tsum
    (T : H →L[ℂ] H) (hT : ProbabilisticTheory.IsTraceClass T)
    (hpos : 0 ≤ T) {w : Type*} (b : HilbertBasis w ℂ H) :
    ProbabilisticTheory.traceNorm T hT =
      ∑' i : w, (inner ℂ (b i) (T (b i))).re := by
  simpa only [CFC.abs_of_nonneg T hpos] using
    (ProbabilisticTheory.traceNorm_eq_of_hilbertBasis hT b)

/-- A real spectral diagonal identified with the diagonal of an
orthonormal Hilbert basis is necessarily summable. The diagonal
identification is an explicit hypothesis, not an assumed theorem. -/
theorem positiveTrace_diagonalValues_summable
    (T : H →L[ℂ] H) (hT : ProbabilisticTheory.IsTraceClass T)
    (hpos : 0 ≤ T) {w : Type*} (b : HilbertBasis w ℂ H)
    (values : w → ℝ)
    (hvalues : ∀ i : w,
      (inner ℂ (b i) (T (b i))).re = values i) :
    Summable values :=
  (positiveTrace_diagonal_summable T hT hpos b).congr hvalues

/-- The true trace norm is the sum of any identified real spectral
diagonal. Instantiating this for the Gram's complete eigenbasis is
the remaining unconditional eigenvalue-enumeration step. -/
theorem positiveTrace_diagonalValues_tsum_eq_traceNorm
    (T : H →L[ℂ] H) (hT : ProbabilisticTheory.IsTraceClass T)
    (hpos : 0 ≤ T) {w : Type*} (b : HilbertBasis w ℂ H)
    (values : w → ℝ)
    (hvalues : ∀ i : w,
      (inner ℂ (b i) (T (b i))).re = values i) :
    (∑' i : w, values i) = ProbabilisticTheory.traceNorm T hT := by
  calc
    (∑' i : w, values i) =
      (∑' i : w, (inner ℂ (b i) (T (b i))).re) := by
        apply tsum_congr
        intro i
        exact (hvalues i).symm
    _ = ProbabilisticTheory.traceNorm T hT :=
      (positiveTrace_traceNorm_eq_diagonal_tsum T hT hpos b).symm

#print axioms GegenbauerFock.HilbertSchmidtBasis.positiveTrace_diagonal_summable
#print axioms GegenbauerFock.HilbertSchmidtBasis.positiveTrace_traceNorm_eq_diagonal_tsum
#print axioms GegenbauerFock.HilbertSchmidtBasis.positiveTrace_diagonalValues_summable
#print axioms GegenbauerFock.HilbertSchmidtBasis.positiveTrace_diagonalValues_tsum_eq_traceNorm

end GegenbauerFock.HilbertSchmidtBasis
