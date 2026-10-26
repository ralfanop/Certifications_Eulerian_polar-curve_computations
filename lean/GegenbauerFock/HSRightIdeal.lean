import GegenbauerFock.ConcreteFockEnergy

/-!
# V007: genuine right ideal stability of square-summable Fock Hilbert rows

For operators into the concrete complete target ℓ², the canonical
coefficient Hilbert-Schmidt energy is the sum of the squared norms
of its Riesz row functionals. Composition on the source side by any
bounded map preserves summability and gives the exact norm-ideal
inequality for the row energy. The two-sided/basis-independent
Hilbert-Schmidt ideal identification is a further step.
-/

open MeasureTheory

namespace GegenbauerFock.FockEnergy

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- For an operator with ℓ² codomain, precomposition by an arbitrary
bounded endomorphism cannot increase the n-th row norm by more than
the operator norm of that endomorphism. -/
theorem row_comp_right_norm_sq_le
    (T : Lp ℂ 2 μ →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (n : ℕ) :
    ‖(coordinate n).comp (T.comp B)‖ ^ 2 ≤
      ‖B‖ ^ 2 * ‖(coordinate n).comp T‖ ^ 2 := by
  have heq :
      (coordinate n).comp (T.comp B) =
        ((coordinate n).comp T).comp B := by
    ext f
    rfl
  rw [heq]
  calc
    ‖((coordinate n).comp T).comp B‖ ^ 2 ≤
        (‖(coordinate n).comp T‖ * ‖B‖) ^ 2 := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖B‖ ^ 2 * ‖(coordinate n).comp T‖ ^ 2 := by ring

/-- Source-side ideal theorem for actual summable Fock Hilbert rows,
valid in the full infinite-dimensional Hilbert space. -/
theorem summableRows_comp_right
    (T : Lp ℂ 2 μ →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hT : HasSummableRows μ T)
    (B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    HasSummableRows μ (T.comp B) := by
  unfold HasSummableRows at hT ⊢
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    (row_comp_right_norm_sq_le μ T B)
    (hT.mul_left (‖B‖ ^ 2))

#print axioms GegenbauerFock.FockEnergy.row_comp_right_norm_sq_le
#print axioms GegenbauerFock.FockEnergy.summableRows_comp_right

end GegenbauerFock.FockEnergy
