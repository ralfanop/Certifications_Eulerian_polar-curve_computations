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

/-- Source-side ideal bound also for a different probability L² space.
The source of B need not coincide with the source of T. -/
theorem row_comp_right_norm_sq_between
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : Lp ℂ 2 μ →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) (n : ℕ) :
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

/-- The row-summable operator property is stable under arbitrary
bounded precomposition between two possibly different probability L² spaces. -/
theorem summableRows_comp_right_between
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : Lp ℂ 2 μ →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hT : HasSummableRows μ T)
    (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) :
    HasSummableRows ν (T.comp B) := by
  unfold HasSummableRows at hT ⊢
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    (row_comp_right_norm_sq_between μ ν T B)
    (hT.mul_left (‖B‖ ^ 2))

#print axioms GegenbauerFock.FockEnergy.row_comp_right_norm_sq_between
#print axioms GegenbauerFock.FockEnergy.summableRows_comp_right_between

#print axioms GegenbauerFock.FockEnergy.row_comp_right_norm_sq_le
#print axioms GegenbauerFock.FockEnergy.summableRows_comp_right

/-- Parseval's exact squared-norm identity for *any* Hilbert basis
of a complex Hilbert space. This is the basis-independent analytical
ingredient needed to promote canonical output-row energy to a true
input-basis Hilbert--Schmidt class norm. -/
theorem hilbertBasis_parseval
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} (b : HilbertBasis ι ℂ E) (x : E) :
    (∑' i : ι, ‖inner ℂ (b i) x‖ ^ 2) = ‖x‖ ^ 2 := by
  calc
    (∑' i : ι, ‖inner ℂ (b i) x‖ ^ 2) =
        ∑' i : ι, ‖(b.repr x) i‖ ^ 2 := by
          apply tsum_congr
          intro i
          rw [HilbertBasis.repr_apply_apply]
    _ = ‖b.repr x‖ ^ 2 := by
          simpa using (lp.norm_rpow_eq_tsum
            (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
            (b.repr x)).symm
    _ = ‖x‖ ^ 2 := by rw [b.repr.norm_map]

#print axioms GegenbauerFock.FockEnergy.hilbertBasis_parseval

/-- The squared-norm sum over ANY complete complex Hilbert basis
of the source space of a concrete weighted moment functional equals
the squared operator norm of that functional.  This is a
basis-independent Riesz/Parseval theorem for each individual
Gegenbauer--Fock row (the double-series interchange is separate). -/
theorem weightedMoment_row_basis_energy
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupport : ∀ᵐ u ∂μ, |u| ≤ (1 : ℝ))
    (alpha : ℝ) (ha : 0 < alpha)
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (n : ℕ) :
    (∑' i : ι,
      ‖WeightedMoments.coefficient μ hsupport alpha n (b i)‖ ^ 2) =
      ‖WeightedMoments.coefficient μ hsupport alpha n‖ ^ 2 := by
  let m := WeightedMoments.monomial μ hsupport n
  let cw := WeightedMoments.complexWeight alpha n
  have ht (i : ι) :
      ‖WeightedMoments.coefficient μ hsupport alpha n (b i)‖ ^ 2 =
        ‖cw‖ ^ 2 * ‖inner ℂ (b i) m‖ ^ 2 := by
    change ‖cw * inner ℂ m (b i)‖ ^ 2 = _
    rw [norm_mul, mul_pow, norm_inner_symm]
  calc
    (∑' i : ι, ‖WeightedMoments.coefficient μ hsupport alpha n (b i)‖ ^ 2) =
        ∑' i : ι, ‖cw‖ ^ 2 * ‖inner ℂ (b i) m‖ ^ 2 := by
          apply tsum_congr
          intro i
          exact ht i
    _ = ‖cw‖ ^ 2 * (∑' i : ι, ‖inner ℂ (b i) m‖ ^ 2) := by
          rw [tsum_mul_left]
    _ = ‖cw‖ ^ 2 * ‖m‖ ^ 2 := by
          rw [hilbertBasis_parseval b m]
    _ = ‖WeightedMoments.coefficient μ hsupport alpha n‖ ^ 2 := by
          change ‖WeightedMoments.complexWeight alpha n‖ ^ 2 *
              ‖WeightedMoments.monomial μ hsupport n‖ ^ 2 = _
          rw [WeightedMoments.complexWeight_norm_sq alpha ha n,
            ← coefficient_energy_exact μ hsupport alpha ha n]

#print axioms GegenbauerFock.FockEnergy.weightedMoment_row_basis_energy

end GegenbauerFock.FockEnergy
