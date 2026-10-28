import GegenbauerFock.HSRowBasisGeneral

/-!
# V007 — general rectangular Schatten S₂ right-ideal theorem

For arbitrary complete complex Hilbert spaces E and F, a bounded
operator T:E → ℓ² with genuinely square-summable output Riesz rows
remains Hilbert–Schmidt after bounded precomposition B:F → E.
The proof also gives the sharp norm-squared bound against the
arbitrary complete source Hilbert-basis energy of T.

Unlike a finite-dimensional matrix proof, no dimension constraint
or choice of a canonical source basis enters this statement.
-/

noncomputable section

namespace GegenbauerFock.FockEnergy

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The n-th output Riesz row of T ∘ B is the original row composed
with B, as an identity of genuinely bounded linear functionals. -/
theorem row_comp_right_eq
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (B : F →L[ℂ] E) (n : ℕ) :
    SummableRowsCompact.row (T.comp B) n =
      (SummableRowsCompact.row T n).comp B := by
  ext x
  rfl

/-- Exact row-norm estimate under arbitrary rectangular precomposition. -/
theorem row_comp_right_norm_sq_le
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (B : F →L[ℂ] E) (n : ℕ) :
    ‖SummableRowsCompact.row (T.comp B) n‖ ^ 2 ≤
      ‖B‖ ^ 2 * ‖SummableRowsCompact.row T n‖ ^ 2 := by
  rw [row_comp_right_eq T B n]
  calc
    ‖(SummableRowsCompact.row T n).comp B‖ ^ 2 ≤
        (‖SummableRowsCompact.row T n‖ * ‖B‖) ^ 2 := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖B‖ ^ 2 * ‖SummableRowsCompact.row T n‖ ^ 2 := by ring

/-- The square-summable Hilbert rows form a rectangular right ideal. -/
theorem rows_comp_right_summable
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row T n‖ ^ 2))
    (B : F →L[ℂ] E) :
    Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row (T.comp B) n‖ ^ 2) := by
  exact Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    (row_comp_right_norm_sq_le T B)
    (hrows.mul_left (‖B‖ ^ 2))

/-- The canonical row energy satisfies the square of the correct
operator-norm ideal bound, for any Hilbert spaces E and F. -/
theorem rows_comp_right_mass_le
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row T n‖ ^ 2))
    (B : F →L[ℂ] E) :
    (∑' n : ℕ, ‖SummableRowsCompact.row (T.comp B) n‖ ^ 2) ≤
      ‖B‖ ^ 2 * (∑' n : ℕ,
        ‖SummableRowsCompact.row T n‖ ^ 2) := by
  calc
    (∑' n : ℕ, ‖SummableRowsCompact.row (T.comp B) n‖ ^ 2) ≤
      ∑' n : ℕ, ‖B‖ ^ 2 * ‖SummableRowsCompact.row T n‖ ^ 2 :=
        (rows_comp_right_summable T hrows B).tsum_le_tsum
          (row_comp_right_norm_sq_le T B)
          (hrows.mul_left (‖B‖ ^ 2))
    _ = ‖B‖ ^ 2 *
      (∑' n : ℕ, ‖SummableRowsCompact.row T n‖ ^ 2) :=
        tsum_mul_left

/-- Genuine infinite-dimensional, arbitrary-source-basis Schatten
S₂ right ideal estimate. The result certifies summability of all
images of the composite operator on every complete source basis,
and gives an exact quantitative estimate relative to any other
complete source basis of T's domain. -/
theorem sourceBasis_HS_comp_right
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row T n‖ ^ 2))
    (B : F →L[ℂ] E)
    {ι : Type*} (b : HilbertBasis ι ℂ F)
    {κ : Type*} (a : HilbertBasis κ ℂ E) :
    Summable (fun i : ι => ‖(T.comp B) (b i)‖ ^ 2) ∧
      (∑' i : ι, ‖(T.comp B) (b i)‖ ^ 2) ≤
        ‖B‖ ^ 2 * (∑' j : κ, ‖T (a j)‖ ^ 2) := by
  have hc := summableRows_iff_sourceBasis_energy
    (T.comp B) (rows_comp_right_summable T hrows B) b
  constructor
  · exact hc.1
  · calc
      (∑' i : ι, ‖(T.comp B) (b i)‖ ^ 2) =
          ∑' n : ℕ,
            ‖SummableRowsCompact.row (T.comp B) n‖ ^ 2 := hc.2
      _ ≤ ‖B‖ ^ 2 *
          (∑' n : ℕ, ‖SummableRowsCompact.row T n‖ ^ 2) :=
        rows_comp_right_mass_le T hrows B
      _ = ‖B‖ ^ 2 * (∑' j : κ, ‖T (a j)‖ ^ 2) := by
        rw [← (summableRows_iff_sourceBasis_energy T hrows a).2]

#print axioms GegenbauerFock.FockEnergy.row_comp_right_eq
#print axioms GegenbauerFock.FockEnergy.row_comp_right_norm_sq_le
#print axioms GegenbauerFock.FockEnergy.rows_comp_right_summable
#print axioms GegenbauerFock.FockEnergy.rows_comp_right_mass_le
#print axioms GegenbauerFock.FockEnergy.sourceBasis_HS_comp_right

end GegenbauerFock.FockEnergy
