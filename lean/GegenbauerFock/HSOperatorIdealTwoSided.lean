import GegenbauerFock.HSRowBasisGeneral
import GegenbauerFock.PositiveNuclearConjugation

/-!
# V007: genuine infinite-dimensional two-sided S₂ ideal laws

For arbitrary bounded maps T : L²(μ) → ℓ² and any two bounded
pre/postprocessing maps B and A, canonical row-square-summability
implies actual summability of ||A ◦ T ◦ B (e_i)||² over EVERY
complete source Hilbert basis (e_i).

This is a genuinely abstract two-sided Hilbert–Schmidt *membership*
theorem for Fock-codomain maps, rather than a statement only about
the single ultraspherical C. It does not falsely assert that a
bundled universal Schatten ideal normed Banach object has been ported.
-/

noncomputable section

namespace GegenbauerFock.FockEnergy

open MeasureTheory

/-- Exact transfer from the source-independent canonical ℓ²
row summability criterion to the full basis-defined S₂ class. -/
theorem summableRows_to_IsHS
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (T : Lp ℂ 2 μ →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : HasSummableRows μ T) :
    HilbertSchmidtBasis.IsHS T := by
  intro ι b
  have hrow :
      Summable (fun n : ℕ =>
        ‖SummableRowsCompact.row T n‖ ^ 2) := hrows
  exact (summableRows_iff_sourceBasis_energy T hrow b).1

/-- Right-ideal closure: arbitrary bounded source precomposition
preserves genuine Hilbert–Schmidt summability on all complete bases. -/
theorem summableRows_right_IsHS
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (T : Lp ℂ 2 μ →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : HasSummableRows μ T)
    (B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    HilbertSchmidtBasis.IsHS (T.comp B) :=
  summableRows_to_IsHS μ (T.comp B)
    (summableRows_comp_right μ T hrows B)

/-- Two-sided S₂ ideal stability for a source Hilbert L² and
*any* complete complex Hilbert output G. Here no particular
ultraspherical measure or Fock coefficient formula is used. -/
theorem summableRows_twoSided_IsHS
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (T : Lp ℂ 2 μ →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : HasSummableRows μ T)
    (B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : InfiniteAnalysis.FockCoefficients →L[ℂ] G) :
    HilbertSchmidtBasis.IsHS (A.comp (T.comp B)) :=
  HilbertSchmidtBasis.isHS_comp_left (T.comp B)
    (summableRows_right_IsHS μ T hrows B) A


/-- Quantitative RIGHT-ideal Schatten-S₂ energy inequality on
ANY complete Hilbert source basis, with exact original canonical
row energy as the constant. -/
theorem summableRows_right_basis_energy_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (T : Lp ℂ 2 μ →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : HasSummableRows μ T)
    (B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) :
    (∑' i : ι, ‖(T.comp B) (b i)‖ ^ 2) ≤
      ‖B‖ ^ 2 * (∑' n : ℕ,
        ‖SummableRowsCompact.row T n‖ ^ 2) := by
  have hTB : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row (T.comp B) n‖ ^ 2) := by
    exact (summableRows_comp_right μ T hrows B)
  have hbound (n : ℕ) :
      ‖SummableRowsCompact.row (T.comp B) n‖ ^ 2 ≤
        ‖B‖ ^ 2 * ‖SummableRowsCompact.row T n‖ ^ 2 := by
    change ‖((FockEnergy.coordinate n).comp (T.comp B))‖ ^ 2 ≤ _
    exact row_comp_right_norm_sq_le μ T B n
  calc
    (∑' i : ι, ‖(T.comp B) (b i)‖ ^ 2) =
        ∑' n : ℕ,
          ‖SummableRowsCompact.row (T.comp B) n‖ ^ 2 :=
      (summableRows_iff_sourceBasis_energy (T.comp B) hTB b).2
    _ ≤ ∑' n : ℕ,
        ‖B‖ ^ 2 * ‖SummableRowsCompact.row T n‖ ^ 2 := by
          apply hTB.tsum_le_tsum hbound
          exact hrows.mul_left (‖B‖ ^ 2)
    _ = ‖B‖ ^ 2 *
        (∑' n : ℕ, ‖SummableRowsCompact.row T n‖ ^ 2) := tsum_mul_left

/-- Quantitative TWO-SIDED S₂ ideal bound with arbitrary bounded
left and right factors and a complete Hilbert source basis.
The target of A may be any complete complex Hilbert space. -/
theorem summableRows_twoSided_basis_energy_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (T : Lp ℂ 2 μ →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : HasSummableRows μ T)
    (B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : InfiniteAnalysis.FockCoefficients →L[ℂ] G)
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) :
    (∑' i : ι, ‖(A.comp (T.comp B)) (b i)‖ ^ 2) ≤
      ‖A‖ ^ 2 * ‖B‖ ^ 2 *
        (∑' n : ℕ, ‖SummableRowsCompact.row T n‖ ^ 2) := by
  have hTB : Summable (fun i : ι => ‖(T.comp B) (b i)‖ ^ 2) :=
    (summableRows_iff_sourceBasis_energy (T.comp B)
      (summableRows_comp_right μ T hrows B) b).1
  have hpoint (i : ι) :
      ‖(A.comp (T.comp B)) (b i)‖ ^ 2 ≤
        ‖A‖ ^ 2 * ‖(T.comp B) (b i)‖ ^ 2 := by
    change ‖A ((T.comp B) (b i))‖ ^ 2 ≤ _
    calc
      ‖A ((T.comp B) (b i))‖ ^ 2 ≤
          (‖A‖ * ‖(T.comp B) (b i)‖) ^ 2 := by
            gcongr
            exact ContinuousLinearMap.le_opNorm A ((T.comp B) (b i))
      _ = ‖A‖ ^ 2 * ‖(T.comp B) (b i)‖ ^ 2 := by ring
  have hATB : Summable (fun i : ι =>
      ‖(A.comp (T.comp B)) (b i)‖ ^ 2) := by
    apply Summable.of_nonneg_of_le
    · intro i
      exact sq_nonneg _
    · intro i
      exact hpoint i
    · exact hTB.mul_left (‖A‖ ^ 2)
  calc
    (∑' i : ι, ‖(A.comp (T.comp B)) (b i)‖ ^ 2) ≤
        ‖A‖ ^ 2 * ∑' i : ι, ‖(T.comp B) (b i)‖ ^ 2 := by
          calc
            (∑' i : ι, ‖(A.comp (T.comp B)) (b i)‖ ^ 2) ≤
                ∑' i : ι, ‖A‖ ^ 2 * ‖(T.comp B) (b i)‖ ^ 2 :=
              hATB.tsum_le_tsum hpoint (hTB.mul_left (‖A‖ ^ 2))
            _ = ‖A‖ ^ 2 * ∑' i : ι, ‖(T.comp B) (b i)‖ ^ 2 :=
              tsum_mul_left
    _ ≤ ‖A‖ ^ 2 * (‖B‖ ^ 2 *
        (∑' n : ℕ, ‖SummableRowsCompact.row T n‖ ^ 2)) := by
          gcongr
          exact summableRows_right_basis_energy_le μ T hrows B b
    _ = ‖A‖ ^ 2 * ‖B‖ ^ 2 *
        (∑' n : ℕ, ‖SummableRowsCompact.row T n‖ ^ 2) := by ring

#print axioms GegenbauerFock.FockEnergy.summableRows_right_basis_energy_le
#print axioms GegenbauerFock.FockEnergy.summableRows_twoSided_basis_energy_le

#print axioms GegenbauerFock.FockEnergy.summableRows_to_IsHS
#print axioms GegenbauerFock.FockEnergy.summableRows_right_IsHS
#print axioms GegenbauerFock.FockEnergy.summableRows_twoSided_IsHS

end GegenbauerFock.FockEnergy
