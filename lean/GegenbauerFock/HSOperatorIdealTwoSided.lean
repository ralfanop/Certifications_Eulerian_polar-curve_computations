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

#print axioms GegenbauerFock.FockEnergy.summableRows_to_IsHS
#print axioms GegenbauerFock.FockEnergy.summableRows_right_IsHS
#print axioms GegenbauerFock.FockEnergy.summableRows_twoSided_IsHS

end GegenbauerFock.FockEnergy
