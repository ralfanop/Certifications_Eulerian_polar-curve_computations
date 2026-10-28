import GegenbauerFock.PhyslibHSProductTraceNormWeightedYoung
import GegenbauerFock.SchattenYoungSharpReal

/-!
# V007 — genuine CFC Schatten–Hölder inequality with sharp constant 1

For two arbitrary Hilbert–Schmidt endomorphisms R,S of a complete
complex Hilbert space and any complete Hilbert basis b, the actual
CFC-absolute trace norm satisfies
   traceNorm(R*S) ≤ √((∑ ‖R eᵢ‖²)*(∑ ‖S eᵢ‖²)).
The bound is *sharp* (constant 1), is basis independent, and needs
no finite rank, positivity, or commutativity hypotheses.

The exact proof combines an independently formalized weighted Young
inequality, trace-norm complex homogeneity, and a fully quantified
real optimization including zero-energy cases. No assumed Schatten
normed-Banach API or unverified complex functional calculus axiom.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem traceNorm_mul_twoHilbertSchmidt_le_sqrt_energy_mul
    (R S : H →L[ℂ] H)
    (hR : HilbertSchmidt.IsHilbertSchmidt R)
    (hS : HilbertSchmidt.IsHilbertSchmidt S)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    traceNorm (R * S)
      (isTraceClass_mul_of_twoHilbertSchmidt R S hR hS) ≤
      Real.sqrt
        ((∑' i : w, ‖R (b i)‖ ^ 2) *
         (∑' i : w, ‖S (b i)‖ ^ 2)) := by
  have hRnonneg : 0 ≤ (∑' i : w, ‖R (b i)‖ ^ 2) :=
    tsum_nonneg (fun i => sq_nonneg _)
  have hSnonneg : 0 ≤ (∑' i : w, ‖S (b i)‖ ^ 2) :=
    tsum_nonneg (fun i => sq_nonneg _)
  have hNnonneg :
      0 ≤ traceNorm (R * S)
        (isTraceClass_mul_of_twoHilbertSchmidt R S hR hS) :=
    traceNorm_nonneg (R * S)
      (isTraceClass_mul_of_twoHilbertSchmidt R S hR hS)
  exact GegenbauerFock.SchattenYoung.all_scales_implies_le_sqrt_mul
    hRnonneg hSnonneg hNnonneg
    (fun t ht =>
      weighted_young_traceNorm_mul_twoHilbertSchmidt R S hR hS b t ht)

#print axioms ProbabilisticTheory.traceNorm_mul_twoHilbertSchmidt_le_sqrt_energy_mul

end ProbabilisticTheory
