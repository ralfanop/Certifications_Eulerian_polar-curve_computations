import GegenbauerFock.PhyslibHSProductTraceNormHalfSumBound
import GegenbauerFock.PhyslibTraceNormHomogeneity

/-!
# V007 — weighted Schatten–Young inequality in the genuine CFC norm

For any real t > 0, arbitrary S₂ endomorphisms R,S, and any
complete Hilbert basis b, the true CFC trace norm obeys:
  2 t traceNorm(R*S) ≤ t² ∑ᵢ ‖R eᵢ‖² + ∑ᵢ ‖S eᵢ‖².

This is obtained by applying the exact coefficient-2 unweighted
inequality to ((t:ℂ)•R)*S, then using the true trace-norm homogeneity
and the exact scalar Hilbert–Schmidt diagonal energy. Proofs of
operator equalities are not assumptions.

The real optimization of all t is performed in
SchattenYoungSharpReal. No claim about full S₁ Banach completeness.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem weighted_young_traceNorm_mul_twoHilbertSchmidt
    (R S : H →L[ℂ] H)
    (hR : HilbertSchmidt.IsHilbertSchmidt R)
    (hS : HilbertSchmidt.IsHilbertSchmidt S)
    {w : Set H} (b : HilbertBasis w ℂ H)
    (t : ℝ) (ht : 0 < t) :
    2 * t * traceNorm (R * S)
      (isTraceClass_mul_of_twoHilbertSchmidt R S hR hS) ≤
      t ^ 2 * (∑' i : w, ‖R (b i)‖ ^ 2) +
      (∑' i : w, ‖S (b i)‖ ^ 2) := by
  let c : ℂ := (t : ℂ)
  let hRS : IsTraceClass (R * S) :=
    isTraceClass_mul_of_twoHilbertSchmidt R S hR hS
  have hc : ‖c‖ = t := by
    simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hRt : HilbertSchmidt.IsHilbertSchmidt (c • R) :=
    HilbertSchmidt.isHilbertSchmidt_smul c hR
  let hcRS : IsTraceClass ((c • R) * S) :=
    isTraceClass_mul_of_twoHilbertSchmidt (c • R) S hRt hS
  have hprod : (c • R) * S = c • (R * S) :=
    smul_mul_assoc c R S
  have htr :
      traceNorm ((c • R) * S) hcRS =
        t * traceNorm (R * S) hRS := by
    calc
      traceNorm ((c • R) * S) hcRS =
        traceNorm (c • (R * S)) (isTraceClass_smul c hRS) := by
          rw [hprod]
          exact traceNorm_congr
      _ = ‖c‖ * traceNorm (R * S) hRS :=
        traceNorm_smul c hRS
      _ = t * traceNorm (R * S) hRS := by rw [hc]
  have hterm (i : w) :
      ‖(c • R) (b i)‖ ^ 2 = t ^ 2 * ‖R (b i)‖ ^ 2 := by
    rw [smul_apply, norm_smul, hc]
    ring
  have henergy :
      (∑' i : w, ‖(c • R) (b i)‖ ^ 2) =
        t ^ 2 * (∑' i : w, ‖R (b i)‖ ^ 2) := by
    calc
      (∑' i : w, ‖(c • R) (b i)‖ ^ 2) =
        ∑' i : w, t ^ 2 * ‖R (b i)‖ ^ 2 := tsum_congr hterm
      _ = t ^ 2 * (∑' i : w, ‖R (b i)‖ ^ 2) :=
        tsum_mul_left
  have hsum :=
    two_mul_traceNorm_mul_twoHilbertSchmidt_le_energy_sum
      (c • R) S hRt hS b
  rw [htr, henergy] at hsum
  nlinarith

#print axioms ProbabilisticTheory.weighted_young_traceNorm_mul_twoHilbertSchmidt

end ProbabilisticTheory
