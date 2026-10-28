import GegenbauerFock.PhyslibHSProductTraceNormEnergy
import GegenbauerFock.PhyslibHSRightBasisEnergyBound

/-!
# V007 — quantitative trace norm of a general S₂ product

Combines the CFC-polar trace diagonal estimate with the sharp
Hilbert–Schmidt right-ideal energy inequality and the Parseval
basis-transfer of adjoint energy.

For arbitrary Hilbert–Schmidt R,S and arbitrary complete Hilbert
basis b, the genuine CFC trace norm of R*S is no more than the
sum of their squared S₂ energies. This is a NONOPTIMAL intermediate
estimate; the sharp Hölder bound uses their geometric mean.

No positivity, finite-dimensionality, assumed trace-class norm
axioms, toolchain changes or admitted results.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An unconditional quantitative bound for the true CFC trace norm
of a general product of Hilbert–Schmidt endomorphisms. -/
theorem traceNorm_mul_twoHilbertSchmidt_le_energy_sum
    (R S : H →L[ℂ] H)
    (hR : HilbertSchmidt.IsHilbertSchmidt R)
    (hS : HilbertSchmidt.IsHilbertSchmidt S)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    traceNorm (R * S) (isTraceClass_mul_of_twoHilbertSchmidt R S hR hS) ≤
      (∑' i : w, ‖R (b i)‖ ^ 2) +
      (∑' i : w, ‖S (b i)‖ ^ 2) := by
  let U : H →L[ℂ] H := Polar.polarFactor (R * S)
  have hbase :
      traceNorm (R * S)
        (isTraceClass_mul_of_twoHilbertSchmidt R S hR hS) ≤
      (∑' i : w, ‖(R.adjoint.comp U) (b i)‖ ^ 2) +
      (∑' i : w, ‖S (b i)‖ ^ 2) :=
    traceNorm_mul_twoHilbertSchmidt_le_polar_energy R S hR hS b
  have hadj : HilbertSchmidt.IsHilbertSchmidt R.adjoint :=
    HilbertSchmidt.isHilbertSchmidt_adjoint R hR
  have hright :
      (∑' i : w, ‖(R.adjoint.comp U) (b i)‖ ^ 2) ≤
      ‖U‖ ^ 2 * (∑' i : w, ‖R.adjoint (b i)‖ ^ 2) :=
    HilbertSchmidt.right_basis_energy_le R.adjoint hadj U b
  have hsR : Summable (fun i : w => ‖R (b i)‖ ^ 2) :=
    HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hR
  have hstar :
      (∑' i : w, ‖R.adjoint (b i)‖ ^ 2) =
        (∑' i : w, ‖R (b i)‖ ^ 2) :=
    (HilbertSchmidt.hasSum_norm_sq_apply_eq_adjoint b b hsR).tsum_eq
  have hR_nonneg : 0 ≤ ∑' i : w, ‖R (b i)‖ ^ 2 :=
    tsum_nonneg (fun i => sq_nonneg _)
  have hU : ‖U‖ ≤ 1 := Polar.polarFactor_opNorm_le (R * S)
  have hU2 : ‖U‖ ^ 2 ≤ (1 : ℝ) := by
    calc
      ‖U‖ ^ 2 ≤ (1 : ℝ) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hU
      _ = 1 := by norm_num
  calc
    traceNorm (R * S) (isTraceClass_mul_of_twoHilbertSchmidt R S hR hS) ≤
        (∑' i : w, ‖(R.adjoint.comp U) (b i)‖ ^ 2) +
        (∑' i : w, ‖S (b i)‖ ^ 2) := hbase
    _ ≤ (‖U‖ ^ 2 * (∑' i : w, ‖R.adjoint (b i)‖ ^ 2)) +
        (∑' i : w, ‖S (b i)‖ ^ 2) :=
      add_le_add_right hright _
    _ = (‖U‖ ^ 2 * (∑' i : w, ‖R (b i)‖ ^ 2)) +
        (∑' i : w, ‖S (b i)‖ ^ 2) := by rw [hstar]
    _ ≤ (∑' i : w, ‖R (b i)‖ ^ 2) +
        (∑' i : w, ‖S (b i)‖ ^ 2) := by
      have hmul :
          ‖U‖ ^ 2 * (∑' i : w, ‖R (b i)‖ ^ 2) ≤
            ∑' i : w, ‖R (b i)‖ ^ 2 := by
        calc
          ‖U‖ ^ 2 * (∑' i : w, ‖R (b i)‖ ^ 2) ≤
              1 * (∑' i : w, ‖R (b i)‖ ^ 2) :=
                mul_le_mul_of_nonneg_right hU2 hR_nonneg
          _ = (∑' i : w, ‖R (b i)‖ ^ 2) := one_mul _
      exact add_le_add_right hmul _

#print axioms ProbabilisticTheory.traceNorm_mul_twoHilbertSchmidt_le_energy_sum

end ProbabilisticTheory
