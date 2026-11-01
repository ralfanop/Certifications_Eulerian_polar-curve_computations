import GegenbauerFock.RectangularHSAdjointTrace
import GegenbauerFock.GramNuclearTrace

/-!
# V007 — exact Hilbert–Schmidt norm of the genuine Gegenbauer–Fock adjoint

Let C_{λ,α} : L²(ν_λ) → ℓ² be the fully constructed Gegenbauer–Fock map.
For *every* complete Hilbert basis of its ℓ² target, the actual adjoint
C† has a summable squared-image-norm series, and its sum is exactly the
unregularized Kummer value for λ,α>0.

This statement is distinct from S₁ membership of either Gram: it
specifies the Hilbert–Schmidt energy and norm of the RECTANGULAR adjoint
itself, independently of the chosen Fock-domain Hilbert basis.

The proof uses certified rectangular-adjoint Parseval/Tonelli and the
certified arbitrary-source-basis Kummer energy identity. No new axioms.
Candidate until exact-SHA Lean compilation and explicit axiom audit.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- The genuine Fock-to-L² adjoint has complete Hilbert–Schmidt
summability over any full Fock Hilbert basis, not just its coordinates. -/
theorem C_adjoint_any_Fock_basis_HSEnergy_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {κ : Type*}
    (b : HilbertBasis κ ℂ InfiniteAnalysis.FockCoefficients) :
    Summable (fun j : κ => ‖C_adjoint lam alpha hlam ha (b j)‖ ^ 2) := by
  let E := Lp ℂ 2 (Ultraspherical.measure lam)
  obtain ⟨w, a, _⟩ := exists_hilbertBasis ℂ E
  have hT : Summable (fun i : w =>
      ‖C lam alpha hlam ha (a i)‖ ^ 2) :=
    C_isHilbertSchmidt lam alpha hlam ha a
  have hstar := (HilbertSchmidtBasis.hasSum_adjoint_energy_rectangular
    (C lam alpha hlam ha) a b hT).summable
  simpa only [C_adjoint] using hstar

/-- The squared S₂ energy of the ACTUAL C†, computed on any
complete Fock basis, equals the exact Kummer sum. -/
theorem C_adjoint_any_Fock_basis_HSEnergy_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {κ : Type*}
    (b : HilbertBasis κ ℂ InfiniteAnalysis.FockCoefficients) :
    (∑' j : κ, ‖C_adjoint lam alpha hlam ha (b j)‖ ^ 2) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  let E := Lp ℂ 2 (Ultraspherical.measure lam)
  obtain ⟨w, a, _⟩ := exists_hilbertBasis ℂ E
  have hT : Summable (fun i : w =>
      ‖C lam alpha hlam ha (a i)‖ ^ 2) :=
    C_isHilbertSchmidt lam alpha hlam ha a
  have hrect := (HilbertSchmidtBasis.hasSum_adjoint_energy_rectangular
    (C lam alpha hlam ha) a b hT).tsum_eq
  calc
    (∑' j : κ, ‖C_adjoint lam alpha hlam ha (b j)‖ ^ 2) =
        ∑' i : w, ‖C lam alpha hlam ha (a i)‖ ^ 2 := by
          simpa only [C_adjoint] using hrect
    _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
      C_sourceBasis_HSEnergy_eq_kummer lam alpha hlam ha a

/-- The genuine rectangular adjoint has exact S₂ norm
sqrt(₁F₁(1/2;λ+1;1/(4α))), in ANY Fock basis. -/
theorem C_adjoint_any_Fock_basis_HSNorm_eq_sqrt_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {κ : Type*}
    (b : HilbertBasis κ ℂ InfiniteAnalysis.FockCoefficients) :
    HilbertSchmidtBasis.basisNorm (C_adjoint lam alpha hlam ha) b =
      Real.sqrt (KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) := by
  unfold HilbertSchmidtBasis.basisNorm
  rw [C_adjoint_any_Fock_basis_HSEnergy_eq_kummer lam alpha hlam ha b]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_any_Fock_basis_HSEnergy_summable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_any_Fock_basis_HSEnergy_eq_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_any_Fock_basis_HSNorm_eq_sqrt_kummer

end GegenbauerFock.GeneralUltrasphericalFock
