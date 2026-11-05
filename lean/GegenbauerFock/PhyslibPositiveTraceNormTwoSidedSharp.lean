import GegenbauerFock.PhyslibHSProductTraceNormHolder
import GegenbauerFock.PhyslibTraceNormSqrtAbsEnergy
import GegenbauerFock.PhyslibTraceClassTwoSidedIdeal
import GegenbauerFock.PhyslibHSRightBasisEnergyBound

/-!
# V007 — general sharp two-sided Schatten S₁ ideal bound for positive T

The source-compatible Physlib genuine CFC-absolute trace norm obeys
  traceNorm (A*T*B) ≤ ‖A‖*‖B‖*traceNorm T
for all bounded operators A,B and positive trace-class T on an
arbitrary complete complex Hilbert space.

The kernel proof factors T=sqrt(T)*sqrt(T), proves both factors
genuinely Hilbert–Schmidt, and applies the already independently
certified *sharp* Schatten–Hölder inequality to (A*sqrt T)*(sqrt T*B).

This is a new generic proof, with a separate exact-SHA CI. It
requires neither a finite-rank model nor full trace-class Banach
completeness, and includes zero operators and noncommuting A,B.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positive_traceNorm_twoSided_le_sharp
    (T : H →L[ℂ] H) (hpos : 0 ≤ T) (hT : IsTraceClass T)
    (A B : H →L[ℂ] H) :
    traceNorm (A * T * B)
        (isTraceClass_twoSided T hT A B) ≤
      ‖A‖ * ‖B‖ * traceNorm T hT := by
  let Q : H →L[ℂ] H := CFC.sqrt T
  have hQQ : Q * Q = T := CFC.sqrt_mul_sqrt_self T hpos
  have hQ : HilbertSchmidt.IsHilbertSchmidt Q := by
    change HilbertSchmidt.IsHilbertSchmidt (CFC.sqrt T)
    simpa only [CFC.abs_of_nonneg T hpos] using
      traceClass_sqrt_abs_isHS T hT
  have hAQ : HilbertSchmidt.IsHilbertSchmidt (A * Q) := by
    change HilbertSchmidt.IsHilbertSchmidt (A.comp Q)
    exact HilbertSchmidt.isHilbertSchmidt_comp_left Q hQ A
  have hQB : HilbertSchmidt.IsHilbertSchmidt (Q * B) := by
    change HilbertSchmidt.IsHilbertSchmidt (Q.comp B)
    exact HilbertSchmidt.isHilbertSchmidt_comp_right Q hQ B
  have hfactor : (A * Q) * (Q * B) = A * T * B := by
    calc
      (A * Q) * (Q * B) = A * (Q * Q) * B := by simp only [mul_assoc]
      _ = A * T * B := by rw [hQQ]
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hQsum : Summable (fun i : w => ‖Q (b i)‖ ^ 2) :=
    HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hQ
  have hAQsum : Summable (fun i : w => ‖(A * Q) (b i)‖ ^ 2) :=
    HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hAQ
  have hQtrace : traceNorm T hT = (∑' i : w, ‖Q (b i)‖ ^ 2) := by
    have h := traceNorm_eq_sqrt_abs_basisEnergy T hT b
    simpa only [CFC.abs_of_nonneg T hpos] using h
  let eQ : ℝ := ∑' i : w, ‖Q (b i)‖ ^ 2
  let eAQ : ℝ := ∑' i : w, ‖(A * Q) (b i)‖ ^ 2
  let eQB : ℝ := ∑' i : w, ‖(Q * B) (b i)‖ ^ 2
  have heQ : 0 ≤ eQ := tsum_nonneg (fun i => sq_nonneg _)
  have heAQ : 0 ≤ eAQ := tsum_nonneg (fun i => sq_nonneg _)
  have heQB : 0 ≤ eQB := tsum_nonneg (fun i => sq_nonneg _)
  have hpoint (i : w) :
      ‖(A * Q) (b i)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖Q (b i)‖ ^ 2 := by
    change ‖A (Q (b i))‖ ^ 2 ≤ _
    calc
      ‖A (Q (b i))‖ ^ 2 ≤ (‖A‖ * ‖Q (b i)‖) ^ 2 := by
        exact (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
            (ContinuousLinearMap.le_opNorm A (Q (b i)))
      _ = ‖A‖ ^ 2 * ‖Q (b i)‖ ^ 2 := by ring
  have hleft : eAQ ≤ ‖A‖ ^ 2 * eQ := by
    calc
      eAQ ≤ ∑' i : w, ‖A‖ ^ 2 * ‖Q (b i)‖ ^ 2 :=
        hAQsum.tsum_le_tsum hpoint (hQsum.mul_left (‖A‖ ^ 2))
      _ = ‖A‖ ^ 2 * eQ := tsum_mul_left
  have hright : eQB ≤ ‖B‖ ^ 2 * eQ :=
    HilbertSchmidt.right_basis_energy_le Q hQ B b
  have hprod : eAQ * eQB ≤ (‖A‖ * ‖B‖ * eQ) ^ 2 := by
    calc
      eAQ * eQB ≤ (‖A‖ ^ 2 * eQ) * (‖B‖ ^ 2 * eQ) :=
        mul_le_mul hleft hright heQB (mul_nonneg (sq_nonneg _) heQ)
      _ = (‖A‖ * ‖B‖ * eQ) ^ 2 := by ring
  have hroot : Real.sqrt (eAQ * eQB) ≤ ‖A‖ * ‖B‖ * eQ := by
    have hsq := Real.sq_sqrt (mul_nonneg heAQ heQB)
    have hrootpos := Real.sqrt_nonneg (eAQ * eQB)
    have hrhs : 0 ≤ ‖A‖ * ‖B‖ * eQ := by positivity
    nlinarith
  have htrace :
      traceNorm (A * T * B) (isTraceClass_twoSided T hT A B) =
      traceNorm ((A * Q) * (Q * B))
        (isTraceClass_mul_of_twoHilbertSchmidt (A * Q) (Q * B) hAQ hQB) := by
    rw [traceNorm_eq_of_hilbertBasis (isTraceClass_twoSided T hT A B) b,
      traceNorm_eq_of_hilbertBasis
        (isTraceClass_mul_of_twoHilbertSchmidt (A * Q) (Q * B) hAQ hQB) b,
      ← hfactor]
  calc
    traceNorm (A * T * B) (isTraceClass_twoSided T hT A B) =
        traceNorm ((A * Q) * (Q * B))
          (isTraceClass_mul_of_twoHilbertSchmidt (A * Q) (Q * B) hAQ hQB) :=
      htrace
    _ ≤ Real.sqrt (eAQ * eQB) :=
      traceNorm_mul_twoHilbertSchmidt_le_sqrt_energy_mul (A * Q) (Q * B) hAQ hQB b
    _ ≤ ‖A‖ * ‖B‖ * eQ := hroot
    _ = ‖A‖ * ‖B‖ * traceNorm T hT := by rw [hQtrace]

#print axioms ProbabilisticTheory.positive_traceNorm_twoSided_le_sharp

end ProbabilisticTheory
