import GegenbauerFock.PhyslibHSProductTraceNormHolder
import GegenbauerFock.PhyslibTraceNormSqrtAbsEnergy
import GegenbauerFock.PhyslibMixedGramTraceClass
import GegenbauerFock.PhyslibHSRightBasisEnergyBound

/-!
# V007 — sharp bilateral CFC trace-norm bound for ultraspherical Gram

For the actual bounded Gegenbauer–Fock Gram G=C†C, and arbitrary
bounded source operators A and B, this module targets the sharp
two-sided Schatten trace ideal inequality

 traceNorm(A*G*B) ≤ ‖A‖ ‖B‖ traceNorm(G)
                 = ‖A‖ ‖B‖ KummerSeries(λ, 1/(4α)).

The proof factors G as Q*Q for the true CFC-positive square root
Q=sqrt(G), invokes the exact full CFC S₂·S₂ Hölder estimate with
coefficient 1 on (A*Q)*(Q*B), and bounds the two HS squared energies
by ‖A‖², ‖B‖² times traceNorm(G).

This is an independent candidate until pinned CI and axiom audit
are SUCCESS. No finite-dimensional surrogate or abstract
yet-unchecked Banach S₁ completeness is assumed.
-/

noncomputable section
namespace GegenbauerFock.GeneralUltrasphericalFock
open MeasureTheory

theorem gram_twoSided_traceNorm_le_kummer_sharp
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (A B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.traceNorm
        (A * gram lam alpha hlam ha * B)
        (gram_twoSided_isTraceClass lam alpha hlam ha A B) ≤
      ‖A‖ * ‖B‖ *
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  let H := Lp ℂ 2 (Ultraspherical.measure lam)
  let G : H →L[ℂ] H := gram lam alpha hlam ha
  let hG : ProbabilisticTheory.IsTraceClass G :=
    gram_isTraceClass lam alpha hlam ha
  have hpos : 0 ≤ G := gram_nonneg lam alpha hlam ha
  let Q : H →L[ℂ] H := CFC.sqrt G
  have hQQ : Q * Q = G := CFC.sqrt_mul_sqrt_self G hpos
  have hQ : ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt Q := by
    have hh := ProbabilisticTheory.traceClass_sqrt_abs_isHS G hG
    rw [CFC.abs_of_nonneg G hpos] at hh
    exact hh
  have hAQ : ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt
      (A * Q) := by
    change ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt (A.comp Q)
    exact ProbabilisticTheory.HilbertSchmidt.isHilbertSchmidt_comp_left Q hQ A
  have hQB : ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt
      (Q * B) := by
    change ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt (Q.comp B)
    exact ProbabilisticTheory.HilbertSchmidt.isHilbertSchmidt_comp_right Q hQ B
  have hfactor : (A * Q) * (Q * B) = A * G * B := by
    calc
      (A * Q) * (Q * B) = A * (Q * Q) * B := by
        simp only [mul_assoc]
      _ = A * G * B := by rw [hQQ]
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hQsum : Summable (fun i : w => ‖Q (b i)‖ ^ 2) :=
    ProbabilisticTheory.HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis
      w b hQ
  have hAQsum : Summable (fun i : w => ‖(A * Q) (b i)‖ ^ 2) :=
    ProbabilisticTheory.HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis
      w b hAQ
  have hQBsum : Summable (fun i : w => ‖(Q * B) (b i)‖ ^ 2) :=
    ProbabilisticTheory.HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis
      w b hQB
  let eQ : ℝ := ∑' i : w, ‖Q (b i)‖ ^ 2
  let eAQ : ℝ := ∑' i : w, ‖(A * Q) (b i)‖ ^ 2
  let eQB : ℝ := ∑' i : w, ‖(Q * B) (b i)‖ ^ 2
  have heQ : 0 ≤ eQ := tsum_nonneg (fun i => sq_nonneg _)
  have heAQ : 0 ≤ eAQ := tsum_nonneg (fun i => sq_nonneg _)
  have heQB : 0 ≤ eQB := tsum_nonneg (fun i => sq_nonneg _)
  have hQtrace :
      ProbabilisticTheory.traceNorm G hG = eQ := by
    have h := ProbabilisticTheory.traceNorm_eq_sqrt_abs_basisEnergy G hG b
    rw [CFC.abs_of_nonneg G hpos] at h
    exact h
  have hpoint (i : w) :
      ‖(A * Q) (b i)‖ ^ 2 ≤
        ‖A‖ ^ 2 * ‖Q (b i)‖ ^ 2 := by
    change ‖A (Q (b i))‖ ^ 2 ≤ _
    calc
      ‖A (Q (b i))‖ ^ 2 ≤
          (‖A‖ * ‖Q (b i)‖) ^ 2 := by
        exact (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
            (ContinuousLinearMap.le_opNorm A (Q (b i)))
      _ = ‖A‖ ^ 2 * ‖Q (b i)‖ ^ 2 := by ring
  have hleft : eAQ ≤ ‖A‖ ^ 2 * eQ := by
    calc
      eAQ ≤ ∑' i : w, ‖A‖ ^ 2 * ‖Q (b i)‖ ^ 2 :=
        hAQsum.tsum_le_tsum hpoint (hQsum.mul_left (‖A‖ ^ 2))
      _ = ‖A‖ ^ 2 * eQ := tsum_mul_left
  have hright : eQB ≤ ‖B‖ ^ 2 * eQ := by
    have h := ProbabilisticTheory.HilbertSchmidt.right_basis_energy_le
      Q hQ B b
    exact h
  have hproduct : eAQ * eQB ≤ (‖A‖ * ‖B‖ * eQ) ^ 2 := by
    calc
      eAQ * eQB ≤ (‖A‖ ^ 2 * eQ) * (‖B‖ ^ 2 * eQ) :=
        mul_le_mul hleft hright heQB
          (mul_nonneg (sq_nonneg _) heQ)
      _ = (‖A‖ * ‖B‖ * eQ) ^ 2 := by ring
  have hroot : Real.sqrt (eAQ * eQB) ≤ ‖A‖ * ‖B‖ * eQ := by
    have hsq := Real.sq_sqrt (mul_nonneg heAQ heQB)
    have hrootpos := Real.sqrt_nonneg (eAQ * eQB)
    have hrhs : 0 ≤ ‖A‖ * ‖B‖ * eQ := by positivity
    nlinarith
  have htrace :
      ProbabilisticTheory.traceNorm
          (A * G * B)
          (gram_twoSided_isTraceClass lam alpha hlam ha A B) =
      ProbabilisticTheory.traceNorm
          ((A * Q) * (Q * B))
          (ProbabilisticTheory.isTraceClass_mul_of_twoHilbertSchmidt
            (A * Q) (Q * B) hAQ hQB) := by
    rw [ProbabilisticTheory.traceNorm_eq_of_hilbertBasis
        (gram_twoSided_isTraceClass lam alpha hlam ha A B) b,
      ProbabilisticTheory.traceNorm_eq_of_hilbertBasis
        (ProbabilisticTheory.isTraceClass_mul_of_twoHilbertSchmidt
          (A * Q) (Q * B) hAQ hQB) b,
      ← hfactor]
  calc
    ProbabilisticTheory.traceNorm
        (A * gram lam alpha hlam ha * B)
        (gram_twoSided_isTraceClass lam alpha hlam ha A B) =
      ProbabilisticTheory.traceNorm
        ((A * Q) * (Q * B))
        (ProbabilisticTheory.isTraceClass_mul_of_twoHilbertSchmidt
          (A * Q) (Q * B) hAQ hQB) := htrace
    _ ≤ Real.sqrt (eAQ * eQB) :=
      ProbabilisticTheory.traceNorm_mul_twoHilbertSchmidt_le_sqrt_energy_mul
        (A * Q) (Q * B) hAQ hQB b
    _ ≤ ‖A‖ * ‖B‖ * eQ := hroot
    _ = ‖A‖ * ‖B‖ *
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
      rw [← hQtrace]
      dsimp only [G, hG]
      rw [gram_traceNorm_eq_kummer lam alpha hlam ha]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_twoSided_traceNorm_le_kummer_sharp

end GegenbauerFock.GeneralUltrasphericalFock
