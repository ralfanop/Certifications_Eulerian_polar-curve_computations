import GegenbauerFock.PhyslibHSProductTraceNormHolder
import GegenbauerFock.PhyslibTraceClassTwoSidedIdeal
import GegenbauerFock.PhyslibTraceNormSqrtAbsEnergy
import GegenbauerFock.PhyslibHSRightBasisEnergyBound

/-!
# V007 — sharp two-sided trace norm ideal law for arbitrary CFC-S₁ maps

For T in the true source-compatible complex trace class and arbitrary
bounded A,B on any complete complex Hilbert space,

  ‖A*T*B‖₁ ≤ ‖A‖ * ‖B‖ * ‖T‖₁.

We use the polar factorization T=R*Q with Q=sqrt(|T|)
and R=polarFactor(T)*Q. Both are genuinely Hilbert--Schmidt.
The previously certified sharp HS-product Holder bound applies to
(A*R)*(Q*B); the two HS energies are controlled by A and B.
No positivity, finite-rank surrogate, or Banach-completeness axiom
is required.
-/

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem traceNorm_twoSided_le
    (T A B : H →L[ℂ] H) (hT : IsTraceClass T) :
    traceNorm (A * T * B) (isTraceClass_twoSided T hT A B) ≤
      ‖A‖ * ‖B‖ * traceNorm T hT := by
  let U : H →L[ℂ] H := Polar.polarFactor T
  let Q : H →L[ℂ] H := CFC.sqrt (CFC.abs T)
  let R : H →L[ℂ] H := U * Q
  have hQ : HilbertSchmidt.IsHilbertSchmidt Q :=
    traceClass_sqrt_abs_isHS T hT
  have hR : HilbertSchmidt.IsHilbertSchmidt R := by
    change HilbertSchmidt.IsHilbertSchmidt
      ((Polar.polarFactor T).comp (CFC.sqrt (CFC.abs T)))
    exact traceClass_polar_sqrt_abs_isHS T hT
  have hQQ : Q * Q = CFC.abs T :=
    CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)
  have hRQ : R * Q = T := by
    calc
      R * Q = U * (Q * Q) := mul_assoc _ _ _
      _ = U * CFC.abs T := by rw [hQQ]
      _ = T := Polar.polarFactor_mul_absOperator T
  have hAR : HilbertSchmidt.IsHilbertSchmidt (A * R) := by
    change HilbertSchmidt.IsHilbertSchmidt (A.comp R)
    exact HilbertSchmidt.isHilbertSchmidt_comp_left R hR A
  have hQB : HilbertSchmidt.IsHilbertSchmidt (Q * B) := by
    change HilbertSchmidt.IsHilbertSchmidt (Q.comp B)
    exact HilbertSchmidt.isHilbertSchmidt_comp_right Q hQ B
  have hfactor : (A * R) * (Q * B) = A * T * B := by
    calc
      (A * R) * (Q * B) = A * (R * Q) * B := by
        simp only [mul_assoc]
      _ = A * T * B := by rw [hRQ]
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hQsum : Summable (fun i : w => ‖Q (b i)‖ ^ 2) :=
    HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hQ
  have hARsum : Summable (fun i : w => ‖(A * R) (b i)‖ ^ 2) :=
    HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hAR
  have hQBsum : Summable (fun i : w => ‖(Q * B) (b i)‖ ^ 2) :=
    HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hQB
  let eQ : ℝ := ∑' i : w, ‖Q (b i)‖ ^ 2
  let eAR : ℝ := ∑' i : w, ‖(A * R) (b i)‖ ^ 2
  let eQB : ℝ := ∑' i : w, ‖(Q * B) (b i)‖ ^ 2
  have heQ : 0 ≤ eQ := tsum_nonneg (fun i => sq_nonneg _)
  have heAR : 0 ≤ eAR := tsum_nonneg (fun i => sq_nonneg _)
  have heQB : 0 ≤ eQB := tsum_nonneg (fun i => sq_nonneg _)
  have htraceQ : traceNorm T hT = eQ :=
    traceNorm_eq_sqrt_abs_basisEnergy T hT b
  have hpoint (i : w) :
      ‖(A * R) (b i)‖ ^ 2 ≤
        ‖A‖ ^ 2 * ‖Q (b i)‖ ^ 2 := by
    have hAop : ‖A (R (b i))‖ ≤ ‖A‖ * ‖R (b i)‖ :=
      ContinuousLinearMap.le_opNorm A (R (b i))
    have hU : ‖R (b i)‖ ≤ ‖Q (b i)‖ :=
      Polar.polarFactor_norm_le T (Q (b i))
    have hpoint' : ‖(A * R) (b i)‖ ≤ ‖A‖ * ‖Q (b i)‖ := by
      change ‖A (R (b i))‖ ≤ _
      exact hAop.trans (mul_le_mul_of_nonneg_left hU (norm_nonneg _))
    calc
      ‖(A * R) (b i)‖ ^ 2 ≤ (‖A‖ * ‖Q (b i)‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
          hpoint'
      _ = ‖A‖ ^ 2 * ‖Q (b i)‖ ^ 2 := by ring
  have hleft : eAR ≤ ‖A‖ ^ 2 * eQ := by
    calc
      eAR ≤ ∑' i : w, ‖A‖ ^ 2 * ‖Q (b i)‖ ^ 2 :=
        hARsum.tsum_le_tsum hpoint (hQsum.mul_left (‖A‖ ^ 2))
      _ = ‖A‖ ^ 2 * eQ := tsum_mul_left
  have hright : eQB ≤ ‖B‖ ^ 2 * eQ :=
    HilbertSchmidt.right_basis_energy_le Q hQ B b
  have hproduct : eAR * eQB ≤ (‖A‖ * ‖B‖ * eQ) ^ 2 := by
    calc
      eAR * eQB ≤ (‖A‖ ^ 2 * eQ) * (‖B‖ ^ 2 * eQ) :=
        mul_le_mul hleft hright heQB (mul_nonneg (sq_nonneg _) heQ)
      _ = (‖A‖ * ‖B‖ * eQ) ^ 2 := by ring
  have hroot : Real.sqrt (eAR * eQB) ≤ ‖A‖ * ‖B‖ * eQ := by
    have hsq := Real.sq_sqrt (mul_nonneg heAR heQB)
    have hrootpos := Real.sqrt_nonneg (eAR * eQB)
    have hrhs : 0 ≤ ‖A‖ * ‖B‖ * eQ := by positivity
    nlinarith
  have hnormeq :
      traceNorm (A * T * B) (isTraceClass_twoSided T hT A B) =
      traceNorm ((A * R) * (Q * B))
        (isTraceClass_mul_of_twoHilbertSchmidt (A * R) (Q * B) hAR hQB) := by
    rw [traceNorm_eq_of_hilbertBasis (isTraceClass_twoSided T hT A B) b,
      traceNorm_eq_of_hilbertBasis
        (isTraceClass_mul_of_twoHilbertSchmidt (A * R) (Q * B) hAR hQB) b,
      ← hfactor]
  calc
    traceNorm (A * T * B) (isTraceClass_twoSided T hT A B) =
        traceNorm ((A * R) * (Q * B))
          (isTraceClass_mul_of_twoHilbertSchmidt (A * R) (Q * B) hAR hQB) :=
      hnormeq
    _ ≤ Real.sqrt (eAR * eQB) :=
      traceNorm_mul_twoHilbertSchmidt_le_sqrt_energy_mul
        (A * R) (Q * B) hAR hQB b
    _ ≤ ‖A‖ * ‖B‖ * eQ := hroot
    _ = ‖A‖ * ‖B‖ * traceNorm T hT := by rw [htraceQ]

#print axioms ProbabilisticTheory.traceNorm_twoSided_le

end ProbabilisticTheory
