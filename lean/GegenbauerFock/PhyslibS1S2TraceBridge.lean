import GegenbauerFock.FockHilbertSchmidtNorm
import GegenbauerFock.PhyslibPositiveTraceAddNorm

/-!
# V007 — genuine trace-norm / Hilbert–Schmidt-norm square identity

The actual Gegenbauer–Fock map C : L²(νλ) → ℓ² has a basis-independent
Hilbert–Schmidt S₂ norm. Its genuine positive Gram C†C and every
bounded source conjugation B†C†CB have the Physlib-compatible CFC
trace norm. Here we show the two norms coincide **exactly**:
  ‖C†C‖₁ = ‖C‖₂²
  ‖B†C†CB‖₁ = ‖C ∘ B‖₂².
In particular both coincide with the previously kernel-checked
Gaussian/Kummer row-energy calculation in the B = id case.

This is a real infinite-dimensional operator identity. It does not
assume generic trace-class addition, the S₁ triangle inequality,
or a completed normed Banach Schatten type.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- The true S₂ norm squared of the ultraspherical analysis operator
is exactly the unregularized Kummer function. -/
theorem C_s2Norm_sq_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (FockEnergy.s2Norm (C lam alpha hlam ha)
      (C_rows_summable lam alpha hlam ha)) ^ 2 =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  calc
    (FockEnergy.s2Norm (C lam alpha hlam ha)
      (C_rows_summable lam alpha hlam ha)) ^ 2 =
        ∑' n : ℕ,
          ‖SummableRowsCompact.row (C lam alpha hlam ha) n‖ ^ 2 :=
            FockEnergy.s2Norm_sq_eq_rowEnergy
              (C lam alpha hlam ha) (C_rows_summable lam alpha hlam ha)
    _ = ∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖ := by
      apply tsum_congr
      intro n
      exact (gramNuclearTerm_norm_eq_row_sq lam alpha hlam ha n).symm
    _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
      gramNuclearMass_eq_kummerSeries lam alpha hlam ha

/-- The S₂ norm itself is the square root of the exact positive
ultraspherical Kummer scalar, with no chosen source Hilbert basis. -/
theorem C_s2Norm_eq_sqrt_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    FockEnergy.s2Norm (C lam alpha hlam ha)
      (C_rows_summable lam alpha hlam ha) =
        Real.sqrt (KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) := by
  change Real.sqrt
      (∑' n : ℕ, ‖SummableRowsCompact.row (C lam alpha hlam ha) n‖ ^ 2) = _
  have hsum :
      (∑' n : ℕ, ‖SummableRowsCompact.row (C lam alpha hlam ha) n‖ ^ 2) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
    calc
      _ = ∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖ := by
        apply tsum_congr
        intro n
        exact (gramNuclearTerm_norm_eq_row_sq lam alpha hlam ha n).symm
      _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
        gramNuclearMass_eq_kummerSeries lam alpha hlam ha
  rw [hsum]

/-- Schatten identity S₁(C†C) = (S₂ C)² for the genuine
CFC-absolute trace norm, not a formal nuclear-mass proxy. -/
theorem gram_traceNorm_eq_s2Norm_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.traceNorm (gram lam alpha hlam ha)
      (gram_isTraceClass lam alpha hlam ha) =
      (FockEnergy.s2Norm (C lam alpha hlam ha)
        (C_rows_summable lam alpha hlam ha)) ^ 2 := by
  calc
    _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
      gram_traceNorm_eq_kummer lam alpha hlam ha
    _ = _ := (C_s2Norm_sq_eq_kummer lam alpha hlam ha).symm

/-- Schatten identity for *every* bounded source preconditioner:
S₁(B†C†CB) = (S₂(C ∘ B))². The two norms are the actual CFC and
basis-independent Hilbert–Schmidt norms, not proxies. -/
theorem gramAfterRight_traceNorm_eq_s2Norm_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.traceNorm (gramAfterRight lam alpha hlam ha B)
      (gramAfterRight_isTraceClass lam alpha hlam ha B) =
    (FockEnergy.s2Norm ((C lam alpha hlam ha).comp B)
      (C_comp_right_rows_summable lam alpha hlam ha B)) ^ 2 := by
  calc
    _ = ∑' n : ℕ,
        ‖(SummableRowsCompact.row (C lam alpha hlam ha) n).comp B‖ ^ 2 :=
      gramAfterRight_traceNorm_eq_composedRowMass lam alpha hlam ha B
    _ = ∑' n : ℕ,
        ‖SummableRowsCompact.row ((C lam alpha hlam ha).comp B) n‖ ^ 2 := by
      apply tsum_congr
      intro n
      rw [C_row_comp_right lam alpha hlam ha B n]
    _ = (FockEnergy.s2Norm ((C lam alpha hlam ha).comp B)
          (C_comp_right_rows_summable lam alpha hlam ha B)) ^ 2 :=
      (FockEnergy.s2Norm_sq_eq_rowEnergy
        ((C lam alpha hlam ha).comp B)
        (C_comp_right_rows_summable lam alpha hlam ha B)).symm

/-- The true trace-norm ideal inequality expressed in terms of
the genuine Fock S₂ norm, without any finite-rank hypothesis. -/
theorem gramAfterRight_traceNorm_le_s2Norm_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.traceNorm (gramAfterRight lam alpha hlam ha B)
      (gramAfterRight_isTraceClass lam alpha hlam ha B) ≤
      ‖B‖ ^ 2 *
        (FockEnergy.s2Norm (C lam alpha hlam ha)
          (C_rows_summable lam alpha hlam ha)) ^ 2 := by
  rw [C_s2Norm_sq_eq_kummer]
  exact gramAfterRight_traceNorm_le_kummer lam alpha hlam ha B

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_s2Norm_sq_eq_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_s2Norm_eq_sqrt_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_traceNorm_eq_s2Norm_sq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramAfterRight_traceNorm_eq_s2Norm_sq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramAfterRight_traceNorm_le_s2Norm_sq

end GegenbauerFock.GeneralUltrasphericalFock
