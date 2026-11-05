import GegenbauerFock.HSRowBasisGeneral
import GegenbauerFock.PositiveNuclearConjugation

/-!
# V007 — full source-side S₂ ideal for the concrete rectangular Fock map

The kernel-checked general Riesz–Parseval/Tonelli bridge upgrades the
pre-existing canonical coordinate-row bound to summability on every
complete Hilbert source basis, after an arbitrary bounded source
operator B. The actual Hilbert–Schmidt energy then has the exact
quadratic ideal estimate controlled by the Γ-normalized Kummer norm.

This does not assume a bundled rectangular Schatten API, nor an
unproved right-ideal property of the source-compatible Physlib
endomorphism predicate.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- Canonical ℓ² row of a postcomposed Fock operator is exactly
postcomposition of that same genuine Fock row. -/
theorem C_row_comp_right
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) (n : ℕ) :
    SummableRowsCompact.row ((C lam alpha hlam ha).comp B) n =
      (SummableRowsCompact.row (C lam alpha hlam ha) n).comp B := by
  apply ContinuousLinearMap.ext
  intro f
  rfl

/-- Precomposition by an arbitrary bounded operator leaves
the actual Gegenbauer--Fock canonical rows square-summable. -/
theorem C_comp_right_rows_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row ((C lam alpha hlam ha).comp B) n‖ ^ 2) := by
  simpa only [C_row_comp_right lam alpha hlam ha B] using
    C_momentRows_comp_right_summable lam alpha hlam ha B

/-- **A genuine right S₂ ideal theorem:** the bounded rectangular
Gegenbauer--Fock map stays Hilbert--Schmidt after arbitrary bounded
precomposition, for EVERY complete source Hilbert basis. -/
theorem C_comp_right_isHilbertSchmidt
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    HilbertSchmidtBasis.IsHS ((C lam alpha hlam ha).comp B) := by
  intro ι b
  exact (FockEnergy.summableRows_iff_sourceBasis_energy
    ((C lam alpha hlam ha).comp B)
    (C_comp_right_rows_summable lam alpha hlam ha B) b).1

/-- Squared Hilbert--Schmidt norm right-ideal estimate, quantified
over arbitrary complete source Hilbert bases, with the exact
unregularized Kummer scalar bound. -/
theorem C_comp_right_basis_HSEnergy_le_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam))
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (∑' i : ι, ‖((C lam alpha hlam ha).comp B) (b i)‖ ^ 2) ≤
      ‖B‖ ^ 2 * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  calc
    (∑' i : ι, ‖((C lam alpha hlam ha).comp B) (b i)‖ ^ 2) =
        ∑' n : ℕ,
          ‖SummableRowsCompact.row ((C lam alpha hlam ha).comp B) n‖ ^ 2 :=
      (FockEnergy.summableRows_iff_sourceBasis_energy
        ((C lam alpha hlam ha).comp B)
        (C_comp_right_rows_summable lam alpha hlam ha B) b).2
    _ = ∑' n : ℕ,
        ‖(SummableRowsCompact.row (C lam alpha hlam ha) n).comp B‖ ^ 2 := by
      apply tsum_congr
      intro n
      rw [C_row_comp_right lam alpha hlam ha B n]
    _ ≤ ‖B‖ ^ 2 *
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
      C_momentRows_comp_right_mass_le_kummer lam alpha hlam ha B

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_row_comp_right
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_comp_right_rows_summable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_comp_right_isHilbertSchmidt
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_comp_right_basis_HSEnergy_le_kummer

end GegenbauerFock.GeneralUltrasphericalFock
