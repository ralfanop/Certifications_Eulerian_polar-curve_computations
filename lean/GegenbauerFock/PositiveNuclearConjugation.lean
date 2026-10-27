import GegenbauerFock.PositiveTraceClassBridge

/-!
# V007: positive nuclear row mass under bounded source conjugation

A trace-class Gram presentation with genuinely summable squared norms
of the rank-one generating rows has finite nuclear mass. Precomposition
of the rows by *any* bounded endomorphism preserves summability, with
the ideal bound ||r_n ◦ B||² ≤ ||B||² ||r_n||², and the corresponding
precise estimate for total positive nuclear mass.

Unlike general Schatten S₁ ideal membership of ATB for arbitrary
trace-class T, this is an explicitly proved *positive conjugation*
estimate. This formulation avoids silently assuming an unported
general Physlib Banach/ideal theorem.
-/

noncomputable section

namespace GegenbauerFock.PositiveNuclearIdeal

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Squared Hilbert-row norm after any bounded precomposition obeys
the correct right ideal inequality. -/
theorem row_comp_norm_sq_le
    (r : E →L[ℂ] ℂ) (B : E →L[ℂ] E) :
    ‖r.comp B‖ ^ 2 ≤ ‖B‖ ^ 2 * ‖r‖ ^ 2 := by
  calc
    ‖r.comp B‖ ^ 2 ≤ (‖r‖ * ‖B‖) ^ 2 := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le r B
    _ = ‖B‖ ^ 2 * ‖r‖ ^ 2 := by ring

/-- General positive nuclear row-series summability is stable under
bounded precomposition. -/
theorem rows_comp_summable
    (rows : ℕ → (E →L[ℂ] ℂ))
    (hs : Summable (fun n : ℕ => ‖rows n‖ ^ 2))
    (B : E →L[ℂ] E) :
    Summable (fun n : ℕ => ‖(rows n).comp B‖ ^ 2) := by
  apply Summable.of_nonneg_of_le
  · intro n
    exact sq_nonneg _
  · intro n
    exact row_comp_norm_sq_le (rows n) B
  · exact hs.mul_left (‖B‖ ^ 2)

/-- The general Schatten-type positive conjugation bound on the
genuine convergent nuclear row mass; no abstract trace norm is
postulated. -/
theorem rows_comp_tsum_le
    (rows : ℕ → (E →L[ℂ] ℂ))
    (hs : Summable (fun n : ℕ => ‖rows n‖ ^ 2))
    (B : E →L[ℂ] E) :
    (∑' n : ℕ, ‖(rows n).comp B‖ ^ 2) ≤
      ‖B‖ ^ 2 * (∑' n : ℕ, ‖rows n‖ ^ 2) := by
  have hcomp := rows_comp_summable rows hs B
  have hbound : ∀ n : ℕ,
      ‖(rows n).comp B‖ ^ 2 ≤ ‖B‖ ^ 2 * ‖rows n‖ ^ 2 :=
    fun n => row_comp_norm_sq_le (rows n) B
  calc
    (∑' n : ℕ, ‖(rows n).comp B‖ ^ 2) ≤
        ∑' n : ℕ, ‖B‖ ^ 2 * ‖rows n‖ ^ 2 :=
          hcomp.tsum_le_tsum hbound (hs.mul_left (‖B‖ ^ 2))
    _ = ‖B‖ ^ 2 * (∑' n : ℕ, ‖rows n‖ ^ 2) := tsum_mul_left

#print axioms GegenbauerFock.PositiveNuclearIdeal.row_comp_norm_sq_le
#print axioms GegenbauerFock.PositiveNuclearIdeal.rows_comp_summable
#print axioms GegenbauerFock.PositiveNuclearIdeal.rows_comp_tsum_le

end GegenbauerFock.PositiveNuclearIdeal

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- All canonical ultraspherical--Fock rows remain square-summable
after arbitrary bounded precomposition. The theorem's *statement*
uses the genuine canonical rows to avoid a spurious probability
instance in the proposition itself. -/
theorem C_momentRows_comp_right_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    Summable (fun n : ℕ =>
      ‖(SummableRowsCompact.row (C lam alpha hlam ha) n).comp B‖ ^ 2) := by
  exact PositiveNuclearIdeal.rows_comp_summable
    (fun n : ℕ => SummableRowsCompact.row (C lam alpha hlam ha) n)
    (C_rows_summable lam alpha hlam ha) B

/-- The positive nuclear-mass estimate for bounded source
postprocessing of the actual ultraspherical Gram. Its exact scalar
bound is the kernel-checked Kummer trace-norm value. -/
theorem C_momentRows_comp_right_mass_le_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    (∑' n : ℕ,
      ‖(SummableRowsCompact.row (C lam alpha hlam ha) n).comp B‖ ^ 2) ≤
      ‖B‖ ^ 2 * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  have hm := PositiveNuclearIdeal.rows_comp_tsum_le
    (fun n : ℕ => SummableRowsCompact.row (C lam alpha hlam ha) n)
    (C_rows_summable lam alpha hlam ha) B
  have hmass :
      (∑' n : ℕ, ‖SummableRowsCompact.row
        (C lam alpha hlam ha) n‖ ^ 2) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
    calc
      (∑' n : ℕ, ‖SummableRowsCompact.row
        (C lam alpha hlam ha) n‖ ^ 2) =
        ∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖ := by
          apply tsum_congr
          intro n
          exact (gramNuclearTerm_norm_eq_row_sq lam alpha hlam ha n).symm
      _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
          gramNuclearMass_eq_kummerSeries lam alpha hlam ha
  calc
    (∑' n : ℕ,
      ‖(SummableRowsCompact.row (C lam alpha hlam ha) n).comp B‖ ^ 2) ≤
        ‖B‖ ^ 2 * (∑' n : ℕ,
          ‖SummableRowsCompact.row (C lam alpha hlam ha) n‖ ^ 2) := hm
    _ = ‖B‖ ^ 2 *
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by rw [hmass]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_momentRows_comp_right_summable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_momentRows_comp_right_mass_le_kummer

end GegenbauerFock.GeneralUltrasphericalFock
