import GegenbauerFock.GegenbauerIntrinsicEntireGramPairing
import GegenbauerFock.GramNuclearTrace

/-!
# V007 — basis-independent Hilbert–Schmidt Kummer energy in true analytic Fock

The ultraspherical-to-Gaussian entire-L² operator is a genuine
bounded operator between Hilbert spaces. Its squared Hilbert–Schmidt
source-basis energy is summable for EVERY complete source Hilbert
basis, and equals the unregularized Kummer series independently
certified for the coefficient-space transform.

The result is phrased using the already certified basis-defined S₂
criterion, and does not quietly identify that criterion with a
different external Schatten ideal implementation.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- On every complete source Hilbert basis, the true holomorphic
Gaussian L² transform has summable squared output norms. -/
theorem C_intrinsicEntire_HS_basis_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    Summable (fun i : ι =>
      ‖C_intrinsicEntire lam alpha hlam ha (b i)‖ ^ 2) := by
  have h :
      Summable (fun i : ι => ‖C lam alpha hlam ha (b i)‖ ^ 2) :=
    (C_isHilbertSchmidt lam alpha hlam ha) b
  simpa only [C_intrinsicEntire_norm] using h

/-- The exact basis-independent S₂ energy on the actual analytic
Bargmann–Fock codomain equals the unregularized Kummer series. -/
theorem C_intrinsicEntire_HS_energy_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (∑' i : ι, ‖C_intrinsicEntire lam alpha hlam ha (b i)‖ ^ 2) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  calc
    (∑' i : ι, ‖C_intrinsicEntire lam alpha hlam ha (b i)‖ ^ 2) =
        ∑' i : ι, ‖C lam alpha hlam ha (b i)‖ ^ 2 := by
          apply tsum_congr
          intro i
          rw [C_intrinsicEntire_norm lam alpha hlam ha]
    _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
      C_sourceBasis_HSEnergy_eq_kummer lam alpha hlam ha b

/-- Consequently the actual intrinsic Fock source-Gram diagonal trace
has the same Kummer value in every complete source Hilbert basis. -/
theorem C_intrinsicEntire_Gram_basis_trace_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (∑' i : ι,
      RCLike.re (inner ℂ
        (C_intrinsicEntire_gram lam alpha hlam ha (b i)) (b i))) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  calc
    (∑' i : ι,
        RCLike.re (inner ℂ
          (C_intrinsicEntire_gram lam alpha hlam ha (b i)) (b i))) =
      (∑' i : ι, ‖C_intrinsicEntire lam alpha hlam ha (b i)‖ ^ 2) := by
        apply tsum_congr
        intro i
        rw [C_intrinsicEntire_gram_energy lam alpha hlam ha (b i)]
        exact (HilbertGram.gram_norm_sq
          (C lam alpha hlam ha) (b i)).symm
    _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
      C_intrinsicEntire_HS_energy_eq_kummer lam alpha hlam ha b

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_basis_summable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_eq_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_basis_trace_eq_kummer

end GegenbauerFock.GeneralUltrasphericalFock
