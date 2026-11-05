import GegenbauerFock.GegenbauerIntrinsicEntireHSLambdaStrictIdentifiability
import GegenbauerFock.GegenbauerIntrinsicEntireHSStrictMonotonicity

/-!
# V007 — simultaneous coordinatewise ordering in ultraspherical and Gaussian parameters

For lambda₁ ≤ lambda₂ and alpha₁ ≤ alpha₂, the genuine Gaussian-Fock
Kummer energy H(lambda,alpha) is antitone in both variables, strictly
so if at least one comparison is strict. The results transfer to
Hilbert–Schmidt source-basis energies and source-Gram diagonal traces
even though the different ultraspherical parameters determine
different source Hilbert spaces.

Coordinatewise strict antitonicity does NOT imply joint identifiability
of (lambda,alpha) from one scalar observation; this module makes no
such assertion.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- Simultaneously increasing lambda and Gaussian width cannot raise
the unregularized Kummer/Fock scalar energy. -/
theorem kummerSeries_mixed_antitone
    (lam₁ lam₂ alpha₁ alpha₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂) :
    kummerSeries lam₂ (1 / (4 * alpha₂)) ≤
      kummerSeries lam₁ (1 / (4 * alpha₁)) := by
  have hlam₂ : 0 < lam₂ := lt_of_lt_of_le hlam₁ hleL
  have hargs : (1 / (4 * alpha₂) : ℝ) ≤ 1 / (4 * alpha₁) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  calc
    kummerSeries lam₂ (1 / (4 * alpha₂)) ≤
        kummerSeries lam₂ (1 / (4 * alpha₁)) :=
      kummerSeries_mono_of_nonneg
        lam₂ (1 / (4 * alpha₂)) (1 / (4 * alpha₁))
        hlam₂ (by positivity) hargs
    _ ≤ kummerSeries lam₁ (1 / (4 * alpha₁)) :=
      kummerSeries_antitone_lambda
        lam₁ lam₂ (1 / (4 * alpha₁)) hlam₁ hleL (by positivity)

/-- Simultaneous weak width ordering and strictly increasing lambda
force a strictly decreasing Kummer/Fock mass. -/
theorem kummerSeries_mixed_strict_of_lambda
    (lam₁ lam₂ alpha₁ alpha₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hltL : lam₁ < lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂) :
    kummerSeries lam₂ (1 / (4 * alpha₂)) <
      kummerSeries lam₁ (1 / (4 * alpha₁)) := by
  have hlam₂ : 0 < lam₂ := lt_trans hlam₁ hltL
  have hargs : (1 / (4 * alpha₂) : ℝ) ≤ 1 / (4 * alpha₁) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  calc
    kummerSeries lam₂ (1 / (4 * alpha₂)) ≤
        kummerSeries lam₂ (1 / (4 * alpha₁)) :=
      kummerSeries_mono_of_nonneg
        lam₂ (1 / (4 * alpha₂)) (1 / (4 * alpha₁))
        hlam₂ (by positivity) hargs
    _ < kummerSeries lam₁ (1 / (4 * alpha₁)) :=
      kummerSeries_strictAnti_lambda
        lam₁ lam₂ (1 / (4 * alpha₁)) hlam₁ hltL (by positivity)

/-- Simultaneous weak lambda ordering and strictly increasing
Gaussian width force a strictly decreasing Kummer/Fock mass. -/
theorem kummerSeries_mixed_strict_of_alpha
    (lam₁ lam₂ alpha₁ alpha₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hltA : alpha₁ < alpha₂) :
    kummerSeries lam₂ (1 / (4 * alpha₂)) <
      kummerSeries lam₁ (1 / (4 * alpha₁)) := by
  have hlam₂ : 0 < lam₂ := lt_of_lt_of_le hlam₁ hleL
  have hargs : (1 / (4 * alpha₂) : ℝ) < 1 / (4 * alpha₁) :=
    one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  calc
    kummerSeries lam₂ (1 / (4 * alpha₂)) <
        kummerSeries lam₂ (1 / (4 * alpha₁)) :=
      kummerSeries_strictMono_nonneg
        lam₂ (1 / (4 * alpha₂)) (1 / (4 * alpha₁))
        hlam₂ (by positivity) hargs
    _ ≤ kummerSeries lam₁ (1 / (4 * alpha₁)) :=
      kummerSeries_antitone_lambda
        lam₁ lam₂ (1 / (4 * alpha₁)) hlam₁ hleL (by positivity)

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_mixed_antitone
#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_mixed_strict_of_lambda
#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_mixed_strict_of_alpha

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Genuine complete-basis Hilbert–Schmidt squared energy is
strictly antitone in the joint parameter order when lambda increases. -/
theorem C_intrinsicEntire_HS_energy_mixed_strict_of_lambda
    (lam₁ lam₂ alpha₁ alpha₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hltL : lam₁ < lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂))) :
    (∑' i : ι₂,
      ‖C_intrinsicEntire lam₂ alpha₂ (lt_trans hlam₁ hltL) ha₂ (b₂ i)‖ ^ 2) <
    (∑' i : ι₁,
      ‖C_intrinsicEntire lam₁ alpha₁ hlam₁ ha₁ (b₁ i)‖ ^ 2) := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer
       lam₂ alpha₂ (lt_trans hlam₁ hltL) ha₂ b₂,
      C_intrinsicEntire_HS_energy_eq_kummer lam₁ alpha₁ hlam₁ ha₁ b₁]
  exact KummerCoefficients.kummerSeries_mixed_strict_of_lambda
    lam₁ lam₂ alpha₁ alpha₂ hlam₁ hltL ha₁ ha₂ hleA

/-- Genuine Fock S2 energy is strictly antitone in the joint
parameter order when Gaussian width increases. -/
theorem C_intrinsicEntire_HS_energy_mixed_strict_of_alpha
    (lam₁ lam₂ alpha₁ alpha₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hltA : alpha₁ < alpha₂)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂))) :
    (∑' i : ι₂,
      ‖C_intrinsicEntire lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ (b₂ i)‖ ^ 2) <
    (∑' i : ι₁,
      ‖C_intrinsicEntire lam₁ alpha₁ hlam₁ ha₁ (b₁ i)‖ ^ 2) := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer
       lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ b₂,
      C_intrinsicEntire_HS_energy_eq_kummer lam₁ alpha₁ hlam₁ ha₁ b₁]
  exact KummerCoefficients.kummerSeries_mixed_strict_of_alpha
    lam₁ lam₂ alpha₁ alpha₂ hlam₁ hleL ha₁ ha₂ hltA

/-- True source-Gram real diagonal trace is strictly antitone
under weak Gaussian ordering and strict ultraspherical ordering. -/
theorem C_intrinsicEntire_Gram_trace_mixed_strict_of_lambda
    (lam₁ lam₂ alpha₁ alpha₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hltL : lam₁ < lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂))) :
    (∑' i : ι₂, RCLike.re (inner ℂ
      (C_intrinsicEntire_gram lam₂ alpha₂ (lt_trans hlam₁ hltL) ha₂ (b₂ i))
      (b₂ i))) <
    (∑' i : ι₁, RCLike.re (inner ℂ
      (C_intrinsicEntire_gram lam₁ alpha₁ hlam₁ ha₁ (b₁ i))
      (b₁ i))) := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer
       lam₂ alpha₂ (lt_trans hlam₁ hltL) ha₂ b₂,
      C_intrinsicEntire_Gram_basis_trace_eq_kummer lam₁ alpha₁ hlam₁ ha₁ b₁]
  exact KummerCoefficients.kummerSeries_mixed_strict_of_lambda
    lam₁ lam₂ alpha₁ alpha₂ hlam₁ hltL ha₁ ha₂ hleA

/-- True source-Gram real diagonal trace is strictly antitone
under weak ultraspherical ordering and strict Gaussian ordering. -/
theorem C_intrinsicEntire_Gram_trace_mixed_strict_of_alpha
    (lam₁ lam₂ alpha₁ alpha₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hltA : alpha₁ < alpha₂)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂))) :
    (∑' i : ι₂, RCLike.re (inner ℂ
      (C_intrinsicEntire_gram lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ (b₂ i))
      (b₂ i))) <
    (∑' i : ι₁, RCLike.re (inner ℂ
      (C_intrinsicEntire_gram lam₁ alpha₁ hlam₁ ha₁ (b₁ i))
      (b₁ i))) := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer
       lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ b₂,
      C_intrinsicEntire_Gram_basis_trace_eq_kummer lam₁ alpha₁ hlam₁ ha₁ b₁]
  exact KummerCoefficients.kummerSeries_mixed_strict_of_alpha
    lam₁ lam₂ alpha₁ alpha₂ hlam₁ hleL ha₁ ha₂ hltA

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_mixed_strict_of_lambda
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_mixed_strict_of_alpha
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_mixed_strict_of_lambda
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_mixed_strict_of_alpha

end GegenbauerFock.GeneralUltrasphericalFock
