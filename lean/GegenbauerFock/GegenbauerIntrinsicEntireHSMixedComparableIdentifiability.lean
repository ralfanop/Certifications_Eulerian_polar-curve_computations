import GegenbauerFock.GegenbauerIntrinsicEntireHSMixedParameterOrder

/-!
# V007 — joint parameter identifiability on coordinatewise-comparable pairs

The exact entire-Fock Kummer mass is strictly antitone along every
nonconstant coordinatewise-increasing path in the positive parameter
quadrant. Thus, if two positive pairs are comparable in the product
order, equality of their masses forces both coordinates to be equal.

This is an injectivity theorem *on comparable pairs*, not global
joint identifiability of (lambda, alpha) from one scalar observation.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- Equal Kummer masses force both positive parameters to coincide
whenever the two parameter pairs are coordinatewise ordered. -/
theorem kummerSeries_identifies_comparable_pair
    (lam₁ lam₂ alpha₁ alpha₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂)
    (heq :
      kummerSeries lam₁ (1 / (4 * alpha₁)) =
        kummerSeries lam₂ (1 / (4 * alpha₂))) :
    lam₁ = lam₂ ∧ alpha₁ = alpha₂ := by
  have hlam₂ : 0 < lam₂ := lt_of_lt_of_le hlam₁ hleL
  rcases lt_or_eq_of_le hleL with hltL | heqL
  · have hlt := kummerSeries_mixed_strict_of_lambda
      lam₁ lam₂ alpha₁ alpha₂ hlam₁ hltL ha₁ ha₂ hleA
    exact False.elim (hlt.ne heq.symm)
  · rcases lt_or_eq_of_le hleA with hltA | heqA
    · have hlt := kummerSeries_mixed_strict_of_alpha
        lam₁ lam₂ alpha₁ alpha₂ hlam₁ hleL ha₁ ha₂ hltA
      exact False.elim (hlt.ne heq.symm)
    · exact ⟨heqL, heqA⟩

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_identifies_comparable_pair

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The genuine source-basis Hilbert–Schmidt squared energy identifies
both parameters jointly for positive *comparable* parameter pairs;
the source Hilbert spaces and complete bases may be different. -/
theorem C_intrinsicEntire_HS_energy_identifies_comparable_pair
    (lam₁ lam₂ alpha₁ alpha₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂)))
    (heq :
      (∑' i : ι₁,
        ‖C_intrinsicEntire lam₁ alpha₁ hlam₁ ha₁ (b₁ i)‖ ^ 2) =
      (∑' i : ι₂,
        ‖C_intrinsicEntire lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂
          (b₂ i)‖ ^ 2)) :
    lam₁ = lam₂ ∧ alpha₁ = alpha₂ := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer
      lam₁ alpha₁ hlam₁ ha₁ b₁,
      C_intrinsicEntire_HS_energy_eq_kummer
      lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ b₂] at heq
  exact KummerCoefficients.kummerSeries_identifies_comparable_pair
    lam₁ lam₂ alpha₁ alpha₂ hlam₁ hleL ha₁ ha₂ hleA heq

/-- Joint identifiability on comparable pairs from actual
intrinsic source-Gram real diagonal traces with unrelated bases. -/
theorem C_intrinsicEntire_Gram_trace_identifies_comparable_pair
    (lam₁ lam₂ alpha₁ alpha₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂)))
    (heq :
      (∑' i : ι₁, RCLike.re (inner ℂ
        (C_intrinsicEntire_gram lam₁ alpha₁ hlam₁ ha₁ (b₁ i)) (b₁ i))) =
      (∑' i : ι₂, RCLike.re (inner ℂ
        (C_intrinsicEntire_gram lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂
          (b₂ i)) (b₂ i)))) :
    lam₁ = lam₂ ∧ alpha₁ = alpha₂ := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer
      lam₁ alpha₁ hlam₁ ha₁ b₁,
      C_intrinsicEntire_Gram_basis_trace_eq_kummer
      lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ b₂] at heq
  exact KummerCoefficients.kummerSeries_identifies_comparable_pair
    lam₁ lam₂ alpha₁ alpha₂ hlam₁ hleL ha₁ ha₂ hleA heq

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_identifies_comparable_pair
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_identifies_comparable_pair

end GegenbauerFock.GeneralUltrasphericalFock
