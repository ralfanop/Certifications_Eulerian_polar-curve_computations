import GegenbauerFock.GegenbauerIntrinsicEntireHSMixedCoordinateRecovery
import GegenbauerFock.GegenbauerIntrinsicEntireHSMixedParameterOrder

/-!
# V007 — two-parameter recovery from noisy true Hilbert–Schmidt norms

For coordinatewise-comparable positive pairs
  0 < lambda₁ <= lambda₂ <= L, 0 < a <= alpha₁ <= alpha₂ <= A,
a common observed unsquared Hilbert–Schmidt norm with errors eps₁, eps₂
controls each parameter difference with explicit constants.

N(lambda,alpha) = sqrt(H(lambda,alpha)), where H is the exact
Gaussian-Fock Kummer squared S₂ mass. Let M = sqrt(exp(1/(4*a))).
The results yield
  lambda₂-lambda₁ <= 16 A (L+1)^2 M (eps₁+eps₂)
  alpha₂-alpha₁ <= 16 (L+1) A^2 M (eps₁+eps₂).

Unlike unrestricted joint identifiability, the comparison explicitly
requires coordinatewise ordering, and the positive Gaussian lower
bound a is essential for the uniform norm-to-energy factor.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- On comparable positive parameter pairs with Gaussian width bounded
below by a > 0, the difference of exact squared masses is controlled
by errors against a shared observation of the *unsquared* masses. -/
theorem kummerSeries_mixed_norm_energy_gap_from_observation
    (lam₁ lam₂ alpha₁ alpha₂ a y eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂)
    (ha : 0 < a) (hlo₁ : a ≤ alpha₁) (hlo₂ : a ≤ alpha₂)
    (hleA : alpha₁ ≤ alpha₂)
    (h₁ : |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) - y| ≤ eps₁)
    (h₂ : |Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) - y| ≤ eps₂) :
    kummerSeries lam₁ (1 / (4 * alpha₁)) -
        kummerSeries lam₂ (1 / (4 * alpha₂)) ≤
      2 * Real.sqrt (Real.exp (1 / (4 * a))) * (eps₁ + eps₂) := by
  have hlam₂ : 0 < lam₂ := lt_of_lt_of_le hlam₁ hleL
  have ha₁ : 0 < alpha₁ := lt_of_lt_of_le ha hlo₁
  have ha₂ : 0 < alpha₂ := lt_of_lt_of_le ha hlo₂
  have harg₁ : (1 / (4 * alpha₁) : ℝ) ≤ 1 / (4 * a) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have harg₂ : (1 / (4 * alpha₂) : ℝ) ≤ 1 / (4 * a) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hK₁ : 0 ≤ kummerSeries lam₁ (1 / (4 * alpha₁)) := by
    have h := kummerSeries_ge_one lam₁ (1 / (4 * alpha₁))
      hlam₁ (by positivity)
    linarith
  have hK₂ : 0 ≤ kummerSeries lam₂ (1 / (4 * alpha₂)) := by
    have h := kummerSeries_ge_one lam₂ (1 / (4 * alpha₂))
      hlam₂ (by positivity)
    linarith
  have hupper₁ :
      Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) ≤
        Real.sqrt (Real.exp (1 / (4 * a))) :=
    Real.sqrt_le_sqrt
      ((kummerSeries_le_exp lam₁ (1 / (4 * alpha₁))
          hlam₁ (by positivity)).trans (Real.exp_le_exp.mpr harg₁))
  have hupper₂ :
      Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) ≤
        Real.sqrt (Real.exp (1 / (4 * a))) :=
    Real.sqrt_le_sqrt
      ((kummerSeries_le_exp lam₂ (1 / (4 * alpha₂))
          hlam₂ (by positivity)).trans (Real.exp_le_exp.mpr harg₂))
  have hsum :
      Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) +
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) ≤
      2 * Real.sqrt (Real.exp (1 / (4 * a))) := by linarith
  have hsum_nonneg :
      0 ≤ Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) +
          Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) := by positivity
  have herr : 0 ≤ eps₁ + eps₂ :=
    add_nonneg ((abs_nonneg _).trans h₁) ((abs_nonneg _).trans h₂)
  have htri :
      |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) -
       Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))| ≤
        eps₁ + eps₂ := by
    calc
      |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) -
       Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))| ≤
        |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) - y| +
        |y - Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))| :=
          abs_sub_le _ _ _
      _ = |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) - y| +
          |Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) - y| := by
        rw [abs_sub_comm y
          (Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))))]
      _ ≤ eps₁ + eps₂ := add_le_add h₁ h₂
  have hdiff :
      Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) -
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) ≤
        eps₁ + eps₂ :=
    (le_abs_self _).trans htri
  have hfactor :
      kummerSeries lam₁ (1 / (4 * alpha₁)) -
        kummerSeries lam₂ (1 / (4 * alpha₂)) =
      (Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) -
       Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))) *
      (Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) +
       Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))) := by
    nlinarith [Real.sq_sqrt hK₁, Real.sq_sqrt hK₂]
  calc
    kummerSeries lam₁ (1 / (4 * alpha₁)) -
        kummerSeries lam₂ (1 / (4 * alpha₂)) =
      (Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) -
       Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))) *
      (Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) +
       Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))) := hfactor
    _ ≤ (eps₁ + eps₂) *
      (Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) +
       Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))) :=
      mul_le_mul_of_nonneg_right hdiff hsum_nonneg
    _ ≤ (eps₁ + eps₂) *
        (2 * Real.sqrt (Real.exp (1 / (4 * a)))) :=
      mul_le_mul_of_nonneg_left hsum herr
    _ = 2 * Real.sqrt (Real.exp (1 / (4 * a))) * (eps₁ + eps₂) := by ring

/-- Coordinatewise quantitative stability of lambda and alpha
from noisy *unsquared* Gaussian-Fock scalar masses. -/
theorem kummerSeries_mixed_norm_coordinate_noisy_recovery
    (lam₁ lam₂ L alpha₁ alpha₂ a A y eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂) (hhiL : lam₂ ≤ L)
    (ha : 0 < a) (hlo₁ : a ≤ alpha₁) (hlo₂ : a ≤ alpha₂)
    (hleA : alpha₁ ≤ alpha₂) (hhiA : alpha₂ ≤ A)
    (h₁ : |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) - y| ≤ eps₁)
    (h₂ : |Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) - y| ≤ eps₂) :
    lam₂ - lam₁ ≤
      16 * A * (L + 1) ^ 2 *
        Real.sqrt (Real.exp (1 / (4 * a))) * (eps₁ + eps₂) ∧
    alpha₂ - alpha₁ ≤
      16 * (L + 1) * A ^ 2 *
        Real.sqrt (Real.exp (1 / (4 * a))) * (eps₁ + eps₂) := by
  have ha₁ : 0 < alpha₁ := lt_of_lt_of_le ha hlo₁
  have ha₂ : 0 < alpha₂ := lt_of_lt_of_le ha hlo₂
  have hHorder : kummerSeries lam₂ (1 / (4 * alpha₂)) ≤
      kummerSeries lam₁ (1 / (4 * alpha₁)) :=
    kummerSeries_mixed_antitone
      lam₁ lam₂ alpha₁ alpha₂ hlam₁ hleL ha₁ ha₂ hleA
  have hgap := kummerSeries_mixed_norm_energy_gap_from_observation
    lam₁ lam₂ alpha₁ alpha₂ a y eps₁ eps₂
    hlam₁ hleL ha hlo₁ hlo₂ hleA h₁ h₂
  have hfit₁ :
      |kummerSeries lam₁ (1 / (4 * alpha₁)) -
       kummerSeries lam₂ (1 / (4 * alpha₂))| ≤
      2 * Real.sqrt (Real.exp (1 / (4 * a))) *
        (eps₁ + eps₂) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hHorder)]
    exact hgap
  have hfit₂ :
      |kummerSeries lam₂ (1 / (4 * alpha₂)) -
       kummerSeries lam₂ (1 / (4 * alpha₂))| ≤ (0 : ℝ) := by simp
  have hresult := kummerSeries_mixed_coordinate_noisy_recovery
    lam₁ lam₂ L alpha₁ alpha₂ A
    (kummerSeries lam₂ (1 / (4 * alpha₂)))
    (2 * Real.sqrt (Real.exp (1 / (4 * a))) * (eps₁ + eps₂)) 0
    hlam₁ hleL hhiL ha₁ ha₂ hleA hhiA hfit₁ hfit₂
  constructor
  · calc
      lam₂ - lam₁ ≤
        8 * A * (L + 1) ^ 2 *
          (2 * Real.sqrt (Real.exp (1 / (4 * a))) *
            (eps₁ + eps₂) + 0) := hresult.1
      _ = 16 * A * (L + 1) ^ 2 *
          Real.sqrt (Real.exp (1 / (4 * a))) * (eps₁ + eps₂) := by ring
  · calc
      alpha₂ - alpha₁ ≤
        8 * (L + 1) * A ^ 2 *
          (2 * Real.sqrt (Real.exp (1 / (4 * a))) *
            (eps₁ + eps₂) + 0) := hresult.2
      _ = 16 * (L + 1) * A ^ 2 *
          Real.sqrt (Real.exp (1 / (4 * a))) * (eps₁ + eps₂) := by ring

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_mixed_norm_energy_gap_from_observation
#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_mixed_norm_coordinate_noisy_recovery

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Coordinatewise stability from the *true unsquared* intrinsic
entire-Fock Hilbert–Schmidt norms, permitting unrelated complete
source Hilbert bases and distinct source L² spaces. -/
theorem C_intrinsicEntire_basisHSNorm_mixed_coordinate_noisy_recovery
    (lam₁ lam₂ L alpha₁ alpha₂ a A y eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂) (hhiL : lam₂ ≤ L)
    (ha : 0 < a) (hlo₁ : a ≤ alpha₁) (hlo₂ : a ≤ alpha₂)
    (hleA : alpha₁ ≤ alpha₂) (hhiA : alpha₂ ≤ A)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂)))
    (h₁ : |Real.sqrt (∑' i : ι₁,
        ‖C_intrinsicEntire lam₁ alpha₁ hlam₁
          (lt_of_lt_of_le ha hlo₁) (b₁ i)‖ ^ 2) - y| ≤ eps₁)
    (h₂ : |Real.sqrt (∑' i : ι₂,
        ‖C_intrinsicEntire lam₂ alpha₂
          (lt_of_lt_of_le hlam₁ hleL)
          (lt_of_lt_of_le ha hlo₂) (b₂ i)‖ ^ 2) - y| ≤ eps₂) :
    lam₂ - lam₁ ≤
      16 * A * (L + 1) ^ 2 *
        Real.sqrt (Real.exp (1 / (4 * a))) * (eps₁ + eps₂) ∧
    alpha₂ - alpha₁ ≤
      16 * (L + 1) * A ^ 2 *
        Real.sqrt (Real.exp (1 / (4 * a))) * (eps₁ + eps₂) := by
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer
    lam₁ alpha₁ hlam₁ (lt_of_lt_of_le ha hlo₁) b₁] at h₁
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer
    lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL)
      (lt_of_lt_of_le ha hlo₂) b₂] at h₂
  exact KummerCoefficients.kummerSeries_mixed_norm_coordinate_noisy_recovery
    lam₁ lam₂ L alpha₁ alpha₂ a A y eps₁ eps₂
    hlam₁ hleL hhiL ha hlo₁ hlo₂ hleA hhiA h₁ h₂

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_basisHSNorm_mixed_coordinate_noisy_recovery

end GegenbauerFock.GeneralUltrasphericalFock
