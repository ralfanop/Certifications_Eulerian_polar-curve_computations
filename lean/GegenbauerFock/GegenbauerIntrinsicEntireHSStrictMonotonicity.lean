import GegenbauerFock.GegenbauerIntrinsicEntireHSMonotonicity
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# V007 — strict Gaussian-width ordering of true entire-Fock S₂ energy

For positive ultraspherical λ, the coefficient of order n=1 in the
unregularized Kummer expansion is strictly positive. Consequently,
termwise monotonicity becomes strictly positive under s<t, even if s=0.

Since the physical Gaussian parameter is t=1/(4α), strictly increasing
α strictly lowers the *full analytic* entire-Fock Hilbert–Schmidt energy
and the basis-independent intrinsic source-Gram diagonal trace.
This statement does not equate operators between different Gaussian
Fock target spaces: it compares their scalar invariant energies.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- The unregularized Kummer function is strictly increasing on
nonnegative real arguments, witnessed by its positive n=1 term. -/
theorem kummerSeries_strictMono_nonneg
    (lam s t : ℝ) (hlam : 0 < lam) (hs : 0 ≤ s) (hst : s < t) :
    kummerSeries lam s < kummerSeries lam t := by
  have ht : 0 ≤ t := le_trans hs hst.le
  have hc : 0 < ratio lam 1 := by
    have heq : ratio lam 1 = (1 / 2 : ℝ) / (lam + 1) := by
      simp [ratio_succ, ratio_zero]
    rw [heq]
    exact div_pos (by norm_num) (by linarith)
  have hnonneg (n : ℕ) :
      0 ≤ ratio lam n * (s ^ n / (Nat.factorial n : ℝ)) :=
    mul_nonneg (ratio_nonneg lam hlam n) (by positivity)
  have hterms (n : ℕ) :
      ratio lam n * (s ^ n / (Nat.factorial n : ℝ)) ≤
      ratio lam n * (t ^ n / (Nat.factorial n : ℝ)) := by
    have hpow : s ^ n ≤ t ^ n := by gcongr
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hpow (by positivity))
      (ratio_nonneg lam hlam n)
  have hfirst :
      ratio lam 1 * (s ^ 1 / (Nat.factorial 1 : ℝ)) <
      ratio lam 1 * (t ^ 1 / (Nat.factorial 1 : ℝ)) := by
    simpa using (mul_lt_mul_of_pos_left hst hc)
  unfold kummerSeries
  exact Summable.tsum_lt_tsum_of_nonneg (i := 1)
    hnonneg hterms hfirst (kummerSeries_summable lam t hlam ht)

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_strictMono_nonneg

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Strict increase in Gaussian width lowers the genuine entire
Gaussian Fock Hilbert–Schmidt energy for every complete source basis. -/
theorem C_intrinsicEntire_HS_energy_strictAnti_alpha
    (lam alpha₁ alpha₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (halpha : alpha₁ < alpha₂)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (∑' i : ι, ‖C_intrinsicEntire lam alpha₂ hlam ha₂ (b i)‖ ^ 2) <
      (∑' i : ι, ‖C_intrinsicEntire lam alpha₁ hlam ha₁ (b i)‖ ^ 2) := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer lam alpha₂ hlam ha₂ b,
    C_intrinsicEntire_HS_energy_eq_kummer lam alpha₁ hlam ha₁ b]
  have hscale : (4 * alpha₁ : ℝ) < 4 * alpha₂ := by nlinarith
  have ht : (0 : ℝ) ≤ 1 / (4 * alpha₂) := by positivity
  have hparam : (1 / (4 * alpha₂) : ℝ) < 1 / (4 * alpha₁) :=
    one_div_lt_one_div_of_lt (by positivity) hscale
  exact KummerCoefficients.kummerSeries_strictMono_nonneg
    lam (1 / (4 * alpha₂)) (1 / (4 * alpha₁)) hlam ht hparam

/-- The genuine intrinsic holomorphic Gaussian source-Gram diagonal
trace is strictly decreasing as α strictly increases. -/
theorem C_intrinsicEntire_Gram_trace_strictAnti_alpha
    (lam alpha₁ alpha₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (halpha : alpha₁ < alpha₂)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (∑' i : ι, RCLike.re (inner ℂ
      (C_intrinsicEntire_gram lam alpha₂ hlam ha₂ (b i)) (b i))) <
    (∑' i : ι, RCLike.re (inner ℂ
      (C_intrinsicEntire_gram lam alpha₁ hlam ha₁ (b i)) (b i))) := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer lam alpha₂ hlam ha₂ b,
    C_intrinsicEntire_Gram_basis_trace_eq_kummer lam alpha₁ hlam ha₁ b]
  have hscale : (4 * alpha₁ : ℝ) < 4 * alpha₂ := by nlinarith
  have ht : (0 : ℝ) ≤ 1 / (4 * alpha₂) := by positivity
  have hparam : (1 / (4 * alpha₂) : ℝ) < 1 / (4 * alpha₁) :=
    one_div_lt_one_div_of_lt (by positivity) hscale
  exact KummerCoefficients.kummerSeries_strictMono_nonneg
    lam (1 / (4 * alpha₂)) (1 / (4 * alpha₁)) hlam ht hparam

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_strictAnti_alpha
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_strictAnti_alpha

end GegenbauerFock.GeneralUltrasphericalFock
