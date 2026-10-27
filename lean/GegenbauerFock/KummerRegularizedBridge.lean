import GegenbauerFock.UltrasphericalKummerBridge
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# V007: Mathlib's regularized complex confluent hypergeometric function

The unregularized Kummer {}_1 F_1(a;b;z) is NOT Mathlib's
`Complex.regularizedHGFun {a} {b} z`. The exact conversion factor is
`Complex.Gamma b`. This file relates the true ultraspherical moment
quotients to Mathlib's actual regularized hypergeometric coefficients,
and then identifies the *whole* complex function on the real axis.

Parameters: a=1/2, b=λ+1, λ>0. No hidden Gamma regularization.
-/

namespace GegenbauerFock.KummerCoefficients

open Complex Polynomial

private noncomputable def kummerA : ℂ := 1 / 2

private noncomputable def kummerB (lam : ℝ) : ℂ := ((lam + 1 : ℝ) : ℂ)

/-- The actual Mathlib complex regularized hypergeometric function with
the Eulerian ultraspherical parameters (1/2; λ+1). -/
noncomputable def mathlibRegularizedKummer (lam : ℝ) (z : ℂ) : ℂ :=
  Complex.regularizedHGFun ({kummerA} : Multiset ℂ)
    ({kummerB lam} : Multiset ℂ) z

/-- Real Pochhammer coefficients become exactly complex Pochhammer
coefficients after the usual inclusion ℝ → ℂ. -/
private theorem pochhammer_ofReal (n : ℕ) (x : ℝ) :
    (((ascPochhammer ℝ n).eval x : ℝ) : ℂ) =
      (ascPochhammer ℂ n).eval (x : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [ascPochhammer_succ_eval, Complex.ofReal_mul,
        Complex.ofReal_add, Complex.ofReal_natCast, ih]

/-- Gamma is nonzero at the positive real denominator parameter. -/
private theorem gamma_kummerB_ne_zero (lam : ℝ) (hlam : 0 < lam) :
    Complex.Gamma (kummerB lam) ≠ 0 := by
  apply Complex.Gamma_ne_zero_of_re_pos
  dsimp [kummerB]
  simp only [Complex.ofReal_re]
  linarith

/-- The general denominator Gamma(b+n) is nonzero. -/
private theorem gamma_kummerB_add_nat_ne_zero
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    Complex.Gamma (kummerB lam + (n : ℂ)) ≠ 0 := by
  apply Complex.Gamma_ne_zero_of_re_pos
  dsimp [kummerB]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re]
  positivity

/-- The Gamma quotient equals precisely Mathlib's complex rising
Pochhammer polynomial for b=λ+1>0. -/
private theorem gamma_quotient_eq_pochhammer
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    Complex.Gamma (kummerB lam + (n : ℂ)) /
      Complex.Gamma (kummerB lam) =
        (ascPochhammer ℂ n).eval (kummerB lam) := by
  apply Complex.Gamma_add_nat_div_Gamma_eq
  intro k hk
  have hr := congrArg Complex.re hk
  dsimp [kummerB] at hr
  simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hr
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  linarith

/-- The kernel-certified normalization at EVERY coefficient:
  Γ(λ+1) * (regularized complex hypergeometric coefficient)
       = ((1/2)_n/(λ+1)_n)/n!.
This is not a mere definition of an alternative "Kummer" symbol. -/
theorem gamma_mul_regularizedCoeff_eq_ratio
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    Complex.Gamma (kummerB lam) *
      Complex.regularizedHGFunCoeff
        ({kummerA} : Multiset ℂ) ({kummerB lam} : Multiset ℂ) n =
      (KummerCoefficients.ratio lam n : ℂ) / (Nat.factorial n : ℂ) := by
  let b := kummerB lam
  let a := kummerA
  have hg : Complex.Gamma b ≠ 0 := gamma_kummerB_ne_zero lam hlam
  have hgn : Complex.Gamma (b + (n : ℂ)) ≠ 0 :=
    gamma_kummerB_add_nat_ne_zero lam hlam n
  have hq :
      Complex.Gamma (b + (n : ℂ)) / Complex.Gamma b =
        (ascPochhammer ℂ n).eval b :=
    gamma_quotient_eq_pochhammer lam hlam n
  have hp :
      (ascPochhammer ℂ n).eval b ≠ 0 := by
    rw [← hq]
    exact div_ne_zero hgn hg
  have hf : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hr :
      (KummerCoefficients.ratio lam n : ℂ) =
        (ascPochhammer ℂ n).eval a /
          (ascPochhammer ℂ n).eval b := by
    rw [KummerCoefficients.ratio_eq_pochhammer lam hlam n]
    simp only [Complex.ofReal_div, pochhammer_ofReal]
    rfl
  change Complex.Gamma b *
      Complex.regularizedHGFunCoeff ({a} : Multiset ℂ)
        ({b} : Multiset ℂ) n = _
  rw [hr]
  simp only [Complex.regularizedHGFunCoeff,
    Multiset.map_singleton, Multiset.prod_singleton]
  rw [← hq]
  field_simp [hg, hgn, hf]
  ring

/-- For any complex z, the classical unregularized Kummer series agrees
with Gamma(b) times Mathlib's ACTUAL regularized complex function.
The identity is established at each gamma-normalized coefficient. -/
theorem gamma_mul_regularizedHGFun_eq_complexSeries
    (lam : ℝ) (hlam : 0 < lam) (z : ℂ) :
    Complex.Gamma (kummerB lam) * mathlibRegularizedKummer lam z =
      ∑' n : ℕ, (KummerCoefficients.ratio lam n : ℂ) *
        (z ^ n / (Nat.factorial n : ℂ)) := by
  unfold mathlibRegularizedKummer Complex.regularizedHGFun
    Complex.regularizedHGFunSeries
  rw [← FormalMultilinearSeries.ofScalarsSum,
    FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]
  rw [tsum_mul_left]
  apply tsum_congr
  intro n
  rw [← mul_assoc, gamma_mul_regularizedCoeff_eq_ratio lam hlam n]
  ring

/-- The genuine real Kummer ₁F₁ series is the Gamma-normalized
Mathlib complex regularized hypergeometric function on the real axis. -/
theorem kummerSeries_eq_gamma_mul_mathlibRegularized
    (lam z : ℝ) (hlam : 0 < lam) :
    (KummerCoefficients.kummerSeries lam z : ℂ) =
      Complex.Gamma (kummerB lam) *
        mathlibRegularizedKummer lam (z : ℂ) := by
  rw [gamma_mul_regularizedHGFun_eq_complexSeries lam hlam]
  unfold KummerCoefficients.kummerSeries
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp only [Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_natCast]

#print axioms GegenbauerFock.KummerCoefficients.gamma_mul_regularizedCoeff_eq_ratio
#print axioms GegenbauerFock.KummerCoefficients.gamma_mul_regularizedHGFun_eq_complexSeries
#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_eq_gamma_mul_mathlibRegularized

end GegenbauerFock.KummerCoefficients

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Exact Gamma-normalized Mathlib complex hypergeometric evaluation
of the actual infinite-dimensional Gegenbauer--Fock HS energy,
without confusing regularized and unregularized ₁F₁. -/
theorem rowEnergy_eq_mathlibRegularizedKummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (rowEnergy lam alpha hlam ha : ℂ) =
      Complex.Gamma (((lam + 1 : ℝ) : ℂ)) *
        KummerCoefficients.mathlibRegularizedKummer lam
          (((1 / (4 * alpha) : ℝ) : ℂ)) := by
  rw [rowEnergy_eq_kummerSeries lam alpha hlam ha]
  exact KummerCoefficients.kummerSeries_eq_gamma_mul_mathlibRegularized
    lam (1 / (4 * alpha)) hlam

#print axioms GegenbauerFock.GeneralUltrasphericalFock.rowEnergy_eq_mathlibRegularizedKummer

end GegenbauerFock.GeneralUltrasphericalFock
