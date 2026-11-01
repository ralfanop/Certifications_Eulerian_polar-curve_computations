import GegenbauerFock.GegenbauerIntrinsicEntireHSKummer
import GegenbauerFock.UltrasphericalGammaKummerComplete
import GegenbauerFock.KummerPochhammer

/-!
# V007 — the intrinsic entire Gaussian Fock S₂ energy is an actual real integral

For the entire-valued Gegenbauer transform, summing true analytic
Gaussian L² norms over any complete orthonormal source basis gives the
unregularized Kummer value. This file further identifies that same
basis-independent Hilbert–Schmidt energy with the original real-line
Gamma-normalized ultraspherical exponential integral, and with its
precisely normalized Pochhammer series. No formal moment-only measure
or unproved external hypergeometric convention enters this equality.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The intrinsic entire Gaussian Fock S₂ energy equals the genuine
Gamma-density integral on the real ultraspherical source variable. -/
theorem C_intrinsicEntire_HS_energy_eq_gamma_integral
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (∑' i : ι, ‖C_intrinsicEntire lam alpha hlam ha (b i)‖ ^ 2) =
      ∫ u : ℝ, Real.exp (u ^ 2 / (4 * alpha))
        ∂((volume : Measure ℝ).withDensity
          (fun u => ENNReal.ofReal (Ultraspherical.gammaDensity lam u))) := by
  exact (C_intrinsicEntire_HS_energy_eq_kummer lam alpha hlam ha b).trans
    (Ultraspherical.gammaDensity_exp_integral_eq_kummerSeries
      lam alpha hlam ha).symm

/-- Exact unregularized Pochhammer-series evaluation of true
Gaussian entire Fock Hilbert–Schmidt energy, with the factor 1/(4α). -/
theorem C_intrinsicEntire_HS_energy_eq_pochhammer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (∑' i : ι, ‖C_intrinsicEntire lam alpha hlam ha (b i)‖ ^ 2) =
      ∑' n : ℕ,
        ((ascPochhammer ℝ n).eval (1 / 2) /
          (ascPochhammer ℝ n).eval (lam + 1)) *
          ((1 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ)) := by
  exact (C_intrinsicEntire_HS_energy_eq_kummer lam alpha hlam ha b).trans
    (KummerCoefficients.kummerSeries_eq_pochhammer
      lam (1 / (4 * alpha)) hlam)

/-- The genuine intrinsic source-Gram Hilbert diagonal trace on
every complete ultraspherical basis is the same concrete Gamma
exponential integral, not merely a formal coefficient trace. -/
theorem C_intrinsicEntire_Gram_trace_eq_gamma_integral
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (∑' i : ι,
      RCLike.re (inner ℂ
        (C_intrinsicEntire_gram lam alpha hlam ha (b i)) (b i))) =
      ∫ u : ℝ, Real.exp (u ^ 2 / (4 * alpha))
        ∂((volume : Measure ℝ).withDensity
          (fun u => ENNReal.ofReal (Ultraspherical.gammaDensity lam u))) := by
  exact (C_intrinsicEntire_Gram_basis_trace_eq_kummer lam alpha hlam ha b).trans
    (Ultraspherical.gammaDensity_exp_integral_eq_kummerSeries
      lam alpha hlam ha).symm

/-- Same intrinsic analytic source-Gram diagonal trace in the fully
specified, unregularized rising-Pochhammer Kummer convention. -/
theorem C_intrinsicEntire_Gram_trace_eq_pochhammer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (∑' i : ι,
      RCLike.re (inner ℂ
        (C_intrinsicEntire_gram lam alpha hlam ha (b i)) (b i))) =
      ∑' n : ℕ,
        ((ascPochhammer ℝ n).eval (1 / 2) /
          (ascPochhammer ℝ n).eval (lam + 1)) *
          ((1 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ)) := by
  exact (C_intrinsicEntire_Gram_basis_trace_eq_kummer lam alpha hlam ha b).trans
    (KummerCoefficients.kummerSeries_eq_pochhammer
      lam (1 / (4 * alpha)) hlam)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_eq_gamma_integral
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_eq_pochhammer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_eq_gamma_integral
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_eq_pochhammer

end GegenbauerFock.GeneralUltrasphericalFock
