import GegenbauerFock.GegenbauerIntrinsicEntireHSBounds
import GegenbauerFock.GegenbauerIntrinsicEntireHSMonotonicity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# V007 — exact vacuum asymptotic of the genuine Gaussian Fock S₂ energy

For every fixed ultraspherical parameter λ>0, the nonregularized
Kummer function at the physical Fock argument 1/(4α) tends to one
as α→+∞. The proof uses the *certified two-sided inequality*
1 ≤ Kummer(λ,1/(4α)) ≤ exp(1/(4α)) and the elementary limit of the
reciprocal exponential argument. No asymptotic expansion is assumed.

The resulting threshold theorem is independent of the complete
source Hilbert basis. It applies to the genuine analytic Gaussian L²
transform and its intrinsic source Gram, not merely formal coefficients.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.KummerCoefficients

/-- The exact unregularized Kummer trace mass tends to the normalized
vacuum value as the Gaussian scale α tends to positive infinity. -/
theorem kummerSeries_gaussianScale_tendsto_one
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun alpha : ℝ => kummerSeries lam (1 / (4 * alpha)))
      atTop (nhds (1 : ℝ)) := by
  have harg :
      Tendsto (fun alpha : ℝ => 1 / (4 * alpha))
        atTop (nhds (0 : ℝ)) := by
    simpa only [add_zero, one_div] using
      (tendsto_mul_add_inv_atTop_nhds_zero 4 0 (by norm_num))
  have hexp :
      Tendsto (fun alpha : ℝ => Real.exp (1 / (4 * alpha)))
        atTop (nhds (1 : ℝ)) := by
    simpa only [Function.comp_def, Real.exp_zero] using
      (Real.continuous_exp.continuousAt.tendsto.comp harg)
  have hpositive : ∀ᶠ alpha : ℝ in atTop, 0 < alpha := by
    exact eventually_atTop.2 ⟨1, by intro alpha ha; linarith⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hexp
  · filter_upwards [hpositive] with alpha ha
    exact kummerSeries_ge_one lam (1 / (4 * alpha)) hlam (by positivity)
  · filter_upwards [hpositive] with alpha ha
    exact kummerSeries_le_exp lam (1 / (4 * alpha)) hlam (by positivity)

/-- The exact full analytic Hilbert–Schmidt norm expression tends
to one (the square root of the normalized vacuum energy). -/
theorem sqrt_kummerSeries_gaussianScale_tendsto_one
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto
      (fun alpha : ℝ =>
        Real.sqrt (kummerSeries lam (1 / (4 * alpha))))
      atTop (nhds (1 : ℝ)) := by
  simpa only [Function.comp_def, Real.sqrt_one] using
    (Real.continuous_sqrt.continuousAt.tendsto.comp
      (kummerSeries_gaussianScale_tendsto_one lam hlam))

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_gaussianScale_tendsto_one
#print axioms GegenbauerFock.KummerCoefficients.sqrt_kummerSeries_gaussianScale_tendsto_one

end GegenbauerFock.KummerCoefficients

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Uniform over *all* complete ultraspherical source Hilbert bases:
for every positive tolerance, all sufficiently large Gaussian scales
have intrinsic entire-Fock S₂ energies in [1,1+ε). -/
theorem C_intrinsicEntire_HS_vacuum_limit_uniform_bases
    (lam : ℝ) (hlam : 0 < lam)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ A : ℝ, ∀ alpha : ℝ, A ≤ alpha → ∀ ha : 0 < alpha,
      ∀ {ι : Type*}
        (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))),
        (1 : ℝ) ≤
          (∑' i : ι, ‖C_intrinsicEntire lam alpha hlam ha (b i)‖ ^ 2) ∧
        (∑' i : ι, ‖C_intrinsicEntire lam alpha hlam ha (b i)‖ ^ 2) <
          1 + eps := by
  have hlim := KummerCoefficients.kummerSeries_gaussianScale_tendsto_one lam hlam
  have hwindow : Set.Iio (1 + eps) ∈ nhds (1 : ℝ) :=
    isOpen_Iio.mem_nhds (show (1 : ℝ) < 1 + eps by linarith)
  obtain ⟨A, hA⟩ := eventually_atTop.1 (hlim.eventually hwindow)
  refine ⟨A, ?_⟩
  intro alpha hAlpha ha ι b
  have ht : 0 ≤ (1 / (4 * alpha) : ℝ) := by positivity
  constructor
  · rw [C_intrinsicEntire_HS_energy_eq_kummer lam alpha hlam ha b]
    exact KummerCoefficients.kummerSeries_ge_one
      lam (1 / (4 * alpha)) hlam ht
  · calc
      (∑' i : ι, ‖C_intrinsicEntire lam alpha hlam ha (b i)‖ ^ 2) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
          C_intrinsicEntire_HS_energy_eq_kummer lam alpha hlam ha b
      _ < 1 + eps := hA alpha hAlpha

/-- The *actual* intrinsic holomorphic Gaussian Fock source Gram
diagonal trace satisfies the same basis-independent vacuum asymptotic. -/
theorem C_intrinsicEntire_Gram_trace_vacuum_limit_uniform_bases
    (lam : ℝ) (hlam : 0 < lam)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ A : ℝ, ∀ alpha : ℝ, A ≤ alpha → ∀ ha : 0 < alpha,
      ∀ {ι : Type*}
        (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))),
        (1 : ℝ) ≤
          (∑' i : ι,
            RCLike.re (inner ℂ
              (C_intrinsicEntire_gram lam alpha hlam ha (b i)) (b i))) ∧
        (∑' i : ι,
          RCLike.re (inner ℂ
            (C_intrinsicEntire_gram lam alpha hlam ha (b i)) (b i))) <
          1 + eps := by
  obtain ⟨A, hA⟩ :=
    C_intrinsicEntire_HS_vacuum_limit_uniform_bases lam hlam eps heps
  refine ⟨A, ?_⟩
  intro alpha hAlpha ha ι b
  have hbound := hA alpha hAlpha ha b
  rw [C_intrinsicEntire_HS_energy_eq_kummer lam alpha hlam ha b] at hbound
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer lam alpha hlam ha b]
  exact hbound

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_vacuum_limit_uniform_bases
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_vacuum_limit_uniform_bases

end GegenbauerFock.GeneralUltrasphericalFock
