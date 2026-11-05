import GegenbauerFock.GegenbauerIntrinsicEntireHSBounds
import GegenbauerFock.UltrasphericalGammaKummerComplete
import Mathlib.Topology.Algebra.Order.Field

/-!
# V007 — narrow Gaussian Fock trace diverges on the positive scale

For λ>0, the exact unregularized Kummer Hilbert–Schmidt energy
K(λ,1/(4α)) tends to +∞ as α→0 through positive values.

The proof is a genuine filter-level limit, not an isolated unboundedness
witness. Its only growth input is the independently certified positive
first excited coefficient in the true Kummer series. The divergence
transfers to the actual Gamma-density exponential integral, which
equals the exact intrinsic entire-Fock S₂ energy / source-Gram trace
on every complete ultraspherical input basis.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace GegenbauerFock.KummerCoefficients

/-- As the positive Gaussian scale shrinks to zero, the unregularized
ultraspherical Kummer mass tends to positive infinity. -/
theorem kummerSeries_gaussianScale_tendsto_atTop
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun alpha : ℝ => kummerSeries lam (1 / (4 * alpha)))
      (𝓝[>] (0 : ℝ)) atTop := by
  have hr : 0 < ratio lam 1 := by
    have hd : 0 < lam + 1 := by linarith
    have hquot : 0 < (1 / 2 : ℝ) / (lam + 1) :=
      div_pos (by norm_num) hd
    simpa [ratio] using hquot
  let r : ℝ := ratio lam 1 / 4
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  have hscale :
      Tendsto (fun alpha : ℝ => r * alpha⁻¹)
        (𝓝[>] (0 : ℝ)) atTop :=
    Filter.Tendsto.const_mul_atTop hrpos
      (tendsto_inv_nhdsGT_zero : Tendsto
        (fun alpha : ℝ => alpha⁻¹) (𝓝[>] (0 : ℝ)) atTop)
  have hle :
      (fun alpha : ℝ => r * alpha⁻¹) ≤ᶠ[𝓝[>] (0 : ℝ)]
        (fun alpha : ℝ => kummerSeries lam (1 / (4 * alpha))) := by
    filter_upwards [self_mem_nhdsWithin] with alpha ha
    have ha' : 0 < alpha := ha
    have hmass := kummerSeries_ge_vacuum_add_first
      lam (1 / (4 * alpha)) hlam (by positivity)
    calc
      r * alpha⁻¹ =
          ratio lam 1 * (1 / (4 * alpha)) := by
            dsimp [r]
            simp only [one_div, mul_inv_rev, div_eq_mul_inv]
            ring
      _ ≤ 1 + ratio lam 1 * (1 / (4 * alpha)) := by linarith
      _ ≤ kummerSeries lam (1 / (4 * alpha)) := hmass
  exact tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) hle hscale

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_gaussianScale_tendsto_atTop

end GegenbauerFock.KummerCoefficients

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The original real Gamma-normalized ultraspherical energy integral
diverges as α→0 through positive Gaussian scales; this is the actual
intrinsic Gaussian entire-L² Hilbert–Schmidt and Gram trace mass. -/
theorem gammaDensity_exponentialTrace_tendsto_atTop
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto
      (fun alpha : ℝ =>
        ∫ u : ℝ, Real.exp (u ^ 2 / (4 * alpha))
          ∂((volume : Measure ℝ).withDensity
            (fun u => ENNReal.ofReal (Ultraspherical.gammaDensity lam u))))
      (𝓝[>] (0 : ℝ)) atTop := by
  have hle :
      (fun alpha : ℝ =>
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) ≤ᶠ[𝓝[>] (0 : ℝ)]
      (fun alpha : ℝ =>
        ∫ u : ℝ, Real.exp (u ^ 2 / (4 * alpha))
          ∂((volume : Measure ℝ).withDensity
            (fun u => ENNReal.ofReal (Ultraspherical.gammaDensity lam u)))) := by
    filter_upwards [self_mem_nhdsWithin] with alpha ha
    exact le_of_eq
      (Ultraspherical.gammaDensity_exp_integral_eq_kummerSeries
        lam alpha hlam ha).symm
  exact tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) hle
    (KummerCoefficients.kummerSeries_gaussianScale_tendsto_atTop lam hlam)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gammaDensity_exponentialTrace_tendsto_atTop

end GegenbauerFock.GeneralUltrasphericalFock
