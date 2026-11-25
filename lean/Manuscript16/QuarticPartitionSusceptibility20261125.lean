import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Manuscript 16, Proposition 15.1 (`prop:cross-suscept16`): quartic partition susceptibility

Source: `16.tex` of `Manuscript_16_20261125_CROSS_CONNECTIONS.zip`, Section 15,
labels `eq:cross-law16`, `eq:cross-logder16`, `eq:cross-loghess16`, `eq:cross-ode16`.

`F_crit` is the function of Manuscript 12 (`12.tex` of
`Manuscript_12_20261125_CROSS_CONNECTIONS.zip`, line 2637):
`F_crit(λ) = (1 / (2√π)) ∫_ℝ du / exp(u⁴/40 + 6λu²)`.
-/

open Real MeasureTheory Filter Set
open scoped Topology

namespace Manuscript16.QuarticPartition20261125

/-- The quartic potential `u⁴/40 + 6λu²`. -/
noncomputable def V (lam u : ℝ) : ℝ := u ^ 4 / 40 + 6 * lam * u ^ 2

/-- Unnormalised moments `m_k(λ) = ∫ u^k exp(-(u⁴/40 + 6λu²)) du`. -/
noncomputable def mom (k : ℕ) (lam : ℝ) : ℝ := ∫ u, u ^ k * exp (-V lam u)

/-- `F_crit(λ) = (1/(2√π)) ∫ exp(-(u⁴/40 + 6λu²)) du` (Manuscript 12, line 2637). -/
noncomputable def Fcrit (lam : ℝ) : ℝ := (1 / (2 * √π)) * ∫ u, 1 / exp (V lam u)

lemma Fcrit_eq (lam : ℝ) : Fcrit lam = mom 0 lam / (2 * √π) := by
  unfold Fcrit mom
  simp only [pow_zero, one_mul, one_div, Real.exp_neg]
  ring

/-- Elementary quartic–Gaussian domination: `-u⁴/40 + c u² ≤ 10 (c+1)² - u²`. -/
lemma quartic_le (c u : ℝ) : -(u ^ 4 / 40) + c * u ^ 2 ≤ 10 * (c + 1) ^ 2 - u ^ 2 := by
  nlinarith [sq_nonneg (u ^ 2 - 20 * (c + 1))]

/-- `|u|^k exp(-u⁴/40 + c u²)` is integrable for every real `c`. -/
lemma integrable_abs_pow_mul_exp (k : ℕ) (c : ℝ) :
    Integrable (fun u : ℝ => |u| ^ k * exp (-(u ^ 4 / 40) + c * u ^ 2)) := by
  have hG : Integrable (fun u : ℝ => u ^ (k : ℝ) * exp (-1 * u ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq one_pos (by have := k.cast_nonneg (α := ℝ); linarith)
  have hG' : Integrable (fun u : ℝ => exp (10 * (c + 1) ^ 2) * ‖u ^ (k : ℝ) * exp (-1 * u ^ 2)‖) :=
    hG.norm.const_mul _
  refine hG'.mono' (by fun_prop) (Eventually.of_forall fun u => ?_)
  have hpow : u ^ (k : ℝ) = u ^ k := Real.rpow_natCast u k
  rw [hpow, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_abs,
    abs_of_pos (exp_pos _), abs_of_pos (exp_pos _)]
  have h1 : exp (-(u ^ 4 / 40) + c * u ^ 2) ≤ exp (10 * (c + 1) ^ 2) * exp (-1 * u ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [quartic_le c u])
  calc |u| ^ k * exp (-(u ^ 4 / 40) + c * u ^ 2)
      ≤ |u| ^ k * (exp (10 * (c + 1) ^ 2) * exp (-1 * u ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = exp (10 * (c + 1) ^ 2) * (|u| ^ k * exp (-1 * u ^ 2)) := by ring
    _ = exp (10 * (c + 1) ^ 2) * (|u ^ k| * exp (-1 * u ^ 2)) := by rw [abs_pow]

lemma neg_V (lam u : ℝ) : -V lam u = -(u ^ 4 / 40) + (-6 * lam) * u ^ 2 := by
  unfold V; ring

/-- Every moment integrand is integrable. -/
lemma integrable_mom (k : ℕ) (lam : ℝ) :
    Integrable (fun u : ℝ => u ^ k * exp (-V lam u)) := by
  refine (integrable_abs_pow_mul_exp k (-6 * lam)).mono' (by unfold V; fun_prop)
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (exp_pos _), neg_V]

lemma hasDerivAt_exp_negV (lam u : ℝ) :
    HasDerivAt (fun l => exp (-V l u)) (-(6 * u ^ 2) * exp (-V lam u)) lam := by
  have h : HasDerivAt (fun l => -V l u) (-(6 * u ^ 2)) lam := by
    have e : (fun l => -V l u) = fun l => -(6 * u ^ 2) * l + -(u ^ 4 / 40) := by
      funext l; unfold V; ring
    rw [e]
    simpa using ((hasDerivAt_id lam).const_mul (-(6 * u ^ 2))).add_const (-(u ^ 4 / 40))
  simpa [mul_comm] using h.exp

/-- Differentiation under the integral sign: `m_k' = -6 m_{k+2}`. -/
theorem hasDerivAt_mom (k : ℕ) (lam : ℝ) :
    HasDerivAt (mom k) (-6 * mom (k + 2) lam) lam := by
  set c : ℝ := 6 * (|lam| + 1)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun l u => u ^ k * exp (-V l u))
    (F' := fun l u => u ^ k * (-(6 * u ^ 2) * exp (-V l u)))
    (bound := fun u => 6 * (|u| ^ (k + 2) * exp (-(u ^ 4 / 40) + c * u ^ 2)))
    (x₀ := lam) (s := Metric.ball lam 1) (Metric.ball_mem_nhds lam one_pos)
    (Eventually.of_forall fun l => (integrable_mom k l).aestronglyMeasurable)
    (integrable_mom k lam) (by unfold V; fun_prop) ?_
    ((integrable_abs_pow_mul_exp (k + 2) c).const_mul 6) ?_
  · refine (key.2.congr_deriv ?_)
    unfold mom
    rw [← integral_const_mul]
    congr 1; funext u; ring
  · refine Eventually.of_forall fun u l hl => ?_
    rw [Metric.mem_ball, Real.dist_eq] at hl
    have hl' : -6 * l ≤ c := by
      have : |l| ≤ |lam| + 1 := by
        have := abs_sub_abs_le_abs_sub l lam; linarith
      simp only [c]; nlinarith [neg_abs_le l]
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_mul, abs_neg, abs_of_pos (exp_pos _),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 6 * u ^ 2), neg_V]
    have he : exp (-(u ^ 4 / 40) + -6 * l * u ^ 2) ≤ exp (-(u ^ 4 / 40) + c * u ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])
    have hu2 : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
    calc |u| ^ k * (6 * u ^ 2 * exp (-(u ^ 4 / 40) + -6 * l * u ^ 2))
        ≤ |u| ^ k * (6 * u ^ 2 * exp (-(u ^ 4 / 40) + c * u ^ 2)) := by gcongr
      _ = 6 * (|u| ^ (k + 2) * exp (-(u ^ 4 / 40) + c * u ^ 2)) := by rw [hu2]; ring
  · exact Eventually.of_forall fun u l _ => (hasDerivAt_exp_negV l u).const_mul (u ^ k)

lemma mom_pos (lam : ℝ) : 0 < mom 0 lam := by
  unfold mom
  simp only [pow_zero, one_mul]
  exact integral_exp_pos (by simpa using integrable_mom 0 lam)

lemma Fcrit_pos (lam : ℝ) : 0 < Fcrit lam := by
  rw [Fcrit_eq]; exact div_pos (mom_pos lam) (by positivity)

/-- Integration by parts of `d/du [u exp(-V)]` on the line:
`m₀ = m₄/10 + 12 λ m₂`. -/
theorem mom_ibp (lam : ℝ) : mom 0 lam = mom 4 lam / 10 + 12 * lam * mom 2 lam := by
  have hderiv : ∀ u : ℝ, HasDerivAt (fun x => x * exp (-V lam x))
      (exp (-V lam u) - (1 / 10) * (u ^ 4 * exp (-V lam u))
        - 12 * lam * (u ^ 2 * exp (-V lam u))) u := by
    intro u
    have hV : HasDerivAt (fun x => -V lam x) (-(u ^ 3 / 10 + 12 * lam * u)) u := by
      have e : (fun x => -V lam x) = fun x => -(x ^ 4 / 40 + 6 * lam * x ^ 2) := by
        funext x; rfl
      rw [e]
      have h4 := (hasDerivAt_pow 4 u).div_const 40
      have h2 := (hasDerivAt_pow 2 u).const_mul (6 * lam)
      refine (h4.add h2).neg.congr_deriv ?_
      norm_num
      ring
    refine ((hasDerivAt_id u).mul hV.exp).congr_deriv ?_
    simp only [id]; ring
  have h0 : Integrable (fun u => exp (-V lam u)) := by simpa using integrable_mom 0 lam
  have h4 : Integrable (fun u => (1 / 10) * (u ^ 4 * exp (-V lam u))) :=
    (integrable_mom 4 lam).const_mul _
  have h2 : Integrable (fun u => 12 * lam * (u ^ 2 * exp (-V lam u))) :=
    (integrable_mom 2 lam).const_mul _
  have h04 : Integrable (fun u => exp (-V lam u) - (1 / 10) * (u ^ 4 * exp (-V lam u))) :=
    h0.sub h4
  have hf' : Integrable (fun u => exp (-V lam u) - (1 / 10) * (u ^ 4 * exp (-V lam u))
        - 12 * lam * (u ^ 2 * exp (-V lam u))) := h04.sub h2
  have hf : Integrable (fun u => u * exp (-V lam u)) := by simpa using integrable_mom 1 lam
  have h := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hf' hf
  rw [integral_sub h04 h2, integral_sub h0 h4, integral_const_mul, integral_const_mul] at h
  unfold mom
  simp only [pow_zero, one_mul]
  linarith

/-- First derivative: `F_crit' = -6 m₂ / (2√π)`. -/
theorem hasDerivAt_Fcrit (lam : ℝ) :
    HasDerivAt Fcrit (-6 * mom 2 lam / (2 * √π)) lam := by
  have e : Fcrit = fun l => mom 0 l / (2 * √π) := funext Fcrit_eq
  rw [e]
  exact (hasDerivAt_mom 0 lam).div_const _

theorem deriv_Fcrit : deriv Fcrit = fun lam => -6 * mom 2 lam / (2 * √π) :=
  funext fun lam => (hasDerivAt_Fcrit lam).deriv

/-- Second derivative: `F_crit'' = 36 m₄ / (2√π)`. -/
theorem hasDerivAt_deriv_Fcrit (lam : ℝ) :
    HasDerivAt (deriv Fcrit) (36 * mom 4 lam / (2 * √π)) lam := by
  rw [deriv_Fcrit]
  convert ((hasDerivAt_mom 2 lam).const_mul (-6)).div_const (2 * √π) using 1
  ring

/-- **`eq:cross-ode16`**: `F_crit'' - 720 λ F_crit' - 360 F_crit = 0`. -/
theorem Fcrit_ode (lam : ℝ) :
    deriv (deriv Fcrit) lam - 720 * lam * deriv Fcrit lam - 360 * Fcrit lam = 0 := by
  rw [(hasDerivAt_deriv_Fcrit lam).deriv, (hasDerivAt_Fcrit lam).deriv, Fcrit_eq,
    mom_ibp lam]
  have : (2 * √π) ≠ 0 := by positivity
  field_simp
  ring

/-! ## The law `η_λ` of `eq:cross-law16` -/

/-- Density of `η_λ`, written as in `eq:cross-law16`: `1 / (2√π F_crit(λ) exp(u⁴/40 + 6λu²))`. -/
noncomputable def density (lam u : ℝ) : ℝ := 1 / (2 * √π * Fcrit lam * exp (V lam u))

lemma density_eq (lam u : ℝ) : density lam u = exp (-V lam u) / mom 0 lam := by
  unfold density
  rw [Fcrit_eq, Real.exp_neg]
  have h0 : mom 0 lam ≠ 0 := (mom_pos lam).ne'
  have hs : (2 * √π) ≠ 0 := by positivity
  field_simp

lemma density_nonneg (lam u : ℝ) : 0 ≤ density lam u := by
  rw [density_eq]; exact div_nonneg (exp_pos _).le (mom_pos lam).le

lemma continuous_density (lam : ℝ) : Continuous (density lam) := by
  have : density lam = fun u => exp (-V lam u) / mom 0 lam := funext (density_eq lam)
  rw [this]; unfold V; fun_prop

/-- **`eq:cross-law16`**: `dη_λ(u) = du / (2√π F_crit(λ) exp(u⁴/40 + 6λu²))`. -/
noncomputable def eta (lam : ℝ) : Measure ℝ :=
  volume.withDensity fun u => ENNReal.ofReal (density lam u)

/-- Integrals against `η_λ` are integrals against its density. -/
theorem integral_eta (lam : ℝ) (g : ℝ → ℝ) :
    ∫ u, g u ∂(eta lam) = (∫ u, g u * exp (-V lam u)) / mom 0 lam := by
  unfold eta
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun u => ENNReal.ofReal (density lam u))
    (continuous_density lam).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_div]
  congr 1; funext u
  rw [ENNReal.toReal_ofReal (density_nonneg lam u), density_eq, smul_eq_mul]
  ring

/-- `η_λ` is a probability measure. -/
instance isProbabilityMeasure_eta (lam : ℝ) : IsProbabilityMeasure (eta lam) := by
  constructor
  unfold eta
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · have : ∫ u, density lam u = 1 := by
      simp_rw [density_eq]
      rw [integral_div]
      have := mom_pos lam
      unfold mom at this ⊢
      simp only [pow_zero, one_mul] at this ⊢
      exact div_self this.ne'
    rw [this, ENNReal.ofReal_one]
  · have : Integrable (fun u => exp (-V lam u) / mom 0 lam) :=
      (by simpa using integrable_mom 0 lam : Integrable fun u => exp (-V lam u)).div_const _
    simpa only [← density_eq] using this
  · exact Eventually.of_forall (density_nonneg lam)

lemma integral_eta_pow (lam : ℝ) (k : ℕ) :
    ∫ u, u ^ k ∂(eta lam) = mom k lam / mom 0 lam := by
  rw [integral_eta]; rfl

/-- **`eq:cross-logder16`**: `(log F_crit)'(λ) = -6 ∫ u² dη_λ`. -/
theorem hasDerivAt_log_Fcrit (lam : ℝ) :
    HasDerivAt (fun l => Real.log (Fcrit l)) (-6 * ∫ u, u ^ 2 ∂(eta lam)) lam := by
  refine ((hasDerivAt_Fcrit lam).log (Fcrit_pos lam).ne').congr_deriv ?_
  rw [integral_eta_pow, Fcrit_eq]
  have h0 : mom 0 lam ≠ 0 := (mom_pos lam).ne'
  have hs : (2 * √π) ≠ 0 := by positivity
  field_simp

theorem deriv_log_Fcrit :
    deriv (fun l => Real.log (Fcrit l)) = fun lam => -6 * (mom 2 lam / mom 0 lam) := by
  funext lam
  rw [(hasDerivAt_log_Fcrit lam).deriv, integral_eta_pow]

/-- `Var_{η_λ}(u²)`. -/
noncomputable def varEta (lam : ℝ) : ℝ :=
  ∫ u, (u ^ 2 - ∫ v, v ^ 2 ∂(eta lam)) ^ 2 ∂(eta lam)

lemma varEta_eq (lam : ℝ) :
    varEta lam = mom 4 lam / mom 0 lam - (mom 2 lam / mom 0 lam) ^ 2 := by
  unfold varEta
  rw [integral_eta_pow, integral_eta]
  set a := mom 2 lam / mom 0 lam
  have hexp : (fun u => (u ^ 2 - a) ^ 2 * exp (-V lam u)) =
      fun u => u ^ 4 * exp (-V lam u) - 2 * a * (u ^ 2 * exp (-V lam u))
        + a ^ 2 * (u ^ 0 * exp (-V lam u)) := by
    funext u; ring
  have i4 := integrable_mom 4 lam
  have i2 : Integrable (fun u => 2 * a * (u ^ 2 * exp (-V lam u))) :=
    (integrable_mom 2 lam).const_mul _
  have i0 : Integrable (fun u => a ^ 2 * (u ^ 0 * exp (-V lam u))) :=
    (integrable_mom 0 lam).const_mul _
  have i42 : Integrable (fun u => u ^ 4 * exp (-V lam u) - 2 * a * (u ^ 2 * exp (-V lam u))) :=
    i4.sub i2
  rw [hexp, integral_add i42 i0, integral_sub i4 i2, integral_const_mul, integral_const_mul]
  change (mom 4 lam - 2 * a * mom 2 lam + a ^ 2 * mom 0 lam) / mom 0 lam = _
  have h0 : mom 0 lam ≠ 0 := (mom_pos lam).ne'
  simp only [a]
  field_simp
  ring

/-- The variance is strictly positive: the density is positive and `u²` is not constant. -/
theorem varEta_pos (lam : ℝ) : 0 < varEta lam := by
  unfold varEta
  rw [integral_eta]
  refine div_pos ?_ (mom_pos lam)
  set a := ∫ v, v ^ 2 ∂(eta lam)
  have hint : Integrable (fun u => (u ^ 2 - a) ^ 2 * exp (-V lam u)) := by
    have hexp : (fun u => (u ^ 2 - a) ^ 2 * exp (-V lam u)) =
        fun u => u ^ 4 * exp (-V lam u) - 2 * a * (u ^ 2 * exp (-V lam u))
          + a ^ 2 * (u ^ 0 * exp (-V lam u)) := by
      funext u; ring
    rw [hexp]
    exact ((integrable_mom 4 lam).sub ((integrable_mom 2 lam).const_mul _)).add
      ((integrable_mom 0 lam).const_mul _)
  rw [integral_pos_iff_support_of_nonneg (fun u => by positivity) hint]
  have hsub : Ioi (|a| + 1) ⊆ Function.support (fun u => (u ^ 2 - a) ^ 2 * exp (-V lam u)) := by
    intro u hu
    rw [mem_Ioi] at hu
    rw [Function.mem_support]
    have h1 : 1 ≤ u := by linarith [abs_nonneg a]
    have h2 : a < u ^ 2 := by nlinarith [le_abs_self a]
    exact mul_ne_zero (pow_ne_zero 2 (by linarith)) (exp_pos _).ne'
  calc (0 : ENNReal) < volume (Ioi (|a| + 1)) := by rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top
    _ ≤ _ := measure_mono hsub

/-- **`eq:cross-loghess16`**: `(log F_crit)''(λ) = 36 Var_{η_λ}(u²) > 0`. -/
theorem hasDerivAt_deriv_log_Fcrit (lam : ℝ) :
    HasDerivAt (deriv fun l => Real.log (Fcrit l)) (36 * varEta lam) lam := by
  rw [deriv_log_Fcrit]
  have h0 : mom 0 lam ≠ 0 := (mom_pos lam).ne'
  refine (((hasDerivAt_mom 2 lam).div (hasDerivAt_mom 0 lam) h0).const_mul (-6)).congr_deriv ?_
  rw [varEta_eq]
  field_simp
  ring

theorem cross_loghess16 (lam : ℝ) :
    deriv (deriv fun l => Real.log (Fcrit l)) lam = 36 * varEta lam ∧ 0 < 36 * varEta lam :=
  ⟨(hasDerivAt_deriv_log_Fcrit lam).deriv, by have := varEta_pos lam; positivity⟩

end Manuscript16.QuarticPartition20261125

#print axioms Manuscript16.QuarticPartition20261125.integrable_mom
#print axioms Manuscript16.QuarticPartition20261125.hasDerivAt_mom
#print axioms Manuscript16.QuarticPartition20261125.Fcrit_pos
#print axioms Manuscript16.QuarticPartition20261125.mom_ibp
#print axioms Manuscript16.QuarticPartition20261125.Fcrit_ode
#print axioms Manuscript16.QuarticPartition20261125.isProbabilityMeasure_eta
#print axioms Manuscript16.QuarticPartition20261125.integral_eta
#print axioms Manuscript16.QuarticPartition20261125.hasDerivAt_log_Fcrit
#print axioms Manuscript16.QuarticPartition20261125.varEta_eq
#print axioms Manuscript16.QuarticPartition20261125.varEta_pos
#print axioms Manuscript16.QuarticPartition20261125.hasDerivAt_deriv_log_Fcrit
#print axioms Manuscript16.QuarticPartition20261125.cross_loghess16
