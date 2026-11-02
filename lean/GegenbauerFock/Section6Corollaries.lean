import GegenbauerFock.GegenbauerIntrinsicEntireBochnerEvaluation
import GegenbauerFock.GegenbauerIntrinsicEntireHSKummer
import GegenbauerFock.AnalyticAdjointComplete
import GegenbauerFock.GaussianAreaIntrinsicMonomialEvaluation
import GegenbauerFock.GaussianAreaCoefficientRecovery
import GegenbauerFock.RationalTraceAnalyticTail
import GegenbauerFock.EulerianStateShi
import GegenbauerFock.GaussianAreaIntrinsicCompleteSpace

/-!
# Manuscript 13, Section 6: the remaining statements in the manuscript's own form

* `C_intrinsicEntire_coeff` (**Theorem 6.2**, eq. (6.3)): in the intrinsic Fock space,
  `⟨C f, e_n⟩_α = (i/2)ⁿ / √(αⁿ n!) · ∫ uⁿ f(u) dν_λ(u)` with `e_n = √(αⁿ/n!) zⁿ`.
* `C_intrinsicEntire_adjoint_ae` (**Theorem 6.3**, eq. (6.5)):
  `(C* F)(u) = F(−iu/(2α))` for `ν_λ`-almost every `u`, `F` the entire representative.
* `proposition_6_5` (**Proposition 6.5**): for `λ = 1/2`, `α = 1`, the Hilbert–Schmidt energy on
  every orthonormal basis equals `∫ e^{u²/4} dν_{1/2} = ½ ∫_{-1}^{1} e^{u²/4} du =
  ∑ 1/(4ⁿ n! (2n+1))` and lies in the stated 24-digit rational interval.

Mathlib's inner product is conjugate-linear in the first slot, so `inner (e_n) (C f)` is the
manuscript's `⟨C f, e_n⟩_α`.
-/

noncomputable section

open MeasureTheory Complex
open GegenbauerFock.GeneralUltrasphericalFock

namespace GegenbauerFock.Section6

/-- `complexWeight α n = (i/2)ⁿ / √(αⁿ n!)`. -/
theorem complexWeight_eq (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    WeightedMoments.complexWeight alpha n =
      (I / 2) ^ n / ((Real.sqrt (alpha ^ n * (n.factorial : ℝ)) : ℝ) : ℂ) := by
  have hpos : 0 < alpha ^ n * (n.factorial : ℝ) := by positivity
  have hsq : 0 < Real.sqrt (alpha ^ n * (n.factorial : ℝ)) := Real.sqrt_pos.2 hpos
  have hsw : WeightedMoments.squareWeight alpha n =
      ((1 / 2) ^ n / Real.sqrt (alpha ^ n * (n.factorial : ℝ))) ^ 2 := by
    have h4 : (4 : ℝ) ^ n = (2 ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [div_pow, Real.sq_sqrt hpos.le]
    unfold WeightedMoments.squareWeight
    have hh : ((1 : ℝ) / 2) ^ n = 1 / 2 ^ n := by rw [div_pow, one_pow]
    rw [div_pow, one_pow, mul_pow, h4, div_div, mul_assoc, hh, div_pow, one_pow, div_div]
  unfold WeightedMoments.complexWeight
  rw [hsw, Real.sqrt_sq (by positivity)]
  push_cast
  ring

/-- **Theorem 6.2**, coefficient formula (6.3), in the intrinsic Fock space. -/
theorem C_intrinsicEntire_coeff (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) (n : ℕ) :
    inner ℂ (GaussianArea.normalizedMonomialIntrinsicVector alpha ha n)
        (C_intrinsicEntire lam alpha hlam ha f) =
      (I / 2) ^ n / ((Real.sqrt (alpha ^ n * (n.factorial : ℝ)) : ℝ) : ℂ) *
        ∫ u, (u : ℂ) ^ n * f u ∂(Ultraspherical.measure lam) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) := Ultraspherical.probability lam hlam
  rw [C_intrinsicEntire_eq_synthesizedIntrinsicVector]
  change inner ℂ (GaussianArea.normalizedMonomialL2Vector alpha ha n)
      (GaussianArea.coefficientSynthesisL2 alpha ha (C lam alpha hlam ha f)) = _
  rw [GaussianArea.coefficientSynthesisL2_coefficient, C_coefficient, ← complexWeight_eq alpha ha]
  simp only [WeightedMoments.coefficient, ContinuousLinearMap.smul_apply, smul_eq_mul]
  congr 1
  change inner ℂ (WeightedMoments.monomial (Ultraspherical.measure lam) (ae_abs_le_one lam) n) f = _
  rw [MeasureTheory.L2.inner_def]
  have hm := (WeightedMoments.monomial_memLp (Ultraspherical.measure lam)
    (ae_abs_le_one lam) n).coeFn_toLp
  refine integral_congr_ae ?_
  filter_upwards [hm] with u h1
  simp only [WeightedMoments.monomial] at h1 ⊢
  rw [h1]
  (simp [← Complex.ofReal_pow, Complex.conj_ofReal]) <;> ring

/-- The intrinsic Fock vector of a coefficient sequence is its coherent synthesis. -/
theorem equiv_apply_eq_synthesized (alpha : ℝ) (ha : 0 < alpha) (a : lp (fun _ : ℕ => ℂ) 2) :
    GaussianArea.coefficientIntrinsicEntireEquiv alpha ha a =
      GaussianArea.synthesizedIntrinsicVector alpha ha a := by
  apply Subtype.ext
  rfl

/-- **Theorem 6.3**, (6.5): `(C* F)(u) = F(−iu/(2α))` for `ν_λ`-a.e. `u`. -/
theorem C_intrinsicEntire_adjoint_ae (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (F : GaussianArea.entireGaussianL2Submodule alpha) :
    letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
      (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
    ((C_intrinsicEntire lam alpha hlam ha).adjoint F : ℝ → ℂ) =ᵐ[Ultraspherical.measure lam]
      fun u => GaussianArea.entireRepresentative alpha F
        (-I * (u : ℂ) / (2 * (alpha : ℂ))) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  set E := GaussianArea.coefficientIntrinsicEntireEquiv alpha ha
  have hadj : (C_intrinsicEntire lam alpha hlam ha).adjoint F =
      C_adjoint lam alpha hlam ha (E.symm F) := by
    apply ext_inner_right ℂ
    intro f
    rw [ContinuousLinearMap.adjoint_inner_left, C_adjoint,
      ContinuousLinearMap.adjoint_inner_left, C_intrinsicEntire_apply]
    conv_lhs => rw [show F = E (E.symm F) from (E.apply_symm_apply F).symm]
    exact E.inner_map_map _ _
  rw [hadj, FockAnalyticRestriction.adjoint_eq_analytic_restriction]
  have h := (FockAnalyticRestriction.memLp_evaluate lam alpha hlam ha (E.symm F)).coeFn_toLp
  refine h.trans (Filter.Eventually.of_forall fun u => ?_)
  show FockEvaluation.evaluation alpha ha (FockAnalyticRestriction.imaginaryPoint alpha u)
      (E.symm F) = _
  have hF : F = GaussianArea.synthesizedIntrinsicVector alpha ha (E.symm F) := by
    rw [← equiv_apply_eq_synthesized, LinearIsometryEquiv.apply_symm_apply]
  conv_rhs => rw [hF]
  rw [← GaussianArea.intrinsicEntireEvaluation_synthesized]
  rfl

/-- The real form of `∫ g dν_{1/2} = ½ ∫_{-1}^{1} g`. -/
theorem integral_half_real (g : ℝ → ℝ) :
    ∫ u, g u ∂(Ultraspherical.measure (1 / 2)) = 1 / 2 * ∫ u in (-1 : ℝ)..1, g u := by
  have h := EulerianState.integral_half (fun u => ((g u : ℝ) : ℂ))
  rw [integral_complex_ofReal, intervalIntegral.integral_ofReal] at h
  have h' := congrArg Complex.re h
  simpa using h'

/-- **Proposition 6.5** (13). -/
theorem proposition_6_5 {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure (1 / 2)))) :
    let I := ∑' i : ι, ‖C_intrinsicEntire (1 / 2) 1 (by norm_num) one_pos (b i)‖ ^ 2
    I = ∫ u, Real.exp (u ^ 2 / 4) ∂(Ultraspherical.measure (1 / 2)) ∧
      I = 1 / 2 * ∫ u in (-1 : ℝ)..1, Real.exp (u ^ 2 / 4) ∧
      I = ∑' n : ℕ, 1 / ((4 : ℝ) ^ n * (n.factorial : ℝ) * ((2 * n + 1 : ℕ) : ℝ)) ∧
      (1089974208367244447324816 : ℝ) / 10 ^ 24 < I ∧
      I < (1089974208367244447325767 : ℝ) / 10 ^ 24 := by
  intro I
  have hHS : I = KummerCoefficients.kummerSeries (1 / 2) (1 / (4 * 1)) :=
    C_intrinsicEntire_HS_energy_eq_kummer (1 / 2) 1 (by norm_num) one_pos b
  have hint := exp_integral_eq_kummerSeries (1 / 2) 1 (by norm_num) one_pos
  rw [show (4 : ℝ) * 1 = 4 by norm_num] at hint hHS
  have h1 : I = ∫ u, Real.exp (u ^ 2 / 4) ∂(Ultraspherical.measure (1 / 2)) := hHS.trans hint.symm
  have hser : I = ∑' n : ℕ, 1 / ((4 : ℝ) ^ n * (n.factorial : ℝ) * ((2 * n + 1 : ℕ) : ℝ)) :=
    hHS.trans RationalTrace.kummer_half_quarter_eq_realTraceSeries
  obtain ⟨hlo, hhi⟩ := RationalTrace.legendre_exp_integral_decimal_enclosure
  refine ⟨h1, h1.trans (integral_half_real _), hser, h1 ▸ hlo, h1 ▸ hhi⟩

#print axioms GegenbauerFock.Section6.C_intrinsicEntire_coeff
#print axioms GegenbauerFock.Section6.C_intrinsicEntire_adjoint_ae
#print axioms GegenbauerFock.Section6.proposition_6_5

end GegenbauerFock.Section6
