import UniformLanczos.Lemma513SupportUniform
import UniformLanczos.Rate514Residual

/-! M12 equation (190). Work with the literal scaled B-spline weight gM
and its logarithmic derivative, rather than an abstract measure.
No assumed interior error or Cauchy-Schwarz bound. Spectral Freud
identification and the actual polynomial family's normalization remain
explicit inputs to the later operator-level theorem. -/
noncomputable section
namespace UniformLanczos.Rate514ActualIntegralResidual
open MeasureTheory Set EulerianBridge.Saddle
open UniformLanczos.Lemma513ActualGM UniformLanczos.Lemma513SupportUniform

theorem signed_log_deriv_global {M : ℕ} (hM : 4 ≤ M) (x : ℝ) :
    deriv (φM M) x * gM M x = -(deriv (gM M) x)/(M:ℝ) := by
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  by_cases hx : |x| < (1/2:ℝ)
  · rw [actual_gM_log_deriv (by omega : 3 ≤ M) (abs_lt.mp hx)]
    field_simp [hm]
    <;> ring
  · rw [actual_gM_zero_closed_outside (by omega : 3 ≤ M) (le_of_not_gt hx),
      actual_deriv_zero_closed_outside hM (le_of_not_gt hx)]
    simp

def actualResidual (M : ℕ) (f p q : ℝ → ℝ) : ℝ :=
  ∫ x, (f x-deriv (φM M) x)*(p x*q x)*gM M x

theorem actualResidual_integrable (M : ℕ) (hM : 4 ≤ M)
    (f p q : ℝ → ℝ) (hf : Continuous f) (hp : Continuous p) (hq : Continuous q) :
    Integrable (fun x => (f x-deriv (φM M) x)*(p x*q x)*gM M x) := by
  apply continuous_supported_integrable
  · have he : (fun x => (f x-deriv (φM M) x)*(p x*q x)*gM M x) =
        fun x => (f x*gM M x+deriv (gM M) x/(M:ℝ))*(p x*q x) := by
      funext x
      have h := signed_log_deriv_global hM x
      rw [show (f x-deriv (φM M) x)*(p x*q x)*gM M x =
          (f x*gM M x-deriv (φM M) x*gM M x)*(p x*q x) by ring,h]
      ring
    rw [he]
    exact ((hf.mul (actual_gM_continuous (by omega : 3 ≤ M))).add
      ((actual_gM_deriv_continuous hM).div_const _)).mul (hp.mul hq)
  · intro x hx
    rw [actual_gM_zero_closed_outside (by omega : 3 ≤ M) hx.le,mul_zero]

theorem cross_integrable (M : ℕ) (hM : 4 ≤ M)
    (p q : ℝ → ℝ) (hp : Continuous p) (hq : Continuous q) :
    Integrable (fun x => |p x*q x| *gM M x) := by
  apply continuous_supported_integrable
  · exact (hp.mul hq).abs.mul (actual_gM_continuous (by omega : 3 ≤ M))
  · intro x hx
    rw [actual_gM_zero_closed_outside (by omega : 3 ≤ M) hx.le,mul_zero]

theorem cross_pointwise (p q : ℝ) : |p*q| ≤ (p^2+q^2)/2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|p|-|q|),sq_abs p,sq_abs q]

theorem normalized_cross (M : ℕ) (hM : 4 ≤ M) (p q : ℝ → ℝ)
    (hp : Continuous p) (hq : Continuous q)
    (hp1 : ∫ x, p x^2*gM M x = 1) (hq1 : ∫ x, q x^2*gM M x = 1) :
    (∫ x, |p x*q x| *gM M x) ≤ 1 := by
  have hpi := square_supported_integrable M hM p hp
  have hqi := square_supported_integrable M hM q hq
  calc
    _ ≤ ∫ x, (p x^2*gM M x+q x^2*gM M x)/2 :=
      integral_mono (cross_integrable M hM p q hp hq) ((hpi.add hqi).div_const 2)
        (fun x => by
          have h := mul_le_mul_of_nonneg_right (cross_pointwise (p x) (q x)) (actual_gM_nonneg M x)
          convert h using 1 <;> ring)
    _ = 1 := by rw [integral_div,integral_add hpi hqi,hp1,hq1]; norm_num

theorem actual_integral_residual_bound (M : ℕ) (hM : 4 ≤ M)
    (f p q : ℝ → ℝ) (hf : Continuous f) (hp : Continuous p) (hq : Continuous q)
    {r A Cf T₁ T₂ : ℝ} (hA : 0 ≤ A) (hCf : 0 ≤ Cf)
    (hp1 : ∫ x, p x^2*gM M x = 1) (hq1 : ∫ x, q x^2*gM M x = 1)
    (hinner : ∀ x, |x| < r → |f x-deriv (φM M) x| ≤ A/(M:ℝ))
    (hfb : ∀ x, |f x| ≤ Cf)
    (hTp : tailMass M p r ≤ T₁) (hTq : tailMass M q r ≤ T₁)
    (hTw : weightedTail M p q r ≤ T₂) :
    |actualResidual M f p q| ≤ A/(M:ℝ)+Cf*T₁+T₂ := by
  let S : Set ℝ := {x | r ≤ |x|}
  let F : ℝ → ℝ := fun x => (f x-deriv (φM M) x)*(p x*q x)*gM M x
  let U : ℝ → ℝ := fun x => |p x*q x| *gM M x
  let P : ℝ → ℝ := fun x => p x^2*gM M x
  let Q : ℝ → ℝ := fun x => q x^2*gM M x
  let V : ℝ → ℝ := fun x => |p x*q x| *|deriv (φM M) x| *gM M x
  have hS : MeasurableSet S := measurableSet_le measurable_const continuous_abs.measurable
  have hF : Integrable F := actualResidual_integrable M hM f p q hf hp hq
  have hU : Integrable U := cross_integrable M hM p q hp hq
  have hP : Integrable P := square_supported_integrable M hM p hp
  have hQ : Integrable Q := square_supported_integrable M hM q hq
  have hV : Integrable V := by
    apply continuous_supported_integrable
    · exact weighted_integrand_continuous M hM p q hp hq
    · intro x hx
      dsimp [V]
      rw [actual_gM_zero_closed_outside (by omega : 3 ≤ M) hx.le,mul_zero]
  have hu : ∫ x, U x ≤ 1 := normalized_cross M hM p q hp hq hp1 hq1
  have hAM : 0 ≤ A/(M:ℝ) := by positivity
  have hin : |∫ x in Sᶜ, F x| ≤ A/(M:ℝ) := by
    calc
      _ ≤ ∫ x in Sᶜ, |F x| := abs_integral_le_integral_abs
      _ ≤ ∫ x in Sᶜ, (A/(M:ℝ))*U x := by
        apply setIntegral_mono_on hF.abs.integrableOn (hU.const_mul _).integrableOn hS.compl
        intro x hx
        have hx' : |x| < r := by simpa [S] using hx
        simp only [F,U,abs_mul,abs_of_nonneg (actual_gM_nonneg M x),mul_assoc]
        exact mul_le_mul_of_nonneg_right (hinner x hx')
          (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (actual_gM_nonneg M x))
      _ ≤ ∫ x, (A/(M:ℝ))*U x :=
        setIntegral_le_integral (hU.const_mul _) (Filter.Eventually.of_forall fun x => by
          dsimp [U]; exact mul_nonneg hAM (mul_nonneg (abs_nonneg _) (actual_gM_nonneg M x)))
      _ = (A/(M:ℝ))*(∫ x, U x) := integral_const_mul _ _
      _ ≤ (A/(M:ℝ))*1 := mul_le_mul_of_nonneg_left hu hAM
      _ = _ := mul_one _
  have hsum : Integrable (fun x => Cf*((P x+Q x)/2)+V x) :=
    (((hP.add hQ).div_const 2).const_mul Cf).add hV
  have hout : |∫ x in S, F x| ≤ Cf*T₁+T₂ := by
    calc
      _ ≤ ∫ x in S, |F x| := abs_integral_le_integral_abs
      _ ≤ ∫ x in S, Cf*((P x+Q x)/2)+V x := by
        apply setIntegral_mono_on hF.abs.integrableOn hsum.integrableOn hS
        intro x _
        have hg := actual_gM_nonneg M x
        have hcross := cross_pointwise (p x) (q x)
        have h1 := mul_le_mul (hfb x) hcross (abs_nonneg _) hCf
        have h2 := mul_le_mul_of_nonneg_right (abs_sub (f x) (deriv (φM M) x))
          (mul_nonneg (abs_nonneg (p x*q x)) hg)
        have h3 := mul_le_mul_of_nonneg_right h1 hg
        simp only [F,P,Q,V,abs_mul,abs_of_nonneg hg] at *
        nlinarith
      _ = Cf*((∫ x in S, P x)+(∫ x in S, Q x))/2 + ∫ x in S, V x := by
        rw [integral_add (((hP.add hQ).div_const 2).const_mul Cf).integrableOn hV.integrableOn,
          integral_const_mul,integral_div,integral_add hP.integrableOn hQ.integrableOn]
        ring
      _ ≤ Cf*T₁+T₂ := by
        change (∫ x in S, P x) ≤ T₁ at hTp
        change (∫ x in S, Q x) ≤ T₁ at hTq
        change (∫ x in S, V x) ≤ T₂ at hTw
        have h := mul_le_mul_of_nonneg_left (show ((∫ x in S, P x)+(∫ x in S, Q x))/2 ≤ T₁ by linarith) hCf
        linarith
  unfold actualResidual
  change |∫ x, F x| ≤ _
  rw [← integral_add_compl hS hF]
  exact (abs_add_le _ _).trans (by linarith)

/-- Interior error for the literal logarithmic derivative is discharged
by the integrated saddlepoint theorem, not provided as a premise. -/
theorem actual_interior_uniform (f : ℝ → ℝ) {r : ℝ}
    (hr : 0 < r) (hr2 : r < 1/2)
    (hf : ∀ x ∈ Icc (-r) r, f x = UL.Ip x) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∀ x, |x| < r → |f x-deriv (φM M) x| ≤ A/(M:ℝ) := by
  obtain ⟨M₀,C,hC⟩ := lemma_5_5_phi hr hr2
  refine ⟨|C|,abs_nonneg _,max M₀ 1,?_⟩
  intro M hM x hx
  have hx' : x ∈ Icc (-r) r := ⟨(abs_lt.mp hx).1.le,(abs_lt.mp hx).2.le⟩
  rw [hf x hx',abs_sub_comm]
  exact ((hC M (le_trans (le_max_left _ _) hM) x hx').1).trans
    (div_le_div_of_nonneg_right (le_abs_self C) (Nat.cast_nonneg _))

end UniformLanczos.Rate514ActualIntegralResidual
#print axioms UniformLanczos.Rate514ActualIntegralResidual.signed_log_deriv_global
#print axioms UniformLanczos.Rate514ActualIntegralResidual.actualResidual_integrable
#print axioms UniformLanczos.Rate514ActualIntegralResidual.cross_integrable
#print axioms UniformLanczos.Rate514ActualIntegralResidual.cross_pointwise
#print axioms UniformLanczos.Rate514ActualIntegralResidual.normalized_cross
#print axioms UniformLanczos.Rate514ActualIntegralResidual.actual_integral_residual_bound
#print axioms UniformLanczos.Rate514ActualIntegralResidual.actual_interior_uniform
