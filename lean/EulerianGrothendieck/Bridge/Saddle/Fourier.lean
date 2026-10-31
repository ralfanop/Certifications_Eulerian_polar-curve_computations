import Bridge.Saddle.AFun
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Lemma 5.5, part 4: Fourier representation of `w_M` and of its first two derivatives

Manuscript V173, eqs. (69)–(70).  For every real tilt `s`, every `M ≥ 2` and every real `y`,
`w_M(y) = (2π)⁻¹ ∫ A(s+iu)^M e^{-(s+iu)y} du`
(Fourier inversion of the tilted density `e^{sy} w_M(y)`, whose Fourier transform is
`A(s - 2πiξ)^M`).  Differentiating under the integral sign, for `M ≥ 4`,
`w_M^{(r)}(y) = (2π)⁻¹ ∫ A(s+iu)^M (-(s+iu))^r e^{-(s+iu)y} du`, `r = 1, 2`.
-/

open MeasureTheory Set Complex Filter Topology Metric
open scoped FourierTransform

namespace EulerianBridge.Saddle

/-! ## Integrable majorants -/

theorem norm_A_mul_norm_le (z : ℂ) : ‖A z‖ * ‖z‖ ≤ 2 * Real.exp (|z.re| / 2) := by
  by_cases hz : z = 0
  · subst hz; simp
  · have h := norm_A_decay hz
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    calc ‖A z‖ * ‖z‖ ≤ (2 * Real.exp (|z.re| / 2) / ‖z‖) * ‖z‖ :=
          mul_le_mul_of_nonneg_right h hn.le
      _ = 2 * Real.exp (|z.re| / 2) := by field_simp

theorem norm_A_le_exp (z : ℂ) : ‖A z‖ ≤ Real.exp (|z.re| / 2) :=
  (norm_A_le_Ar z).trans (Ar_le _)

theorem norm_A_sq_le (z : ℂ) :
    ‖A z‖ ^ 2 ≤ 8 * Real.exp (|z.re| / 2) ^ 2 / (4 + ‖z‖ ^ 2) := by
  have h1 := norm_A_le_exp z
  have h2 := norm_A_mul_norm_le z
  have hpos : 0 < 4 + ‖z‖ ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  have hA := norm_nonneg (A z)
  have hK := (Real.exp_pos (|z.re| / 2)).le
  have e1 : ‖A z‖ ^ 2 ≤ Real.exp (|z.re| / 2) ^ 2 := pow_le_pow_left₀ hA h1 2
  have e2 : (‖A z‖ * ‖z‖) ^ 2 ≤ (2 * Real.exp (|z.re| / 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  nlinarith [e1, e2]

/-- `|A(z)|^M |z|^r ≤ 2^r · 8 · e^{M|Re z|/2} / (4 + |z|²)` when `M ≥ r + 2`. -/
theorem norm_A_pow_mul_le (M r : ℕ) (h : r + 2 ≤ M) (z : ℂ) :
    ‖A z‖ ^ M * ‖z‖ ^ r ≤ 2 ^ r * 8 * Real.exp (|z.re| / 2) ^ M / (4 + ‖z‖ ^ 2) := by
  set K := Real.exp (|z.re| / 2)
  have hK : 0 ≤ K := (Real.exp_pos _).le
  have hA := norm_nonneg (A z)
  obtain ⟨m, rfl⟩ : ∃ m, M = m + r + 2 := ⟨M - r - 2, by omega⟩
  have e0 : ‖A z‖ ^ m ≤ K ^ m := pow_le_pow_left₀ hA (norm_A_le_exp z) m
  have e1 : (‖A z‖ * ‖z‖) ^ r ≤ (2 * K) ^ r := pow_le_pow_left₀ (by positivity) (norm_A_mul_norm_le z) r
  have e2 := norm_A_sq_le z
  have hpos : 0 < 4 + ‖z‖ ^ 2 := by positivity
  calc ‖A z‖ ^ (m + r + 2) * ‖z‖ ^ r = ‖A z‖ ^ m * (‖A z‖ * ‖z‖) ^ r * ‖A z‖ ^ 2 := by ring
    _ ≤ K ^ m * (2 * K) ^ r * (8 * K ^ 2 / (4 + ‖z‖ ^ 2)) := by
        apply mul_le_mul (mul_le_mul e0 e1 (by positivity) (by positivity)) e2 (by positivity)
          (by positivity)
    _ = 2 ^ r * 8 * K ^ (m + r + 2) / (4 + ‖z‖ ^ 2) := by
        field_simp; ring

theorem inv_four_add_le {z : ℂ} : 1 / (4 + ‖z‖ ^ 2) ≤ (1 + z.im ^ 2)⁻¹ := by
  rw [one_div]
  apply inv_anti₀ (by positivity)
  have : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm z) 2
  linarith

/-- The integrand `A(s+iu)^M (-(s+iu))^r e^{-(s+iu)y}`. -/
noncomputable def Wf (M r : ℕ) (s y u : ℝ) : ℂ :=
  A ((s:ℂ) + u * I) ^ M * (-((s:ℂ) + u * I)) ^ r * cexp (-((s:ℂ) + u * I) * y)

theorem continuous_Wf (M r : ℕ) (s y : ℝ) : Continuous (Wf M r s y) := by
  unfold Wf
  have : Continuous fun u : ℝ => A ((s:ℂ) + u * I) :=
    continuous_A.comp (by fun_prop)
  fun_prop

theorem norm_Wf_le (M r : ℕ) (h : r + 2 ≤ M) (s y u : ℝ) :
    ‖Wf M r s y u‖ ≤ 2 ^ r * 8 * Real.exp (|s| / 2) ^ M * Real.exp (-(s * y)) * (1 + u ^ 2)⁻¹ := by
  unfold Wf
  set z : ℂ := (s:ℂ) + u * I
  have hre : z.re = s := by simp [z]
  have him : z.im = u := by simp [z]
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, Complex.norm_exp]
  have hexp : (-z * (y:ℂ)).re = -(s * y) := by simp [z]
  rw [hexp]
  have hb := norm_A_pow_mul_le M r h z
  rw [hre] at hb
  have hi : 1 / (4 + ‖z‖ ^ 2) ≤ (1 + u ^ 2)⁻¹ := by rw [← him]; exact inv_four_add_le
  have hE := (Real.exp_pos (-(s * y))).le
  calc ‖A z‖ ^ M * ‖z‖ ^ r * Real.exp (-(s * y))
      ≤ (2 ^ r * 8 * Real.exp (|s| / 2) ^ M / (4 + ‖z‖ ^ 2)) * Real.exp (-(s * y)) :=
        mul_le_mul_of_nonneg_right hb hE
    _ = 2 ^ r * 8 * Real.exp (|s| / 2) ^ M * Real.exp (-(s * y)) * (1 / (4 + ‖z‖ ^ 2)) := by ring
    _ ≤ 2 ^ r * 8 * Real.exp (|s| / 2) ^ M * Real.exp (-(s * y)) * (1 + u ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hi (by positivity)

theorem integrable_Wf (M r : ℕ) (h : r + 2 ≤ M) (s y : ℝ) : Integrable (Wf M r s y) := by
  refine (integrable_inv_one_add_sq.const_mul
    (2 ^ r * 8 * Real.exp (|s| / 2) ^ M * Real.exp (-(s * y)))).mono'
    (continuous_Wf M r s y).aestronglyMeasurable (Eventually.of_forall (fun u => ?_))
  exact norm_Wf_le M r h s y u

/-- `W_{M,r}(s,y) = ∫ A(s+iu)^M (-(s+iu))^r e^{-(s+iu)y} du`. -/
noncomputable def Wint (M r : ℕ) (s y : ℝ) : ℂ := ∫ u : ℝ, Wf M r s y u

/-! ## Fourier inversion -/

/-- The tilted density `e^{sy} w_M(y)`. -/
noncomputable def tilt (M : ℕ) (s : ℝ) (y : ℝ) : ℂ := cexp ((s:ℂ) * y) * (w M y : ℂ)

theorem fourier_tilt (M : ℕ) (hM : 1 ≤ M) (s ξ : ℝ) :
    𝓕 (tilt M s) ξ = A ((s:ℂ) - 2 * Real.pi * ξ * I) ^ M := by
  rw [Real.fourierIntegral_real_eq_integral_exp_smul, ← laplace_w M hM]
  congr 1; funext y
  rw [smul_eq_mul, tilt, ← mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

theorem integrable_fourier_tilt (M : ℕ) (hM : 2 ≤ M) (s : ℝ) : Integrable (𝓕 (tilt M s)) := by
  have heq : 𝓕 (tilt M s) = fun ξ : ℝ => A ((s:ℂ) - 2 * Real.pi * ξ * I) ^ M := by
    funext ξ; exact fourier_tilt M (by omega) s ξ
  rw [heq]
  -- substitute ξ = -u/(2π)
  have hcont : Continuous fun ξ : ℝ => A ((s:ℂ) - 2 * Real.pi * ξ * I) ^ M :=
    (continuous_A.comp (by fun_prop)).pow M
  have hb : ∀ ξ : ℝ, ‖A ((s:ℂ) - 2 * Real.pi * ξ * I) ^ M‖ ≤
      8 * Real.exp (|s| / 2) ^ M * (1 + ξ ^ 2)⁻¹ := by
    intro ξ
    set z : ℂ := (s:ℂ) - 2 * Real.pi * ξ * I
    have hre : z.re = s := by simp [z]
    have him : z.im = -(2 * Real.pi * ξ) := by simp [z]
    have h0 := norm_A_pow_mul_le M 0 (by omega) z
    rw [pow_zero, mul_one, pow_zero, one_mul, hre] at h0
    rw [norm_pow]
    have hi : 1 / (4 + ‖z‖ ^ 2) ≤ (1 + ξ ^ 2)⁻¹ := by
      refine inv_four_add_le.trans ?_
      apply inv_anti₀ (by positivity)
      rw [him]
      have : (1:ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.two_le_pi]
      nlinarith [sq_nonneg ξ]
    calc ‖A z‖ ^ M ≤ 8 * Real.exp (|s| / 2) ^ M / (4 + ‖z‖ ^ 2) := h0
      _ = 8 * Real.exp (|s| / 2) ^ M * (1 / (4 + ‖z‖ ^ 2)) := by ring
      _ ≤ 8 * Real.exp (|s| / 2) ^ M * (1 + ξ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hi (by positivity)
  exact (integrable_inv_one_add_sq.const_mul _).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall hb)

theorem continuous_tilt (M : ℕ) (hM : 2 ≤ M) (s : ℝ) : Continuous (tilt M s) := by
  unfold tilt
  have := (Complex.continuous_ofReal.comp (w_continuous M hM))
  fun_prop

theorem integrable_tilt (M : ℕ) (hM : 1 ≤ M) (s : ℝ) : Integrable (tilt M s) :=
  integrable_mul_w M hM (g := fun y : ℝ => cexp ((s:ℂ) * y)) (by fun_prop)

/-- Representation (70): `w_M(y) = (2π)⁻¹ ∫ A(s+iu)^M e^{-(s+iu)y} du` for every real `s`. -/
theorem w_eq_Wint (M : ℕ) (hM : 2 ≤ M) (s y : ℝ) :
    (w M y : ℂ) = (2 * Real.pi : ℂ)⁻¹ * Wint M 0 s y := by
  have hinv := (continuous_tilt M hM s).fourier_inversion (integrable_tilt M (by omega) s)
    (integrable_fourier_tilt M hM s)
  have hy := congrFun hinv y
  rw [Real.fourierIntegralInv_eq_fourierIntegral_neg, Real.fourierIntegral_real_eq_integral_exp_smul]
    at hy
  simp_rw [smul_eq_mul, fourier_tilt M (by omega) s] at hy
  -- hy : ∫ ξ, e^{2πiξy} A(s - 2πiξ)^M = e^{sy} w(y)
  have hsub : ∫ ξ : ℝ, cexp (↑(-2 * Real.pi * ξ * -y) * I) * A ((s:ℂ) - 2 * Real.pi * ξ * I) ^ M =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ u : ℝ, cexp (-(u:ℂ) * y * I) * A ((s:ℂ) + u * I) ^ M := by
    have := Measure.integral_comp_mul_left
      (fun u : ℝ => cexp (-(u:ℂ) * y * I) * A ((s:ℂ) + u * I) ^ M) (-(2 * Real.pi))
    rw [abs_inv, abs_neg, abs_of_pos Real.two_pi_pos] at this
    rw [← this]
    congr 1; funext ξ
    congr 2
    · push_cast; ring
    · push_cast; ring
  rw [hsub] at hy
  unfold Wint Wf
  have hexp : (w M y : ℂ) = cexp (-(s:ℂ) * y) * tilt M s y := by
    rw [tilt, ← mul_assoc, ← Complex.exp_add]; simp
  rw [hexp, ← hy, Complex.real_smul, ← MeasureTheory.integral_const_mul]
  push_cast
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  congr 1; funext u
  rw [pow_zero, mul_one]
  have : cexp (-((s:ℂ) + u * I) * y) = cexp (-(s:ℂ) * y) * cexp (-(u:ℂ) * y * I) := by
    rw [← Complex.exp_add]; ring_nf
  rw [this]; ring

/-! ## Differentiation under the integral sign -/

theorem hasDerivAt_Wf (M r : ℕ) (s u y : ℝ) :
    HasDerivAt (fun y => Wf M r s y u) (Wf M (r + 1) s y u) y := by
  unfold Wf
  set z : ℂ := (s:ℂ) + u * I
  have h := (((hasDerivAt_id (y:ℂ)).const_mul (-z)).cexp).comp_ofReal (z := y)
  have h2 := h.const_mul (A z ^ M * (-z) ^ r)
  simp only [id, mul_one] at h2
  convert h2 using 1
  ring

theorem hasDerivAt_Wint (M r : ℕ) (h : r + 3 ≤ M) (s y : ℝ) :
    HasDerivAt (Wint M r s) (Wint M (r + 1) s y) y := by
  set C : ℝ := 2 ^ (r + 1) * 8 * Real.exp (|s| / 2) ^ M * Real.exp (|s| * (|y| + 1))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := y)
    (F := fun y u => Wf M r s y u) (F' := fun y u => Wf M (r + 1) s y u)
    (bound := fun u => C * (1 + u ^ 2)⁻¹) (ε := 1) one_pos
    (Eventually.of_forall (fun y' => (continuous_Wf M r s y').aestronglyMeasurable))
    (integrable_Wf M r (by omega) s y)
    ((continuous_Wf M (r + 1) s y).aestronglyMeasurable)
    (Eventually.of_forall (fun u y' hy' => ?_))
    (integrable_inv_one_add_sq.const_mul C)
    (Eventually.of_forall (fun u y' _ => hasDerivAt_Wf M r s u y'))
  · exact key.2
  · refine (norm_Wf_le M (r + 1) (by omega) s y' u).trans ?_
    have hy'' : |y'| ≤ |y| + 1 := by
      rw [mem_ball, Real.dist_eq] at hy'
      have := abs_sub_abs_le_abs_sub y' y
      linarith
    have he : Real.exp (-(s * y')) ≤ Real.exp (|s| * (|y| + 1)) := by
      apply Real.exp_le_exp.mpr
      calc -(s * y') ≤ |s * y'| := neg_le_abs _
        _ = |s| * |y'| := abs_mul _ _
        _ ≤ |s| * (|y| + 1) := mul_le_mul_of_nonneg_left hy'' (abs_nonneg _)
    have : 0 ≤ 2 ^ (r + 1) * 8 * Real.exp (|s| / 2) ^ M := by positivity
    have hi : 0 ≤ (1 + u ^ 2)⁻¹ := by positivity
    calc 2 ^ (r + 1) * 8 * Real.exp (|s| / 2) ^ M * Real.exp (-(s * y')) * (1 + u ^ 2)⁻¹
        ≤ 2 ^ (r + 1) * 8 * Real.exp (|s| / 2) ^ M * Real.exp (|s| * (|y| + 1)) * (1 + u ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he this) hi
      _ = C * (1 + u ^ 2)⁻¹ := rfl

/-- For `M ≥ 3`: `w_M' (y) = (2π)⁻¹ W_{M,1}(s,y)` (as complex numbers), for every real `s`. -/
theorem hasDerivAt_w (M : ℕ) (hM : 3 ≤ M) (s y : ℝ) :
    HasDerivAt (w M) ((2 * Real.pi : ℂ)⁻¹ * Wint M 1 s y).re y := by
  have h := (hasDerivAt_Wint M 0 (by omega) s y).const_mul (2 * Real.pi : ℂ)⁻¹
  have heq : (fun y => (2 * Real.pi : ℂ)⁻¹ * Wint M 0 s y) = fun y => ((w M y : ℝ) : ℂ) := by
    funext y'; rw [w_eq_Wint M (by omega) s y']
  rw [heq] at h
  have := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt y h)
  simpa [Function.comp_def] using this

theorem deriv_w_ofReal (M : ℕ) (hM : 3 ≤ M) (s y : ℝ) :
    ((deriv (w M) y : ℝ) : ℂ) = (2 * Real.pi : ℂ)⁻¹ * Wint M 1 s y := by
  have h := (hasDerivAt_Wint M 0 (by omega) s y).const_mul (2 * Real.pi : ℂ)⁻¹
  have heq : (fun y => (2 * Real.pi : ℂ)⁻¹ * Wint M 0 s y) = fun y => ((w M y : ℝ) : ℂ) := by
    funext y'; rw [w_eq_Wint M (by omega) s y']
  rw [heq] at h
  have h2 := (hasDerivAt_w M hM s y).ofReal_comp
  rw [(hasDerivAt_w M hM s y).deriv]
  exact h2.unique h

theorem deriv_w_eq (M : ℕ) (hM : 3 ≤ M) (s : ℝ) :
    deriv (w M) = fun y => ((2 * Real.pi : ℂ)⁻¹ * Wint M 1 s y).re := by
  funext y; exact (hasDerivAt_w M hM s y).deriv

/-- For `M ≥ 4`: `w_M'' (y) = (2π)⁻¹ W_{M,2}(s,y)`. -/
theorem hasDerivAt_deriv_w (M : ℕ) (hM : 4 ≤ M) (s y : ℝ) :
    HasDerivAt (deriv (w M)) ((2 * Real.pi : ℂ)⁻¹ * Wint M 2 s y).re y := by
  rw [deriv_w_eq M (by omega) s]
  have h := (hasDerivAt_Wint M 1 (by omega) s y).const_mul (2 * Real.pi : ℂ)⁻¹
  have := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt y h)
  simpa [Function.comp_def] using this

theorem deriv2_w_ofReal (M : ℕ) (hM : 4 ≤ M) (s y : ℝ) :
    ((deriv (deriv (w M)) y : ℝ) : ℂ) = (2 * Real.pi : ℂ)⁻¹ * Wint M 2 s y := by
  have h := (hasDerivAt_Wint M 1 (by omega) s y).const_mul (2 * Real.pi : ℂ)⁻¹
  have heq : (fun y => (2 * Real.pi : ℂ)⁻¹ * Wint M 1 s y) = fun y => ((deriv (w M) y : ℝ) : ℂ) := by
    funext y'; rw [deriv_w_ofReal M (by omega) s y']
  rw [heq] at h
  have h2 := (hasDerivAt_deriv_w M hM s y).ofReal_comp
  rw [(hasDerivAt_deriv_w M hM s y).deriv]
  exact h2.unique h

end EulerianBridge.Saddle
