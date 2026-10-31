import Bridge.Fock3

/-!
# Proposition 3.3 (continued): the series, `G_E`, the bounds (10) and the closed form (21)
-/

open MeasureTheory Complex Set intervalIntegral ProbabilityTheory Filter Topology
open scoped ComplexConjugate

namespace EulerianBridge.Fock3

open EulerianGrothendieck.Fock

/-! ## An i.i.d. uniform sequence, to instantiate the general Fock-norm theorems at `M = 1` -/

noncomputable abbrev Pinf : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => V033.UniformSum.uniformLaw)

theorem Pinf_indep : iIndepFun (fun i (ω : ℕ → ℝ) => ω i) Pinf :=
  iIndepFun_infinitePi (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id)

theorem Pinf_law (i : ℕ) : Pinf.map (fun ω : ℕ → ℝ => ω i) = V033.UniformSum.uniformLaw :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => V033.UniformSum.uniformLaw) i).map_eq

theorem moment_uniform (k : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range 1, ω i) ^ (2 * k) ∂Pinf = EulerianBridge.AppendixA.m k := by
  simp only [Finset.range_one, Finset.sum_singleton]
  have h := integral_map (φ := fun ω : ℕ → ℝ => ω 0) (μ := Pinf) (measurable_pi_apply 0).aemeasurable
    (f := fun x : ℝ => x ^ (2 * k)) (by fun_prop)
  rw [Pinf_law] at h
  refine h.symm.trans ?_
  unfold V033.UniformSum.uniformLaw EulerianBridge.AppendixA.m
  rw [intervalIntegral.integral_of_le (by norm_num)]

/-- Prop. 3.3, eq. (11), second equality: the even-moment series. -/
theorem fock_norm_series {α : ℝ} (hα : 0 < α) :
    ∫ z : ℂ, ‖rE z‖ ^ 2 * fockDensity α z =
      ∑' k : ℕ, 1 / (2 ^ (4 * k) * α ^ (2 * k) * ((2 * k).factorial : ℝ) * (2 * k + 1) ^ 2) := by
  have h := fock_norm_eq_moment_series (fun i (ω : ℕ → ℝ) => ω i) (fun i => measurable_pi_apply i)
    Pinf_indep Pinf_law 1 hα
  simp only [pow_one] at h
  rw [h]
  congr 1; funext k
  rw [moment_uniform, EulerianBridge.AppendixA.m_eq]
  have h4 : (4:ℝ) ^ k * 4 ^ k = 2 ^ (4 * k) := by rw [← mul_pow, pow_mul]; norm_num
  have hf : (0:ℝ) < (2 * k).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [← h4]
  field_simp

/-- Odd moments of the uniform law vanish. -/
theorem odd_moment (k : ℕ) : ∫ t in (-1/2:ℝ)..(1/2), t ^ (2 * k + 1) = 0 := by
  rw [integral_pow, show (-1/2:ℝ) = -(1/2) by ring, Even.neg_pow ⟨k + 1, by ring⟩]
  ring

/-! ## The norm of `G_E` -/

theorem charFun_shift (z : ℂ) :
    ∫ x, cexp (I * z * ((x + 1 : ℝ) : ℂ)) ∂V033.UniformSum.uniformLaw = GE z := by
  have e : ∀ x : ℝ, cexp (I * z * ((x + 1 : ℝ) : ℂ)) = cexp (I * z) * cexp (I * z * (x : ℂ)) := by
    intro x; rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [e]
  rw [MeasureTheory.integral_const_mul, charFun_uniform]; rfl

theorem norm_sq_GE_pair (z : ℂ) :
    ((‖GE z‖ ^ 2 : ℝ) : ℂ) =
      ∫ p, cexp (I * z * ((p.1 + 1 : ℝ) : ℂ) - I * conj z * ((p.2 + 1 : ℝ) : ℂ)) ∂ν := by
  have hconj : conj (GE z) = ∫ x, cexp (-I * conj z * ((x + 1 : ℝ) : ℂ)) ∂V033.UniformSum.uniformLaw := by
    rw [← charFun_shift, ← integral_conj]
    congr 1; funext x
    rw [← Complex.exp_conj, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hnorm : ((‖GE z‖ ^ 2 : ℝ) : ℂ) = GE z * conj (GE z) := by
    rw [Complex.mul_conj']; push_cast; ring
  rw [hnorm, hconj]
  conv_lhs => rw [← charFun_shift]
  rw [← integral_prod_mul]
  congr 1; funext p
  rw [← Complex.exp_add]; congr 1; ring

theorem ae_abs_shift_le : ∀ᵐ x ∂V033.UniformSum.uniformLaw, |x + 1| ≤ 3 / 2 := by
  filter_upwards [ae_abs_le_half] with x hx
  rw [abs_le] at hx ⊢; constructor <;> linarith [hx.1, hx.2]

/-- Prop. 3.3, eq. (11), second line: `‖G_E‖² = ∫∫_{[1/2,3/2]²} e^{ts/α}`. -/
theorem fock_norm_GE {α : ℝ} (hα : 0 < α) :
    ∫ z : ℂ, ‖GE z‖ ^ 2 * fockDensity α z =
      ∫ t in (1/2:ℝ)..(3/2), ∫ s in (1/2:ℝ)..(3/2), Real.exp (t * s / α) := by
  have hX : ∀ᵐ p ∂ν, |p.1 + 1| ≤ 3 / 2 := Measure.quasiMeasurePreserving_fst.ae ae_abs_shift_le
  have hY : ∀ᵐ p ∂ν, |p.2 + 1| ≤ 3 / 2 := Measure.quasiMeasurePreserving_snd.ae ae_abs_shift_le
  have hfub := gaussian_fubini (X := fun p : ℝ × ℝ => p.1 + 1) (Y := fun p : ℝ × ℝ => p.2 + 1)
    (by fun_prop) (by fun_prop) (3 / 2) hX hY hα
  have hpair : ∫ z : ℂ, ‖GE z‖ ^ 2 * fockDensity α z = ∫ p, Real.exp ((p.1 + 1) * (p.2 + 1) / α) ∂ν := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal, ← integral_complex_ofReal]
    have hlhs : ∀ z : ℂ, (((‖GE z‖ ^ 2 * fockDensity α z : ℝ)) : ℂ) =
        (∫ p, cexp (I * z * ((p.1 + 1 : ℝ) : ℂ) - I * conj z * ((p.2 + 1 : ℝ) : ℂ)) ∂ν) *
          (fockDensity α z : ℂ) := by
      intro z; rw [ofReal_mul, norm_sq_GE_pair]
    simp_rw [hlhs]
    rw [hfub]
    congr 1; funext p
    rw [ofReal_exp, ofReal_div, ofReal_mul]
  rw [hpair, integral_ν (fun t s => Real.exp ((t + 1) * (s + 1) / α)) (by fun_prop)]
  have hs : ∀ t : ℝ, ∫ s in (-1/2:ℝ)..(1/2), Real.exp ((t + 1) * (s + 1) / α) =
      ∫ s in (1/2:ℝ)..(3/2), Real.exp ((t + 1) * s / α) := by
    intro t
    have := intervalIntegral.integral_comp_add_right (fun s : ℝ => Real.exp ((t + 1) * s / α)) (1:ℝ)
      (a := -1/2) (b := 1/2)
    rw [show (-1/2:ℝ) + 1 = 1/2 by norm_num, show (1/2:ℝ) + 1 = 3/2 by norm_num] at this
    exact this
  simp_rw [hs]
  have := intervalIntegral.integral_comp_add_right
    (fun t : ℝ => ∫ s in (1/2:ℝ)..(3/2), Real.exp (t * s / α)) (1:ℝ) (a := -1/2) (b := 1/2)
  rw [show (-1/2:ℝ) + 1 = 1/2 by norm_num, show (1/2:ℝ) + 1 = 3/2 by norm_num] at this
  exact this

/-! ## The upper bounds (10) -/

theorem double_le (a b : ℝ) (hab : a ≤ b) {α : ℝ} (hα : 0 < α) :
    ∫ t in a..b, ∫ s in a..b, Real.exp (t * s / α) ≤
      (∫ t in a..b, Real.exp (t ^ 2 / (2 * α))) ^ 2 := by
  have hc : ∀ t : ℝ, Continuous (fun s : ℝ => Real.exp (t * s / α)) := fun t => by fun_prop
  have hin : ∀ t s : ℝ, Real.exp (t * s / α) ≤ Real.exp (t ^ 2 / (2 * α)) * Real.exp (s ^ 2 / (2 * α)) := by
    intro t s
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [div_add_div_same, div_le_div_iff₀ hα (by positivity)]
    nlinarith [sq_nonneg (t - s)]
  have hcont : Continuous (fun t : ℝ => ∫ s in a..b, Real.exp (t * s / α)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) a b
  calc ∫ t in a..b, ∫ s in a..b, Real.exp (t * s / α)
      ≤ ∫ t in a..b, ∫ s in a..b, Real.exp (t ^ 2 / (2 * α)) * Real.exp (s ^ 2 / (2 * α)) := by
        apply intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable a b)
        · apply Continuous.intervalIntegrable
          exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) a b
        · intro t _
          exact intervalIntegral.integral_mono_on hab ((hc t).intervalIntegrable a b)
            (by apply Continuous.intervalIntegrable; fun_prop) (fun s _ => hin t s)
    _ = (∫ t in a..b, Real.exp (t ^ 2 / (2 * α))) ^ 2 := by
        simp_rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_mul_const, sq]

/-- Eq. (10): `‖r_E‖ ≤ ∫_{-1/2}^{1/2} e^{t²/(2α)} dt` and `‖G_E‖ ≤ ∫_{1/2}^{3/2} e^{t²/(2α)} dt`. -/
theorem fock_upper {α : ℝ} (hα : 0 < α) :
    Real.sqrt (∫ z : ℂ, ‖rE z‖ ^ 2 * fockDensity α z) ≤ ∫ t in (-1/2:ℝ)..(1/2), Real.exp (t ^ 2 / (2 * α)) ∧
      Real.sqrt (∫ z : ℂ, ‖GE z‖ ^ 2 * fockDensity α z) ≤ ∫ t in (1/2:ℝ)..(3/2), Real.exp (t ^ 2 / (2 * α)) := by
  have hpos : ∀ a b : ℝ, a ≤ b → 0 ≤ ∫ t in a..b, Real.exp (t ^ 2 / (2 * α)) :=
    fun a b hab => intervalIntegral.integral_nonneg hab (fun t _ => (Real.exp_pos _).le)
  constructor
  · rw [fock_norm_rE hα, Real.sqrt_le_left (hpos _ _ (by norm_num))]
    exact double_le _ _ (by norm_num) hα
  · rw [fock_norm_GE hα, Real.sqrt_le_left (hpos _ _ (by norm_num))]
    exact double_le _ _ (by norm_num) hα

/-! ## The closed form (21) -/

/-- The sinh integral `Shi(x) = ∫_0^x sinh t / t dt`. -/
noncomputable def Shi (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, Real.sinh t / t

/-- The inner integral `H(t) = ∫_{-1/2}^{1/2} e^{ts/α} ds`. -/
noncomputable def H (α t : ℝ) : ℝ := ∫ s in (-1/2:ℝ)..(1/2), Real.exp (t * s / α)

theorem H_continuous (α : ℝ) : Continuous (H α) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _

theorem H_neg (α t : ℝ) : H α (-t) = H α t := by
  unfold H
  have h := intervalIntegral.integral_comp_neg (a := (-1/2:ℝ)) (b := 1/2) (fun s : ℝ => Real.exp (t * s / α))
  rw [show -(1/2:ℝ) = -1/2 by ring, show -(-1/2:ℝ) = 1/2 by ring] at h
  rw [← h]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  ring_nf

theorem H_eq {α t : ℝ} (hα : 0 < α) (ht : t ≠ 0) : H α t = 2 * α * Real.sinh (t / (2 * α)) / t := by
  unfold H
  have hc : t / α ≠ 0 := div_ne_zero ht hα.ne'
  have h := intervalIntegral.integral_comp_mul_left (fun u : ℝ => Real.exp u) hc (a := -1/2) (b := 1/2)
  have e : ∀ s : ℝ, Real.exp (t * s / α) = Real.exp (t / α * s) := fun s => by ring_nf
  simp_rw [e]
  rw [h, integral_exp, smul_eq_mul, Real.sinh_eq]
  rw [show t / α * (1 / 2) = t / (2 * α) by field_simp, show t / α * (-1 / 2) = -(t / (2 * α)) by
    field_simp]
  field_simp

/-- Eq. (21): `‖r_E‖² = 4α ∫_0^{1/2} sinh(t/(2α))/t dt = 4α Shi(1/(4α))`. -/
theorem fock_norm_Shi {α : ℝ} (hα : 0 < α) :
    ∫ z : ℂ, ‖rE z‖ ^ 2 * fockDensity α z = 4 * α * ∫ t in (0:ℝ)..(1/2), Real.sinh (t / (2 * α)) / t ∧
      4 * α * ∫ t in (0:ℝ)..(1/2), Real.sinh (t / (2 * α)) / t = 4 * α * Shi (1 / (4 * α)) := by
  have hHi : ∀ a b : ℝ, IntervalIntegrable (H α) volume a b := fun a b => (H_continuous α).intervalIntegrable a b
  have hsplit : ∫ t in (-1/2:ℝ)..(1/2), H α t = 2 * ∫ t in (0:ℝ)..(1/2), H α t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hHi (-1/2) 0) (hHi 0 (1/2))]
    have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := 1/2) (H α)
    rw [neg_zero, show -(1/2:ℝ) = -1/2 by ring] at h
    rw [← h]
    simp_rw [H_neg]
    ring
  have hpos : ∫ t in (0:ℝ)..(1/2), H α t = ∫ t in (0:ℝ)..(1/2), 2 * α * (Real.sinh (t / (2 * α)) / t) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall (fun t ht => ?_))
    rw [uIoc_of_le (by norm_num)] at ht
    rw [H_eq hα (ne_of_gt ht.1)]; ring
  constructor
  · rw [fock_norm_rE hα]
    change ∫ t in (-1/2:ℝ)..(1/2), H α t = _
    rw [hsplit, hpos, intervalIntegral.integral_const_mul]; ring
  · congr 1
    unfold Shi
    have h2 : (2 * α) ≠ 0 := by positivity
    have h := intervalIntegral.integral_comp_mul_left (fun t : ℝ => Real.sinh (t / (2 * α)) / t) h2
      (a := 0) (b := 1 / (4 * α))
    rw [mul_zero, show 2 * α * (1 / (4 * α)) = 1 / 2 by field_simp; ring] at h
    rw [← smul_inv_smul₀ h2 (∫ t in (0:ℝ)..(1/2), Real.sinh (t / (2 * α)) / t), ← h, smul_eq_mul,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    simp only []
    rw [show 2 * α * u / (2 * α) = u by field_simp]
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · field_simp

end EulerianBridge.Fock3
