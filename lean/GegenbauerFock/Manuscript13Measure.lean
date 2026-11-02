import GegenbauerFock.Manuscript13Beta
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Manuscript 13, Definition 2.1 and Proposition 3.1

`ν_λ` has density `c_λ (1-u²)^{λ-1/2}` on `(-1,1)`, `c_λ = Γ(λ+1)/(√π Γ(λ+1/2))`.
For every `λ > -1/2` (in particular `λ > 0`, and the arcsine endpoint `λ = 0`):
`ν_λ` is a probability measure, the odd moments vanish and
`m_{2n}(λ) = (1/2)_n/(λ+1)_n`. -/

open Real MeasureTheory Set intervalIntegral

namespace GegenbauerFock.Manuscript13

noncomputable def cl (l : ℝ) : ℝ := Real.Gamma (l + 1) / (Real.sqrt π * Real.Gamma (l + 1 / 2))

/-- `J(λ,n) = ∫_{-1}^1 u^{2n} (1-u²)^{λ-1/2} du`. -/
noncomputable def J (l : ℝ) (n : ℕ) : ℝ := ∫ u in (-1:ℝ)..1, u ^ (2 * n) * (1 - u ^ 2) ^ (l - 1 / 2)

theorem weight_int {l : ℝ} (hl : -1/2 < l) :
    IntervalIntegrable (fun u : ℝ => (1 - u ^ 2) ^ (l - 1 / 2)) volume (-1) 1 :=
  (sym_weight (by linarith)).1

theorem poly_weight_int {l : ℝ} (hl : -1/2 < l) (k : ℕ) :
    IntervalIntegrable (fun u : ℝ => u ^ k * (1 - u ^ 2) ^ (l - 1 / 2)) volume (-1) 1 :=
  (weight_int hl).continuousOn_mul (continuous_pow k).continuousOn

theorem J_zero {l : ℝ} (hl : -1/2 < l) : J l 0 = Real.sqrt π * Real.Gamma (l + 1 / 2) / Real.Gamma (l + 1) := by
  have h := (sym_weight (s := l - 1 / 2) (by linarith)).2
  unfold J
  simp only [mul_zero, pow_zero, one_mul]
  rw [h, show 2 * (l - 1 / 2) + 1 = 2 * l by ring, show l - 1 / 2 + 1 = l + 1 / 2 by ring,
    show 2 * (l - 1 / 2) + 2 = 2 * (l + 1 / 2) by ring]
  have hd := Real.Gamma_mul_Gamma_add_half (l + 1 / 2)
  rw [show l + 1 / 2 + 1 / 2 = l + 1 by ring, show 1 - 2 * (l + 1 / 2) = -(2 * l) by ring] at hd
  have hG1 : 0 < Real.Gamma (l + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hG2 : 0 < Real.Gamma (l + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hG3 : 0 < Real.Gamma (2 * (l + 1 / 2)) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : (0:ℝ) < 2 ^ (2 * l) := by positivity
  have hneg : (2:ℝ) ^ (-(2 * l)) = (2 ^ (2 * l))⁻¹ := Real.rpow_neg (by norm_num) _
  rw [hneg, show 2 * (l + 1 / 2) = 2 * l + 1 by ring] at hd
  rw [show 2 * (l + 1 / 2) = 2 * l + 1 by ring]
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hG3eq : Real.Gamma (2 * l + 1) = Real.Gamma (l + 1 / 2) * Real.Gamma (l + 1) * 2 ^ (2 * l) / Real.sqrt π := by
    rw [eq_div_iff hs.ne', hd]; field_simp
  rw [hG3eq]
  field_simp

theorem J_succ {l : ℝ} (hl : -1/2 < l) (n : ℕ) :
    J l (n + 1) = (2 * n + 1) / (2 * n + 2 * l + 2) * J l n := by
  set p := l + 1 / 2 with hp
  have hp0 : 0 < p := by rw [hp]; linarith
  set F : ℝ → ℝ := fun u => u ^ (2 * n + 1) * (1 - u ^ 2) ^ p with hF
  set F' : ℝ → ℝ := fun u => (2 * n + 1) * (u ^ (2 * n) * (1 - u ^ 2) ^ p) -
    (2 * p) * (u ^ (2 * n + 2) * (1 - u ^ 2) ^ (l - 1 / 2)) with hF'
  have hpow : ∀ u : ℝ, 0 ≤ 1 - u ^ 2 → (1 - u ^ 2) ^ p = (1 - u ^ 2) * (1 - u ^ 2) ^ (l - 1 / 2) := by
    intro u hu
    rw [show p = (l - 1 / 2) + 1 by rw [hp]; ring, Real.rpow_add_one' hu (by linarith)]
    ring
  have hcont : ContinuousOn F (Icc (-1) 1) := by
    apply ContinuousOn.mul (continuous_pow _).continuousOn
    exact ContinuousOn.rpow_const (by fun_prop) (fun _ _ => Or.inr hp0.le)
  have hderiv : ∀ u ∈ Ioo (-1:ℝ) 1, HasDerivAt F (F' u) u := by
    intro u hu
    have hb : 0 < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
    have h1 : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (-(2 * u)) u := by
      simpa using (hasDerivAt_pow 2 u).const_sub 1
    have h2 := h1.rpow_const (p := p) (Or.inl hb.ne')
    have h3 := (hasDerivAt_pow (2 * n + 1) u).mul h2
    convert h3 using 1
    rw [hF', show p - 1 = l - 1 / 2 by rw [hp]; ring]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.add_sub_cancel]
    ring
  have hint1 : IntervalIntegrable (fun u : ℝ => u ^ (2 * n) * (1 - u ^ 2) ^ p) volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul (continuous_pow _).continuousOn
    exact ContinuousOn.rpow_const (by fun_prop) (fun _ _ => Or.inr hp0.le)
  have hint2 := poly_weight_int hl (2 * n + 2)
  have hint : IntervalIntegrable F' volume (-1) 1 :=
    (hint1.const_mul _).sub (hint2.const_mul _)
  have hFTC := integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hderiv hint
  have hF1 : F 1 = 0 := by simp [hF, Real.zero_rpow hp0.ne']
  have hFm1 : F (-1) = 0 := by simp [hF, Real.zero_rpow hp0.ne']
  rw [hF1, hFm1, sub_zero] at hFTC
  rw [hF', intervalIntegral.integral_sub (hint1.const_mul _) (hint2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hFTC
  -- ∫ u^{2n}(1-u²)^p = J n - J (n+1)
  have hsplit : ∫ u in (-1:ℝ)..1, u ^ (2 * n) * (1 - u ^ 2) ^ p = J l n - J l (n + 1) := by
    unfold J
    rw [← intervalIntegral.integral_sub (poly_weight_int hl (2 * n)) (by
      simpa [show 2 * (n + 1) = 2 * n + 2 by ring] using poly_weight_int hl (2 * n + 2))]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    have hb : 0 ≤ 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
    simp only
    rw [hpow u hb, show 2 * (n + 1) = 2 * n + 2 by ring]
    ring
  have hJ1 : ∫ u in (-1:ℝ)..1, u ^ (2 * n + 2) * (1 - u ^ 2) ^ (l - 1 / 2) = J l (n + 1) := by
    unfold J; rw [show 2 * (n + 1) = 2 * n + 2 by ring]
  rw [hsplit, hJ1] at hFTC
  have hden : (2 * (n:ℝ) + 2 * l + 2) ≠ 0 := by
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  rw [hp] at hFTC
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination (-1:ℝ) * hFTC

/-- `J(λ,n)/J(λ,0) = (1/2)_n/(λ+1)_n`. -/
theorem J_ratio {l : ℝ} (hl : -1/2 < l) (n : ℕ) :
    J l n = (ascPochhammer ℝ n).eval (1 / 2) / (ascPochhammer ℝ n).eval (l + 1) * J l 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [J_succ hl, ih, ascPochhammer_succ_eval, ascPochhammer_succ_eval]
    have hpos : 0 < (ascPochhammer ℝ n).eval (l + 1) :=
      ascPochhammer_pos n (l + 1) (by linarith)
    have h2 : (2 * (n:ℝ) + 2 * l + 2) ≠ 0 := by
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have h3 : (l + 1 + n) ≠ 0 := by
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rw [show (2 * (n:ℝ) + 1) / (2 * n + 2 * l + 2) = (1 / 2 + n) / (l + 1 + n) by
      rw [div_eq_div_iff h2 h3]; ring]
    field_simp

/-- The density of `ν_λ`. -/
noncomputable def dens (l u : ℝ) : ℝ := if u ∈ Ioo (-1:ℝ) 1 then cl l * (1 - u ^ 2) ^ (l - 1 / 2) else 0

theorem dens_nonneg {l : ℝ} (hl : -1/2 < l) (u : ℝ) : 0 ≤ dens l u := by
  unfold dens
  split_ifs with h
  · apply mul_nonneg
    · unfold cl
      exact div_nonneg (Real.Gamma_pos_of_pos (by linarith)).le
        (mul_nonneg (Real.sqrt_nonneg _) (Real.Gamma_pos_of_pos (by linarith)).le)
    · exact Real.rpow_nonneg (by nlinarith [h.1, h.2]) _
  · exact le_rfl

theorem measurable_dens (l : ℝ) : Measurable (dens l) := by
  unfold dens
  exact Measurable.ite measurableSet_Ioo (by fun_prop) measurable_const

/-- Definition 2.1: the ultraspherical measure `ν_λ`. -/
noncomputable def ν (l : ℝ) : Measure ℝ := volume.withDensity (fun u => ENNReal.ofReal (dens l u))

/-- Integrals against `ν_λ` are interval integrals against the density. -/
theorem integral_ν {l : ℝ} (hl : -1/2 < l) (f : ℝ → ℂ) :
    ∫ u, f u ∂(ν l) = ∫ u in (-1:ℝ)..1, ((cl l * (1 - u ^ 2) ^ (l - 1 / 2) : ℝ) : ℂ) * f u := by
  rw [ν, integral_withDensity_eq_integral_toReal_smul (measurable_dens l).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (dens_nonneg hl _)]
  rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo (-1:ℝ) 1)
      (fun u hu => by simp [dens, hu])]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  simp [dens, hu, Complex.real_smul]

theorem cl_mul_J0 {l : ℝ} (hl : -1/2 < l) : cl l * J l 0 = 1 := by
  rw [J_zero hl, cl]
  have hG1 : 0 < Real.Gamma (l + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hG2 : 0 < Real.Gamma (l + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  rw [div_mul_div_comm, div_eq_one_iff_eq (by positivity)]
  ring

/-- The monomial moments `∫ u^k dν_λ` as interval integrals. -/
theorem moment_eq {l : ℝ} (hl : -1/2 < l) (k : ℕ) :
    ∫ u, ((u ^ k : ℝ) : ℂ) ∂(ν l) =
      ((cl l * ∫ u in (-1:ℝ)..1, u ^ k * (1 - u ^ 2) ^ (l - 1 / 2) : ℝ) : ℂ) := by
  rw [integral_ν hl, show (cl l * ∫ u in (-1:ℝ)..1, u ^ k * (1 - u ^ 2) ^ (l - 1 / 2)) =
      ∫ u in (-1:ℝ)..1, cl l * (u ^ k * (1 - u ^ 2) ^ (l - 1 / 2)) from
    (intervalIntegral.integral_const_mul _ _).symm, ← intervalIntegral.integral_ofReal]
  congr 1
  funext u
  push_cast
  ring

/-- **Proposition 3.1**, normalisation: `ν_λ` is a probability measure. -/
theorem isProbability {l : ℝ} (hl : -1/2 < l) : IsProbabilityMeasure (ν l) := by
  constructor
  rw [ν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · have h := moment_eq hl 0
    simp only [pow_zero, Complex.ofReal_one] at h
    rw [integral_ν hl] at h
    have h2 : ∫ u, dens l u = cl l * J l 0 := by
      have := congrArg Complex.re h
      have hint : ∫ u, dens l u = ∫ u in (-1:ℝ)..1, cl l * (1 - u ^ 2) ^ (l - 1 / 2) := by
        rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo,
          ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo (-1:ℝ) 1)
            (fun u hu => by simp [dens, hu])]
        exact setIntegral_congr_fun measurableSet_Ioo fun u hu => by simp [dens, hu]
      rw [hint, intervalIntegral.integral_const_mul]
      unfold J; simp
    rw [h2, cl_mul_J0 hl, ENNReal.ofReal_one]
  · have : IntervalIntegrable (fun u => cl l * (1 - u ^ 2) ^ (l - 1 / 2)) volume (-1) 1 :=
      (weight_int hl).const_mul _
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)] at this
    refine (integrableOn_iff_integrable_of_support_subset (s := Ioo (-1) 1) ?_).mp ?_
    · intro u hu; by_contra h; exact hu (by simp [dens, h])
    · refine this.congr_fun (fun u hu => by simp [dens, hu]) measurableSet_Ioo
  · exact Filter.Eventually.of_forall (dens_nonneg hl)

/-- **Proposition 3.1**, even moments: `m_{2n}(λ) = (1/2)_n/(λ+1)_n`. -/
theorem moment_even {l : ℝ} (hl : -1/2 < l) (n : ℕ) :
    ∫ u, ((u ^ (2 * n) : ℝ) : ℂ) ∂(ν l) =
      (((ascPochhammer ℝ n).eval (1 / 2) / (ascPochhammer ℝ n).eval (l + 1) : ℝ) : ℂ) := by
  rw [moment_eq hl]
  have : ∫ u in (-1:ℝ)..1, u ^ (2 * n) * (1 - u ^ 2) ^ (l - 1 / 2) = J l n := rfl
  rw [this, J_ratio hl n]
  congr 1
  rw [show cl l * ((ascPochhammer ℝ n).eval (1 / 2) / (ascPochhammer ℝ n).eval (l + 1) * J l 0) =
    (ascPochhammer ℝ n).eval (1 / 2) / (ascPochhammer ℝ n).eval (l + 1) * (cl l * J l 0) by ring,
    cl_mul_J0 hl, mul_one]

/-- **Proposition 3.1**, odd moments vanish. -/
theorem moment_odd {l : ℝ} (hl : -1/2 < l) (n : ℕ) :
    ∫ u, ((u ^ (2 * n + 1) : ℝ) : ℂ) ∂(ν l) = 0 := by
  rw [moment_eq hl]
  have h := intervalIntegral.integral_comp_neg
    (fun u : ℝ => u ^ (2 * n + 1) * (1 - u ^ 2) ^ (l - 1 / 2)) (a := -1) (b := 1)
  simp only [neg_neg] at h
  have hodd : ∀ u : ℝ, (-u) ^ (2 * n + 1) * (1 - (-u) ^ 2) ^ (l - 1 / 2) =
      -(u ^ (2 * n + 1) * (1 - u ^ 2) ^ (l - 1 / 2)) := by
    intro u; rw [Odd.neg_pow ⟨n, rfl⟩, neg_sq]; ring
  simp only [hodd, intervalIntegral.integral_neg] at h
  have : ∫ u in (-1:ℝ)..1, u ^ (2 * n + 1) * (1 - u ^ 2) ^ (l - 1 / 2) = 0 := by linarith
  rw [this]; simp

end GegenbauerFock.Manuscript13
