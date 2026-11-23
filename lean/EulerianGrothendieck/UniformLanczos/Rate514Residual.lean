import Mathlib

/-! # Manuscript 12, proof of Theorem 5.14: the residual bounds (163)

* `residual_a_bound`: with Freud's identity (152) and the spectral representation of
  `f(J(a))` (published results cited), `R_k(a) = ∫ (f - φ'_M) p_k p_{k-1} g_M dx`; on
  `|x| < r` Lemma 5.5 gives `|f - φ'_M| ≤ A/M` and Cauchy–Schwarz gives
  `∫ |p_k p_{k-1}| g_M ≤ 1`; off it, `|f| ≤ C_f` and the two tails of Lemma 5.13 apply:
  `|R_k(a)| ≤ A/M + C_f T₁ + T₂`.
* `locality_bound`: along the segment from `v` to `u` (fundamental theorem of calculus and
  linearity of the Fréchet derivative, published results cited),
  `[f(J(u)) - f(J(v))]_{kl} = ∫_0^1 Σ_m (u_m - v_m) K_m(τ) dτ`; the kernel bound of
  Lemma 5.12 then gives (153).
* `residual_b_bound`: comparing `b` with the constant sequence `b_k` (whose entry is
  `k/(M b_k)` by (162)), with `|b_m - b_k| ≤ L|m-k|/M`, gives `|R_k(b)| ≤ C_f L Z₁/M`, where
  `Z₁ = Σ_n |n| (1+|n|)^{-5}`. -/

namespace UniformLanczos.Rate514Residual

open MeasureTheory Set

/-- **`|R_k(a)| ≤ C/M`, (163) first half.** -/
theorem residual_a_bound (μ : Measure ℝ) (f φ' pk pk1 : ℝ → ℝ) {r A M Cf T₁ T₂ R : ℝ}
    (hM : 0 < M) (hA : 0 ≤ A) (hCf : 0 ≤ Cf)
    (hR : R = ∫ x, (f x - φ' x) * (pk x * pk1 x) ∂μ)
    (hint : Integrable (fun x => (f x - φ' x) * (pk x * pk1 x)) μ)
    (hpp : Integrable (fun x => |pk x * pk1 x|) μ)
    (hsq : Integrable (fun x => (pk x ^ 2 + pk1 x ^ 2) / 2) μ)
    (hφp : Integrable (fun x => |φ' x * (pk x * pk1 x)|) μ)
    (hinner : ∀ x, |x| < r → |f x - φ' x| ≤ A / M)
    (hCS : ∫ x, |pk x * pk1 x| ∂μ ≤ 1)
    (hfb : ∀ x, |f x| ≤ Cf)
    (hT₁ : ∫ x in {x | r ≤ |x|}, (pk x ^ 2 + pk1 x ^ 2) / 2 ∂μ ≤ T₁)
    (hT₂ : ∫ x in {x | r ≤ |x|}, |φ' x * (pk x * pk1 x)| ∂μ ≤ T₂) :
    |R| ≤ A / M + Cf * T₁ + T₂ := by
  set S : Set ℝ := {x | r ≤ |x|}
  have hS : MeasurableSet S := measurableSet_le measurable_const continuous_abs.measurable
  have hSc : Sᶜ = {x | |x| < r} := by ext x; simp [S]
  set F := fun x => (f x - φ' x) * (pk x * pk1 x)
  have hFabs : Integrable (fun x => |F x|) μ := hint.abs
  rw [hR, ← integral_add_compl hS hint]
  -- inner part
  have hin : |∫ x in Sᶜ, F x ∂μ| ≤ A / M := by
    calc |∫ x in Sᶜ, F x ∂μ| ≤ ∫ x in Sᶜ, |F x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x in Sᶜ, A / M * |pk x * pk1 x| ∂μ := by
          apply setIntegral_mono_on hFabs.integrableOn (hpp.const_mul _).integrableOn
            hS.compl
          intro x hx
          rw [hSc] at hx
          simp only [F, abs_mul]
          rw [← abs_mul]
          exact mul_le_mul_of_nonneg_right (hinner x hx) (abs_nonneg _)
      _ ≤ ∫ x, A / M * |pk x * pk1 x| ∂μ :=
          setIntegral_le_integral (hpp.const_mul _)
            (Filter.Eventually.of_forall fun x => by positivity)
      _ = A / M * ∫ x, |pk x * pk1 x| ∂μ := integral_const_mul _ _
      _ ≤ A / M * 1 := mul_le_mul_of_nonneg_left hCS (by positivity)
      _ = A / M := mul_one _
  -- outer part
  have hpt : ∀ x, |F x| ≤ Cf * ((pk x ^ 2 + pk1 x ^ 2) / 2) + |φ' x * (pk x * pk1 x)| := by
    intro x
    have hab : |pk x * pk1 x| ≤ (pk x ^ 2 + pk1 x ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|pk x| - |pk1 x|), sq_abs (pk x), sq_abs (pk1 x)]
    simp only [F]
    rw [sub_mul]
    calc |f x * (pk x * pk1 x) - φ' x * (pk x * pk1 x)|
        ≤ |f x * (pk x * pk1 x)| + |φ' x * (pk x * pk1 x)| := abs_sub _ _
      _ ≤ Cf * ((pk x ^ 2 + pk1 x ^ 2) / 2) + |φ' x * (pk x * pk1 x)| := by
          rw [abs_mul (f x)]
          have := mul_le_mul (hfb x) hab (abs_nonneg _) hCf
          linarith
  have hsumI : Integrable (fun x => Cf * ((pk x ^ 2 + pk1 x ^ 2) / 2) +
      |φ' x * (pk x * pk1 x)|) μ := (hsq.const_mul Cf).add hφp
  have hsqC : Integrable (fun x => Cf * ((pk x ^ 2 + pk1 x ^ 2) / 2)) μ := hsq.const_mul Cf
  have hout : |∫ x in S, F x ∂μ| ≤ Cf * T₁ + T₂ := by
    calc |∫ x in S, F x ∂μ| ≤ ∫ x in S, |F x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x in S, (Cf * ((pk x ^ 2 + pk1 x ^ 2) / 2) + |φ' x * (pk x * pk1 x)|) ∂μ :=
          setIntegral_mono_on hFabs.integrableOn hsumI.integrableOn hS (fun x _ => hpt x)
      _ = Cf * ∫ x in S, (pk x ^ 2 + pk1 x ^ 2) / 2 ∂μ +
            ∫ x in S, |φ' x * (pk x * pk1 x)| ∂μ := by
          rw [integral_add hsqC.integrableOn hφp.integrableOn, integral_const_mul]
      _ ≤ Cf * T₁ + T₂ := by
          have := mul_le_mul_of_nonneg_left hT₁ hCf
          linarith
  calc |∫ x in S, F x ∂μ + ∫ x in Sᶜ, F x ∂μ|
      ≤ |∫ x in S, F x ∂μ| + |∫ x in Sᶜ, F x ∂μ| := abs_add_le _ _
    _ ≤ Cf * T₁ + T₂ + A / M := add_le_add hout hin
    _ = A / M + Cf * T₁ + T₂ := by ring

/-- **Locality (153).** If the entry difference is
`∫_0^1 Σ_m (u_m - v_m) K_m(τ) dτ` (fundamental theorem of calculus along the segment and
linearity of the derivative, cited) and `|K_m(τ)| ≤ w_m` with `Σ |u_m - v_m| w_m` summable,
then `|Δ| ≤ Σ_m |u_m - v_m| w_m`. -/
theorem locality_bound (u v w : ℤ → ℝ) (K : ℝ → ℤ → ℝ) (Δ : ℝ)
    (hK : ∀ τ ∈ Icc (0:ℝ) 1, ∀ m, |K τ m| ≤ w m)
    (hsum : Summable fun m => |u m - v m| * w m)
    (hΔ : Δ = ∫ τ in (0:ℝ)..1, ∑' m, (u m - v m) * K τ m) :
    |Δ| ≤ ∑' m, |u m - v m| * w m := by
  have hpt : ∀ τ ∈ Icc (0:ℝ) 1, ‖∑' m, (u m - v m) * K τ m‖ ≤ ∑' m, |u m - v m| * w m := by
    intro τ hτ
    have hb : ∀ m, ‖(u m - v m) * K τ m‖ ≤ |u m - v m| * w m := by
      intro m; rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hK τ hτ m) (abs_nonneg _)
    have hs : Summable fun m => ‖(u m - v m) * K τ m‖ :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _) hb hsum
    exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb hsum)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun τ => ∑' m, (u m - v m) * K τ m) (C := ∑' m, |u m - v m| * w m)
    (fun τ hτ => by rw [uIoc_of_le zero_le_one] at hτ; exact hpt τ ⟨hτ.1.le, hτ.2⟩)
  rw [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at h
  rw [hΔ]; exact h

/-- **`|R_k(b)| ≤ C/M`, (163) second half.** With (162), `R_k(b)` is the difference of the
entries `[f(J(b))]_{k,k-1}` and `[f(J(b_k 1))]_{k,k-1}`; if that difference is bounded by
`Σ_m |b_m - b_k| C_f (1+|k-m|)^{-5}` (locality, (153)) and `|b_m - b_k| ≤ L|m-k|/M`, then
`|R_k(b)| ≤ C_f L Z₁ / M` with `Z₁ = Σ_n |n| (1+|n|)^{-5}`. -/
theorem residual_b_bound (b : ℤ → ℝ) (k : ℤ) {Cf L M Rb : ℝ} (hCf : 0 ≤ Cf)
    (hLip : ∀ m, |b m - b k| ≤ L * |(m:ℝ) - k| / M)
    (hZ : Summable fun n : ℤ => |(n:ℝ)| * ((1 + |(n:ℝ)|) ^ 5)⁻¹)
    (hloc : |Rb| ≤ ∑' m : ℤ, |b m - b k| * (Cf * ((1 + |(k:ℝ) - m|) ^ 5)⁻¹))
    (hsum : Summable fun m : ℤ => |b m - b k| * (Cf * ((1 + |(k:ℝ) - m|) ^ 5)⁻¹)) :
    |Rb| ≤ Cf * L * (∑' n : ℤ, |(n:ℝ)| * ((1 + |(n:ℝ)|) ^ 5)⁻¹) / M := by
  set g : ℤ → ℝ := fun n => |(n:ℝ)| * ((1 + |(n:ℝ)|) ^ 5)⁻¹
  have hg' : Summable fun m : ℤ => Cf * L / M * g (m - k) := by
    have : Summable fun m : ℤ => g (m - k) :=
      (Equiv.subRight k).summable_iff.mpr hZ
    exact this.mul_left _
  have hb : ∀ m : ℤ, |b m - b k| * (Cf * ((1 + |(k:ℝ) - m|) ^ 5)⁻¹) ≤ Cf * L / M * g (m - k) := by
    intro m
    have hsym : |(k:ℝ) - m| = |((m - k : ℤ) : ℝ)| := by push_cast; rw [abs_sub_comm]
    rw [hsym]
    have hw : 0 ≤ Cf * ((1 + |((m - k : ℤ) : ℝ)|) ^ 5)⁻¹ := by positivity
    have hl := hLip m
    have hmk : |(m:ℝ) - k| = |((m - k : ℤ) : ℝ)| := by push_cast; rfl
    rw [hmk] at hl
    calc |b m - b k| * (Cf * ((1 + |((m - k : ℤ) : ℝ)|) ^ 5)⁻¹)
        ≤ L * |((m - k : ℤ) : ℝ)| / M * (Cf * ((1 + |((m - k : ℤ) : ℝ)|) ^ 5)⁻¹) :=
          mul_le_mul_of_nonneg_right hl hw
      _ = Cf * L / M * g (m - k) := by simp only [g]; ring
  have htsum : ∑' m : ℤ, Cf * L / M * g (m - k) = Cf * L / M * ∑' n : ℤ, g n := by
    rw [tsum_mul_left]
    congr 1
    exact (Equiv.subRight k).tsum_eq g
  calc |Rb| ≤ ∑' m : ℤ, |b m - b k| * (Cf * ((1 + |(k:ℝ) - m|) ^ 5)⁻¹) := hloc
    _ ≤ ∑' m : ℤ, Cf * L / M * g (m - k) := hsum.tsum_le_tsum hb hg'
    _ = Cf * L / M * ∑' n : ℤ, g n := htsum
    _ = Cf * L * (∑' n : ℤ, |(n:ℝ)| * ((1 + |(n:ℝ)|) ^ 5)⁻¹) / M := by simp only [g]; ring

end UniformLanczos.Rate514Residual

#print axioms UniformLanczos.Rate514Residual.residual_a_bound
#print axioms UniformLanczos.Rate514Residual.locality_bound
#print axioms UniformLanczos.Rate514Residual.residual_b_bound
