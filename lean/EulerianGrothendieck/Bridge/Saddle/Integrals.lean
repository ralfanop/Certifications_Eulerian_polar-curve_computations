import Bridge.Saddle.InnerBound

/-!
# Lemma 5.5, part 10: the integrals `I_r = ∫ (iz)^r χ(s, εz)^M dz`, `r = 0, 1, 2`

* `exists_rho`: `|χ(s,u)| ≤ ρ < 1` for `|s| ≤ σ`, `|u| ≥ δ` (outer region, (121));
* `integral_main`: `∫ (iz)^r e^{-κ₂z²/2} T dz = √(2π/κ₂) N_r(ε)` with an explicit polynomial
  `N_r = Σ_k τ_k μ_{r+k}` (Gaussian moments after (129));
* `Ir_expansion`: `|I_r - √(2π/κ₂) N_r(ε)| ≤ C ε⁵`, uniformly for `|s| ≤ σ`, `M ≥ 4`, `Mε² = 1`.
-/

open MeasureTheory Set Complex Filter Topology Metric
open scoped Nat

namespace EulerianBridge.Saddle

/-! ## `|χ|` -/

theorem norm_χ_eq (s u : ℝ) : ‖χ s u‖ = ‖A ((s:ℂ) + u * I)‖ / Ar s := by
  unfold χ
  rw [norm_mul, norm_div, A_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Ar_pos s),
    κc_ofReal]
  have : -((u:ℂ) * I) * (κ 1 s : ℂ) = ((-(u * κ 1 s) : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem norm_χ_le_A (s u : ℝ) : ‖χ s u‖ ≤ ‖A ((s:ℂ) + u * I)‖ := by
  rw [norm_χ_eq]
  exact div_le_self (norm_nonneg _) (one_le_Ar s)

theorem norm_χ_le_one (s u : ℝ) : ‖χ s u‖ ≤ 1 := by
  rw [norm_χ_eq, div_le_one (Ar_pos s)]
  have := norm_A_le_Ar ((s:ℂ) + u * I)
  simpa using this

theorem continuous_χ (s : ℝ) : Continuous (χ s) := by
  unfold χ
  have : Continuous fun u : ℝ => A ((s:ℂ) + u * I) := continuous_A.comp (by fun_prop)
  fun_prop

/-- Uniform contraction in the outer region. -/
theorem exists_rho {σ δ : ℝ} (hσ : 0 ≤ σ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ ρ : ℝ, 1 / 2 ≤ ρ ∧ ρ < 1 ∧ ∀ s, |s| ≤ σ → ∀ u, δ ≤ |u| → ‖χ s u‖ ≤ ρ := by
  set U : ℝ := 4 * Real.exp (σ / 2) + 1
  have hU : 1 ≤ U := by have := Real.exp_pos (σ / 2); simp only [U]; linarith
  set K : Set (ℝ × ℝ) := Icc (-σ) σ ×ˢ (Icc (-U) U ∩ {u | δ ≤ |u|})
  have hK : IsCompact K := by
    apply isCompact_Icc.prod
    exact isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hne : K.Nonempty := ⟨(0, δ), ⟨⟨by linarith, hσ⟩, ⟨⟨by linarith, by linarith⟩, by
    simp [abs_of_pos hδ0]⟩⟩⟩
  set f : ℝ × ℝ → ℝ := fun p => ‖A ((p.1:ℂ) + p.2 * I)‖ / (A (p.1:ℂ)).re
  have hf : Continuous f := by
    apply Continuous.div
    · exact continuous_norm.comp (continuous_A.comp (by fun_prop))
    · exact Complex.continuous_re.comp (continuous_A.comp (by fun_prop))
    · intro p; rw [A_ofReal]; simp only [Complex.ofReal_re]; exact (Ar_pos _).ne'
  obtain ⟨p0, hp0, hmax⟩ := hK.exists_isMaxOn hne hf.continuousOn
  have hfeq : ∀ s u : ℝ, f (s, u) = ‖χ s u‖ := by
    intro s u; simp only [f]; rw [norm_χ_eq, A_ofReal]; simp
  have hp0lt : f p0 < 1 := by
    obtain ⟨p1, p2⟩ := p0
    rw [hfeq]
    have hu : p2 ≠ 0 := by
      intro h; have := hp0.2.2; simp only [mem_setOf_eq, h, abs_zero] at this; linarith
    rw [norm_χ_eq, div_lt_one (Ar_pos _)]
    exact norm_A_lt p1 hu
  refine ⟨max (f p0) (1 / 2), le_max_right _ _, max_lt hp0lt (by norm_num), fun s hs u hu => ?_⟩
  by_cases hU' : |u| ≤ U
  · have hmem : (s, u) ∈ K := ⟨abs_le.mp hs, ⟨abs_le.mp hU', hu⟩⟩
    rw [← hfeq]; exact (hmax hmem).trans (le_max_left _ _)
  · push_neg at hU'
    refine le_trans ?_ (le_max_right _ _)
    refine (norm_χ_le_A s u).trans ?_
    have hz : (s:ℂ) + u * I ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this
      rw [this] at hU'; simp at hU'; linarith
    refine (norm_A_decay hz).trans ?_
    have hre : ((s:ℂ) + u * I).re = s := by simp
    have hn : |u| ≤ ‖(s:ℂ) + u * I‖ := by
      have := Complex.abs_im_le_norm ((s:ℂ) + u * I); simpa using this
    rw [hre, div_le_iff₀ (by linarith)]
    have : Real.exp (|s| / 2) ≤ Real.exp (σ / 2) := Real.exp_le_exp.mpr (by linarith)
    simp only [U] at hU'
    linarith

/-! ## Majorants -/

/-- `|w|^r |A(w)|^M ≤ 2^r · 8 e^{M|Re w|/2} (1 + (Im w)²)⁻¹` for `M ≥ r + 2`. -/
theorem norm_pow_A_le {M r : ℕ} (h : r + 2 ≤ M) (w : ℂ) :
    ‖w‖ ^ r * ‖A w‖ ^ M ≤ 2 ^ r * 8 * Real.exp (|w.re| / 2) ^ M * (1 + w.im ^ 2)⁻¹ := by
  have h1 := norm_A_pow_mul_le M r h w
  have h2 := inv_four_add_le (z := w)
  calc ‖w‖ ^ r * ‖A w‖ ^ M = ‖A w‖ ^ M * ‖w‖ ^ r := by ring
    _ ≤ 2 ^ r * 8 * Real.exp (|w.re| / 2) ^ M / (4 + ‖w‖ ^ 2) := h1
    _ = 2 ^ r * 8 * Real.exp (|w.re| / 2) ^ M * (1 / (4 + ‖w‖ ^ 2)) := by ring
    _ ≤ 2 ^ r * 8 * Real.exp (|w.re| / 2) ^ M * (1 + w.im ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

theorem abs_z_pow_le {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) {M : ℕ} (hMe : (M:ℝ) * e ^ 2 = 1)
    {r : ℕ} (hr : r ≤ 2) (s z : ℝ) : |z| ^ r ≤ M * ‖(s:ℂ) + ((e * z : ℝ):ℂ) * I‖ ^ r := by
  have hn : e * |z| ≤ ‖(s:ℂ) + ((e * z : ℝ):ℂ) * I‖ := by
    have := Complex.abs_im_le_norm ((s:ℂ) + ((e * z : ℝ):ℂ) * I)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at this
    rwa [abs_mul, abs_of_pos he0] at this
  have hz : |z| ^ r = (e * |z|) ^ r * ((e⁻¹) ^ r) := by
    rw [← mul_pow]; congr 1; field_simp
  have hinv : (e⁻¹) ^ r ≤ M := by
    have hM : (M:ℝ) = (e⁻¹) ^ 2 := by
      rw [inv_pow]; exact eq_inv_of_mul_eq_one_left hMe
    rw [hM]
    exact pow_le_pow_right₀ (one_le_inv₀ he0 |>.mpr he1) hr
  rw [hz]
  calc (e * |z|) ^ r * (e⁻¹) ^ r ≤ ‖(s:ℂ) + ((e * z : ℝ):ℂ) * I‖ ^ r * M := by
        gcongr
    _ = _ := by ring

/-! ## The Gaussian main term -/

/-- Coefficients of `T` as a polynomial in `t = iz`. -/
noncomputable def τc (s e : ℝ) : ℕ → ℂ
  | 0 => 1
  | 3 => (e:ℂ) * ac 3 s
  | 4 => (e:ℂ) ^ 2 * ac 4 s
  | 5 => (e:ℂ) ^ 3 * ac 5 s
  | 6 => (e:ℂ) ^ 2 * (ac 3 s ^ 2 / 2) + (e:ℂ) ^ 4 * ac 6 s
  | 7 => (e:ℂ) ^ 3 * (ac 3 s * ac 4 s)
  | 8 => (e:ℂ) ^ 4 * (ac 3 s * ac 5 s + ac 4 s ^ 2 / 2)
  | 9 => (e:ℂ) ^ 3 * (ac 3 s ^ 3 / 6)
  | 10 => (e:ℂ) ^ 4 * (ac 3 s ^ 2 * ac 4 s / 2)
  | 12 => (e:ℂ) ^ 4 * (ac 3 s ^ 4 / 24)
  | _ => 0

theorem Tz_eq_sum (s e z : ℝ) :
    Tz s e z = ∑ k ∈ Finset.range 13, τc s e k * ((z:ℂ) * I) ^ k := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, τc, Tz, Tpoly, bz]
  ring

/-- `N_r(ε) = Σ_k τ_k μ_{r+k}`. -/
noncomputable def Nexp (s e : ℝ) (r : ℕ) : ℂ :=
  ∑ k ∈ Finset.range 13, τc s e k * μ (κ 2 s) (r + k)

theorem integrable_main (s e : ℝ) (r : ℕ) :
    Integrable (fun z : ℝ => ((z:ℂ) * I) ^ r * (Real.exp (-(κ 2 s * z ^ 2) / 2) : ℂ) * Tz s e z) := by
  have hκ := κ_two_pos s
  have heq : (fun z : ℝ => ((z:ℂ) * I) ^ r * (Real.exp (-(κ 2 s * z ^ 2) / 2) : ℂ) * Tz s e z) =
      fun z : ℝ => ∑ k ∈ Finset.range 13, τc s e k *
        (((z:ℂ) * I) ^ (r + k) * (Real.exp (-(κ 2 s * z ^ 2) / 2) : ℂ)) := by
    funext z; rw [Tz_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [heq]
  exact integrable_finset_sum _ (fun k _ => (integrable_complex_moment hκ (r + k)).const_mul _)

theorem integral_main (s e : ℝ) (r : ℕ) :
    ∫ z : ℝ, ((z:ℂ) * I) ^ r * (Real.exp (-(κ 2 s * z ^ 2) / 2) : ℂ) * Tz s e z =
      (Real.sqrt (2 * Real.pi / κ 2 s) : ℂ) * Nexp s e r := by
  have hκ := κ_two_pos s
  have heq : (fun z : ℝ => ((z:ℂ) * I) ^ r * (Real.exp (-(κ 2 s * z ^ 2) / 2) : ℂ) * Tz s e z) =
      fun z : ℝ => ∑ k ∈ Finset.range 13, τc s e k *
        (((z:ℂ) * I) ^ (r + k) * (Real.exp (-(κ 2 s * z ^ 2) / 2) : ℂ)) := by
    funext z; rw [Tz_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [heq, integral_finset_sum _ (fun k _ => (integrable_complex_moment hκ (r + k)).const_mul _)]
  simp_rw [MeasureTheory.integral_const_mul, integral_complex_moment hκ]
  rw [Nexp, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _; ring

/-! ## Bounds on `T` -/

theorem norm_Tz_le {σ s : ℝ} (hσ : 0 ≤ σ) (hs : |s| ≤ σ) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (z : ℝ) : ‖Tz s e z‖ ≤ 10 * (1 + Kp σ) ^ 4 * (1 + z ^ 2) ^ 24 := by
  have hω1 : (1:ℝ) ≤ 1 + z ^ 2 := by nlinarith [sq_nonneg z]
  set ω := 1 + z ^ 2
  set β := Kp σ * ω ^ 6
  have hK := Kp_nonneg hσ
  have hβ0 : 0 ≤ β := by positivity
  have hb : ∀ n : ℕ, 3 ≤ n → n ≤ 6 → ‖bz n s z‖ ≤ β := by
    intro n h3 h6
    have h := norm_bz_le hσ hs h6 z
    have hB := (Bσ_pos hσ).le
    have hR := (Rσ_pos σ).le
    have hKn : Bσ σ / Rσ σ ^ n ≤ Kp σ := by
      have t3 := div_nonneg hB (pow_nonneg hR 3)
      have t4 := div_nonneg hB (pow_nonneg hR 4)
      have t5 := div_nonneg hB (pow_nonneg hR 5)
      have t6 := div_nonneg hB (pow_nonneg hR 6)
      interval_cases n <;> simp only [Kp] <;> linarith
    exact h.trans (mul_le_mul_of_nonneg_right hKn (by positivity))
  have h3 := hb 3 le_rfl (by norm_num)
  have h4 := hb 4 (by norm_num) (by norm_num)
  have h5 := hb 5 (by norm_num) (by norm_num)
  have h6 := hb 6 (by norm_num) le_rfl
  have hE : ‖(e:ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he0]; exact he1
  have hT : ‖Tz s e z‖ ≤ 10 * (1 + β) ^ 4 := by
    unfold Tz Tpoly
    set b3 := bz 3 s z; set b4 := bz 4 s z; set b5 := bz 5 s z; set b6 := bz 6 s z
    have hb2 : ‖b3 ^ 2 / 2‖ ≤ β ^ 2 := by
      rw [norm_div, norm_pow]
      have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
      rw [h2]
      have := pow_le_pow_left₀ (norm_nonneg _) h3 2
      have := sq_nonneg β
      linarith
    have hb33 : ‖b3 ^ 3 / 6‖ ≤ β ^ 3 := by
      rw [norm_div, norm_pow]
      have h2 : ‖(6:ℂ)‖ = 6 := by norm_num
      rw [h2]
      have := pow_le_pow_left₀ (norm_nonneg _) h3 3
      have := pow_nonneg hβ0 3
      linarith
    have hb34 : ‖b3 ^ 4 / 24‖ ≤ β ^ 4 := by
      rw [norm_div, norm_pow]
      have h2 : ‖(24:ℂ)‖ = 24 := by norm_num
      rw [h2]
      have := pow_le_pow_left₀ (norm_nonneg _) h3 4
      have := pow_nonneg hβ0 4
      linarith
    have hm : ∀ x y : ℂ, ‖x‖ ≤ β → ‖y‖ ≤ β → ‖x * y‖ ≤ β ^ 2 := by
      intro x y hx hy; rw [norm_mul, sq]; exact mul_le_mul hx hy (norm_nonneg _) hβ0
    have hb42 : ‖b4 ^ 2 / 2‖ ≤ β ^ 2 := by
      rw [norm_div, norm_pow]
      have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
      rw [h2]
      have := pow_le_pow_left₀ (norm_nonneg _) h4 2
      have := sq_nonneg β
      linarith
    have hb324 : ‖b3 ^ 2 * b4 / 2‖ ≤ β ^ 3 := by
      rw [norm_div, norm_mul, norm_pow]
      have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
      rw [h2]
      have := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h3 2) h4 (norm_nonneg _) (by positivity)
      have h3' : β ^ 2 * β = β ^ 3 := by ring
      rw [h3'] at this
      have := pow_nonneg hβ0 3
      linarith
    have hp : ∀ (k : ℕ) (x : ℂ), ‖(e:ℂ) ^ k * x‖ ≤ ‖x‖ := by
      intro k x; rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hE)
    have hp1 : ∀ x : ℂ, ‖(e:ℂ) * x‖ ≤ ‖x‖ := by
      intro x; rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hE
    have e1 : ‖(e:ℂ) * b3‖ ≤ β := (hp1 _).trans h3
    have e2 : ‖(e:ℂ) ^ 2 * (b4 + b3 ^ 2 / 2)‖ ≤ β + β ^ 2 :=
      (hp 2 _).trans ((norm_add_le _ _).trans (add_le_add h4 hb2))
    have e3 : ‖(e:ℂ) ^ 3 * (b5 + b3 * b4 + b3 ^ 3 / 6)‖ ≤ β + β ^ 2 + β ^ 3 :=
      (hp 3 _).trans ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add h5 (hm _ _ h3 h4))) hb33))
    have e4 : ‖(e:ℂ) ^ 4 * (b6 + b3 * b5 + b4 ^ 2 / 2 + b3 ^ 2 * b4 / 2 + b3 ^ 4 / 24)‖ ≤
        β + β ^ 2 + β ^ 2 + β ^ 3 + β ^ 4 :=
      (hp 4 _).trans ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add h6 (hm _ _ h3 h5))) hb42)) hb324)) hb34))
    have hsum := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (le_of_eq norm_one)
        e1)) e2)) e3)) e4)
    refine hsum.trans ?_
    have hb1 : β ≤ (1 + β) ^ 4 := by
      have : β ≤ 1 + β := by linarith
      exact this.trans (le_self_pow₀ (by linarith) (by norm_num))
    have hb2' : β ^ 2 ≤ (1 + β) ^ 4 :=
      (pow_le_pow_left₀ hβ0 (by linarith) 2).trans (pow_le_pow_right₀ (by linarith) (by norm_num))
    have hb3' : β ^ 3 ≤ (1 + β) ^ 4 :=
      (pow_le_pow_left₀ hβ0 (by linarith) 3).trans (pow_le_pow_right₀ (by linarith) (by norm_num))
    have hb4' : β ^ 4 ≤ (1 + β) ^ 4 := pow_le_pow_left₀ hβ0 (by linarith) 4
    have h1' : (1:ℝ) ≤ (1 + β) ^ 4 := one_le_pow₀ (by linarith)
    linarith
  refine hT.trans ?_
  have : 1 + β ≤ (1 + Kp σ) * ω ^ 6 := by
    have : (1:ℝ) ≤ ω ^ 6 := one_le_pow₀ hω1
    simp only [β]; nlinarith
  calc 10 * (1 + β) ^ 4 ≤ 10 * ((1 + Kp σ) * ω ^ 6) ^ 4 := by gcongr
    _ = 10 * (1 + Kp σ) ^ 4 * ω ^ 24 := by ring

end EulerianBridge.Saddle
