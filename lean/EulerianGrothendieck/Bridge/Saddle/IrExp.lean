import Bridge.Saddle.Integrals

/-!
# Lemma 5.5, part 11: the expansion `I_r = √(2π/κ₂) (N_r(ε) + O(ε⁵))`

`I_r(s) = ∫ (iz)^r χ(s, εz)^M dz` with `Mε² = 1`.  Combining the inner estimate
(`inner_pointwise`), the outer contraction (`exists_rho`) and the Gaussian tails gives, for
`r ≤ 2`, uniformly in `|s| ≤ σ` and `M ≥ 4`,
`|I_r - √(2π/κ₂) N_r(ε)| ≤ C ε⁵`  (`Ir_expansion`).
-/

open MeasureTheory Set Complex Filter Topology Metric
open scoped Nat

namespace EulerianBridge.Saddle

/-- `I_r(s) = ∫ (iz)^r χ(s, εz)^M dz`. -/
noncomputable def Ir (s : ℝ) (M : ℕ) (e : ℝ) (r : ℕ) : ℂ :=
  ∫ z : ℝ, ((z:ℂ) * I) ^ r * χ s (e * z) ^ M

theorem integrable_inv_scaled {e : ℝ} (he : e ≠ 0) :
    Integrable (fun z : ℝ => (1 + (e * z) ^ 2)⁻¹) :=
  integrable_inv_one_add_sq.comp_mul_left' he

theorem integral_inv_scaled {e : ℝ} (he : 0 < e) :
    ∫ z : ℝ, (1 + (e * z) ^ 2)⁻¹ = Real.pi * e⁻¹ := by
  have := Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) e
  simp only at this
  rw [this, integral_univ_inv_one_add_sq, abs_inv, abs_of_pos he, smul_eq_mul, mul_comm]

/-- `|(iz)^r χ(s,εz)^M| ≤ M · 2^r · 8 e^{M|s|/2} (1 + (εz)²)⁻¹`. -/
theorem norm_Ir_integrand_le {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) {M : ℕ} (hMe : (M:ℝ) * e ^ 2 = 1)
    {r : ℕ} (hr : r ≤ 2) (hM : r + 2 ≤ M) (s z : ℝ) :
    ‖((z:ℂ) * I) ^ r * χ s (e * z) ^ M‖ ≤
      M * (2 ^ r * 8 * Real.exp (|s| / 2) ^ M * (1 + (e * z) ^ 2)⁻¹) := by
  set w : ℂ := (s:ℂ) + ((e * z : ℝ):ℂ) * I
  rw [norm_mul, norm_pow, norm_uI, norm_pow]
  have h1 := abs_z_pow_le he0 he1 hMe hr s z
  have h2 : ‖χ s (e * z)‖ ^ M ≤ ‖A w‖ ^ M :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_χ_le_A s (e * z)) M
  have h3 := norm_pow_A_le hM w
  have hre : w.re = s := by simp [w]
  have him : w.im = e * z := by simp [w]
  rw [hre, him] at h3
  calc |z| ^ r * ‖χ s (e * z)‖ ^ M ≤ (M * ‖w‖ ^ r) * ‖A w‖ ^ M :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = M * (‖w‖ ^ r * ‖A w‖ ^ M) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)

theorem integrable_Ir {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) {M : ℕ} (hMe : (M:ℝ) * e ^ 2 = 1)
    {r : ℕ} (hr : r ≤ 2) (hM : r + 2 ≤ M) (s : ℝ) :
    Integrable (fun z : ℝ => ((z:ℂ) * I) ^ r * χ s (e * z) ^ M) := by
  have hb := (integrable_inv_scaled he0.ne').const_mul ((M:ℝ) * (2 ^ r * 8 * Real.exp (|s| / 2) ^ M))
  refine hb.mono' ?_ (Eventually.of_forall (fun z => ?_))
  · have := continuous_χ s
    exact (by fun_prop : Continuous fun z : ℝ => ((z:ℂ) * I) ^ r * χ s (e * z) ^ M).aestronglyMeasurable
  · refine (norm_Ir_integrand_le he0 he1 hMe hr hM s z).trans (le_of_eq ?_)
    ring

/-- Polynomial–Gaussian weight `(1+z²)^{26} e^{-cz²}`. -/
noncomputable def Ew (c z : ℝ) : ℝ := (1 + z ^ 2) ^ 26 * Real.exp (-c * z ^ 2)

theorem Ew_nonneg (c z : ℝ) : 0 ≤ Ew c z := by unfold Ew; positivity

theorem zr_le {r : ℕ} (hr : r ≤ 2) (z : ℝ) : |z| ^ r ≤ (1 + z ^ 2) ^ 2 := by
  have hω1 : (1:ℝ) ≤ 1 + z ^ 2 := by nlinarith [sq_nonneg z]
  exact (pow_le_pow_left₀ (abs_nonneg z) (abs_le_one_add_sq z) r).trans (pow_le_pow_right₀ hω1 hr)

theorem pt_inner {σ c0 δ : ℝ} (hσ : 0 ≤ σ) (hc0 : 0 < c0)
    (hκ : ∀ s, |s| ≤ σ → c0 ≤ κ 2 s) (hδ0 : 0 < δ) (hδR : δ ≤ Rσ σ / 2) (hδ1 : δ ≤ 1)
    (hδK : Kw σ * δ ≤ c0 / 4) {s : ℝ} (hs : |s| ≤ σ) {M : ℕ} {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1)
    (hMe : (M:ℝ) * e ^ 2 = 1) {r : ℕ} (hr : r ≤ 2) {z : ℝ} (hz : e * |z| ≤ δ) :
    ‖((z:ℂ) * I) ^ r * χ s (e * z) ^ M -
      ((z:ℂ) * I) ^ r * (Real.exp (-(κ 2 s * z ^ 2) / 2) : ℂ) * Tz s e z‖ ≤
      e ^ 5 * Cin σ * Ew (c0 / 4) z := by
  have hin := inner_pointwise hσ hc0 hκ hδ0 hδR hδ1 hδK hs he0 he1 hMe hz
  have hfac : ((z:ℂ) * I) ^ r * χ s (e * z) ^ M -
      ((z:ℂ) * I) ^ r * (Real.exp (-(κ 2 s * z ^ 2) / 2) : ℂ) * Tz s e z = ((z:ℂ) * I) ^ r *
        (χ s (e * z) ^ M - (Real.exp (-(κ 2 s * z ^ 2) / 2) : ℂ) * Tz s e z) := by ring
  rw [hfac, norm_mul, norm_pow, norm_uI]
  calc _ ≤ (1 + z ^ 2) ^ 2 * (e ^ 5 * Cin σ * (1 + z ^ 2) ^ 24 * Real.exp (-(c0 / 4) * z ^ 2)) :=
        mul_le_mul (zr_le hr z) hin (norm_nonneg _) (by positivity)
    _ = e ^ 5 * Cin σ * Ew (c0 / 4) z := by unfold Ew; ring

theorem pt_outer_f {σ δ ρ : ℝ} (hρ : ∀ s, |s| ≤ σ → ∀ u, δ ≤ |u| → ‖χ s u‖ ≤ ρ) (hρ0 : 0 ≤ ρ)
    {s : ℝ} (hs : |s| ≤ σ) {M : ℕ} (hM : 4 ≤ M) {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1)
    (hMe : (M:ℝ) * e ^ 2 = 1) {r : ℕ} (hr : r ≤ 2) {z : ℝ} (hu : δ ≤ |e * z|) :
    ‖((z:ℂ) * I) ^ r * χ s (e * z) ^ M‖ ≤
      ρ ^ (M - 4) * M * (32 * Real.exp (σ / 2) ^ 4) * (1 + (e * z) ^ 2)⁻¹ := by
  set w : ℂ := (s:ℂ) + ((e * z : ℝ):ℂ) * I
  rw [norm_mul, norm_pow, norm_uI, norm_pow]
  have hχρ := hρ s hs (e * z) hu
  have hsplit : ‖χ s (e * z)‖ ^ M = ‖χ s (e * z)‖ ^ (M - 4) * ‖χ s (e * z)‖ ^ 4 := by
    rw [← pow_add]; congr 1; omega
  have h1 := abs_z_pow_le he0 he1 hMe hr s z
  have h2 : ‖χ s (e * z)‖ ^ 4 ≤ ‖A w‖ ^ 4 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_χ_le_A s (e * z)) 4
  have h3 := norm_pow_A_le (M := 4) (r := r) (by omega) w
  have hre : w.re = s := by simp [w]
  have him : w.im = e * z := by simp [w]
  rw [hre, him] at h3
  have h4 : (2:ℝ) ^ r ≤ 4 := by
    calc (2:ℝ) ^ r ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hr
      _ = 4 := by norm_num
  have h5 : Real.exp (|s| / 2) ^ 4 ≤ Real.exp (σ / 2) ^ 4 :=
    pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by linarith)) 4
  have h6 : ‖w‖ ^ r * ‖A w‖ ^ 4 ≤ 32 * Real.exp (σ / 2) ^ 4 * (1 + (e * z) ^ 2)⁻¹ := by
    refine h3.trans ?_
    have : 0 ≤ (1 + (e * z) ^ 2)⁻¹ := by positivity
    calc 2 ^ r * 8 * Real.exp (|s| / 2) ^ 4 * (1 + (e * z) ^ 2)⁻¹
        ≤ 4 * 8 * Real.exp (σ / 2) ^ 4 * (1 + (e * z) ^ 2)⁻¹ := by gcongr
      _ = 32 * Real.exp (σ / 2) ^ 4 * (1 + (e * z) ^ 2)⁻¹ := by ring
  rw [hsplit]
  calc |z| ^ r * (‖χ s (e * z)‖ ^ (M - 4) * ‖χ s (e * z)‖ ^ 4)
      ≤ (M * ‖w‖ ^ r) * (ρ ^ (M - 4) * ‖A w‖ ^ 4) := by
        apply mul_le_mul h1 (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hχρ _) h2
          (by positivity) (by positivity)) (by positivity) (by positivity)
    _ = ρ ^ (M - 4) * M * (‖w‖ ^ r * ‖A w‖ ^ 4) := by ring
    _ ≤ ρ ^ (M - 4) * M * (32 * Real.exp (σ / 2) ^ 4 * (1 + (e * z) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = _ := by ring

theorem pt_outer_g {σ c0 δ : ℝ} (hσ : 0 ≤ σ) (hc0 : 0 < c0) {s : ℝ} (hs : |s| ≤ σ)
    (hκs : c0 ≤ κ 2 s) (hδ0 : 0 < δ) {M : ℕ} {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1)
    (hMe : (M:ℝ) * e ^ 2 = 1) {r : ℕ} (hr : r ≤ 2) {z : ℝ} (hz : δ < e * |z|) :
    ‖((z:ℂ) * I) ^ r * (Real.exp (-(κ 2 s * z ^ 2) / 2) : ℂ) * Tz s e z‖ ≤
      Real.exp (-(c0 * δ ^ 2 / 4) * M) * (10 * (1 + Kp σ) ^ 4) * Ew (c0 / 4) z := by
  rw [norm_mul, norm_mul, norm_pow, norm_uI, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hT := norm_Tz_le hσ hs he0.le he1 z
  have h1 : δ ^ 2 ≤ e ^ 2 * z ^ 2 := by
    have h := mul_self_le_mul_self hδ0.le hz.le
    have : e * |z| * (e * |z|) = e ^ 2 * z ^ 2 := by rw [← sq_abs z]; ring
    rw [this] at h
    rw [sq]; exact h
  have h2 : δ ^ 2 * M ≤ z ^ 2 := by
    calc δ ^ 2 * M ≤ e ^ 2 * z ^ 2 * M := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
      _ = z ^ 2 * ((M:ℝ) * e ^ 2) := by ring
      _ = z ^ 2 := by rw [hMe, mul_one]
  have h3 : c0 * z ^ 2 ≤ κ 2 s * z ^ 2 := mul_le_mul_of_nonneg_right hκs (sq_nonneg z)
  have h4 : c0 * (δ ^ 2 * M) ≤ c0 * z ^ 2 := mul_le_mul_of_nonneg_left h2 hc0.le
  have hG : Real.exp (-(κ 2 s * z ^ 2) / 2) ≤
      Real.exp (-(c0 * δ ^ 2 / 4) * M) * Real.exp (-(c0 / 4) * z ^ 2) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have : -(κ 2 s * z ^ 2) / 2 = -(κ 2 s * z ^ 2) / 2 := rfl
    nlinarith
  have hK := Kp_nonneg hσ
  calc |z| ^ r * Real.exp (-(κ 2 s * z ^ 2) / 2) * ‖Tz s e z‖
      ≤ (1 + z ^ 2) ^ 2 * (Real.exp (-(c0 * δ ^ 2 / 4) * M) * Real.exp (-(c0 / 4) * z ^ 2)) *
          (10 * (1 + Kp σ) ^ 4 * (1 + z ^ 2) ^ 24) := by
        gcongr
        exact zr_le hr z
    _ = Real.exp (-(c0 * δ ^ 2 / 4) * M) * (10 * (1 + Kp σ) ^ 4) * Ew (c0 / 4) z := by
        unfold Ew; ring

/-- Bounds `ρ^{M-4} M ε⁻¹ ≤ C ε⁵` and `e^{-aM} ≤ C ε⁵`. -/
theorem geom_term {ρ Cg : ℝ} (hρ0 : 0 < ρ) (hCg : ∀ M : ℕ, (M:ℝ) ^ 5 * ρ ^ M ≤ Cg) {M : ℕ}
    (hM : 4 ≤ M) {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (hMe : (M:ℝ) * e ^ 2 = 1) :
    ρ ^ (M - 4) * M * e⁻¹ ≤ Cg / ρ ^ 4 * e ^ 5 := by
  have hρM : ρ ^ (M - 4) = ρ ^ M / ρ ^ 4 := by
    rw [eq_div_iff (by positivity), ← pow_add]; congr 1; omega
  have heinv : e⁻¹ = M * e := by
    rw [inv_eq_iff_eq_inv, eq_comm, inv_eq_iff_eq_inv]
    field_simp; linarith
  have hM3 : (M:ℝ) ^ 3 * e ^ 6 = 1 := by
    calc (M:ℝ) ^ 3 * e ^ 6 = ((M:ℝ) * e ^ 2) ^ 3 := by ring
      _ = 1 := by rw [hMe, one_pow]
  have hMM : (M:ℝ) * e⁻¹ = (M:ℝ) ^ 5 * e ^ 7 := by
    rw [heinv]
    calc (M:ℝ) * (M * e) = (M:ℝ) ^ 2 * e * ((M:ℝ) ^ 3 * e ^ 6) := by rw [hM3]; ring
      _ = (M:ℝ) ^ 5 * e ^ 7 := by ring
  have e75 : e ^ 7 ≤ e ^ 5 := pow_le_pow_of_le_one he0.le he1 (by norm_num)
  have hC0 : 0 ≤ Cg := le_trans (by positivity) (hCg 0)
  calc ρ ^ (M - 4) * M * e⁻¹ = ((M:ℝ) ^ 5 * ρ ^ M) * e ^ 7 / ρ ^ 4 := by
        rw [hρM, mul_assoc, hMM]; ring
    _ ≤ Cg * e ^ 7 / ρ ^ 4 := by gcongr; exact hCg M
    _ ≤ Cg * e ^ 5 / ρ ^ 4 := by gcongr
    _ = Cg / ρ ^ 4 * e ^ 5 := by ring

theorem exp_term {a Cg : ℝ} (hCg : ∀ M : ℕ, (M:ℝ) ^ 3 * Real.exp (-a) ^ M ≤ Cg) {M : ℕ}
    {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (hMe : (M:ℝ) * e ^ 2 = 1) :
    Real.exp (-a * M) ≤ Cg * e ^ 5 := by
  have hexp : Real.exp (-a * M) = Real.exp (-a) ^ M := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hM3 : (M:ℝ) ^ 3 * e ^ 6 = 1 := by
    calc (M:ℝ) ^ 3 * e ^ 6 = ((M:ℝ) * e ^ 2) ^ 3 := by ring
      _ = 1 := by rw [hMe, one_pow]
  have hC0 : 0 ≤ Cg := le_trans (by positivity) (hCg 0)
  have e65 : e ^ 6 ≤ e ^ 5 := pow_le_pow_of_le_one he0.le he1 (by norm_num)
  rw [hexp]
  calc Real.exp (-a) ^ M = ((M:ℝ) ^ 3 * Real.exp (-a) ^ M) * e ^ 6 := by
        rw [show ((M:ℝ) ^ 3 * Real.exp (-a) ^ M) * e ^ 6 = Real.exp (-a) ^ M * ((M:ℝ) ^ 3 * e ^ 6) by ring,
          hM3, mul_one]
    _ ≤ Cg * e ^ 6 := by gcongr; exact hCg M
    _ ≤ Cg * e ^ 5 := by gcongr

/-- Expansion of `I_r` to fifth order, uniformly in `|s| ≤ σ`. -/
theorem Ir_expansion {σ : ℝ} (hσ : 0 ≤ σ) {r : ℕ} (hr : r ≤ 2) :
    ∃ C : ℝ, ∀ s, |s| ≤ σ → ∀ M : ℕ, 4 ≤ M → ∀ e : ℝ, 0 < e → (M:ℝ) * e ^ 2 = 1 →
      ‖Ir s M e r - (Real.sqrt (2 * Real.pi / κ 2 s) : ℂ) * Nexp s e r‖ ≤ C * e ^ 5 := by
  obtain ⟨c0, hc0, hκ⟩ := exists_κ_two_lower σ
  have hKw := Kw_nonneg hσ
  obtain ⟨δ, hδ0, hδR, hδ1, hδK⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ Rσ σ / 2 ∧ δ ≤ 1 ∧ Kw σ * δ ≤ c0 / 4 := by
    refine ⟨min (Rσ σ / 2) (min 1 (c0 / (4 * (Kw σ + 1)))), ?_, min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), ?_⟩
    · have := Rσ_pos σ
      apply lt_min (by positivity); apply lt_min one_pos; positivity
    · have h1 : min (Rσ σ / 2) (min 1 (c0 / (4 * (Kw σ + 1)))) ≤ c0 / (4 * (Kw σ + 1)) :=
        (min_le_right _ _).trans (min_le_right _ _)
      calc Kw σ * min (Rσ σ / 2) (min 1 (c0 / (4 * (Kw σ + 1))))
          ≤ Kw σ * (c0 / (4 * (Kw σ + 1))) := mul_le_mul_of_nonneg_left h1 hKw
        _ ≤ (Kw σ + 1) * (c0 / (4 * (Kw σ + 1))) := by gcongr; linarith
        _ = c0 / 4 := by field_simp
  obtain ⟨ρ, hρ1, hρ2, hρ⟩ := exists_rho hσ hδ0 hδ1
  have hρ0 : 0 < ρ := by linarith
  have hc : 0 < c0 / 4 := by positivity
  have hΓint : Integrable (fun z => Ew (c0 / 4) z) := integrable_poly_gauss hc 26
  obtain ⟨Cg1, hCg1⟩ := bounded_pow_mul_geom hρ0.le hρ2 5
  have ha : 0 < c0 * δ ^ 2 / 4 := by positivity
  obtain ⟨Cg2, hCg2⟩ := bounded_pow_mul_geom (Real.exp_pos (-(c0 * δ ^ 2 / 4))).le
    (Real.exp_lt_one_iff.mpr (by linarith)) 3
  set Γ : ℝ := ∫ z : ℝ, Ew (c0 / 4) z
  set K : ℝ := Real.exp (σ / 2)
  refine ⟨Cin σ * Γ + 32 * K ^ 4 * Real.pi * (Cg1 / ρ ^ 4) + 10 * (1 + Kp σ) ^ 4 * Γ * Cg2,
    fun s hs M hM e he0 hMe => ?_⟩
  have hM0 : (4:ℝ) ≤ M := by exact_mod_cast hM
  have he1 : e ≤ 1 := by
    by_contra h; push_neg at h
    have : (1:ℝ) < e ^ 2 := by nlinarith
    nlinarith
  set f : ℝ → ℂ := fun z => ((z:ℂ) * I) ^ r * χ s (e * z) ^ M
  set g : ℝ → ℂ := fun z => ((z:ℂ) * I) ^ r * (Real.exp (-(κ 2 s * z ^ 2) / 2) : ℂ) * Tz s e z
  have hf : Integrable f := integrable_Ir he0 he1 hMe hr (by omega) s
  have hg : Integrable g := integrable_main s e r
  have hmain : Ir s M e r - (Real.sqrt (2 * Real.pi / κ 2 s) : ℂ) * Nexp s e r = ∫ z, (f z - g z) := by
    rw [integral_sub hf hg, ← integral_main s e r]; rfl
  rw [hmain]
  set c1 : ℝ := e ^ 5 * Cin σ
  set c2 : ℝ := ρ ^ (M - 4) * M * (32 * K ^ 4)
  set c3 : ℝ := Real.exp (-(c0 * δ ^ 2 / 4) * M) * (10 * (1 + Kp σ) ^ 4)
  have hc1 : 0 ≤ c1 := by
    have : 0 ≤ Cin σ := by
      unfold Cin; have := Bσ_pos hσ; have := Rσ_pos σ; have := Kp_nonneg hσ; positivity
    positivity
  have hc2 : 0 ≤ c2 := by positivity
  have hc3 : 0 ≤ c3 := by have := Kp_nonneg hσ; positivity
  set b : ℝ → ℝ := fun z => c1 * Ew (c0 / 4) z + c2 * (1 + (e * z) ^ 2)⁻¹ + c3 * Ew (c0 / 4) z
  have hI1 := hΓint.const_mul c1
  have hI2 := (integrable_inv_scaled he0.ne').const_mul c2
  have hI3 := hΓint.const_mul c3
  have hbint : Integrable b := (hI1.add hI2).add hI3
  have hpt : ∀ z, ‖f z - g z‖ ≤ b z := by
    intro z
    have hE := Ew_nonneg (c0 / 4) z
    have hi : 0 ≤ (1 + (e * z) ^ 2)⁻¹ := by positivity
    have t1 : 0 ≤ c1 * Ew (c0 / 4) z := mul_nonneg hc1 hE
    have t2 : 0 ≤ c2 * (1 + (e * z) ^ 2)⁻¹ := mul_nonneg hc2 hi
    have t3 : 0 ≤ c3 * Ew (c0 / 4) z := mul_nonneg hc3 hE
    by_cases hz : e * |z| ≤ δ
    · have := pt_inner hσ hc0 hκ hδ0 hδR hδ1 hδK hs he0 he1 hMe hr hz
      simp only [f, g, b]; linarith
    · push_neg at hz
      have hu : δ ≤ |e * z| := by rw [abs_mul, abs_of_pos he0]; exact hz.le
      have h1 := pt_outer_f hρ hρ0.le hs hM he0 he1 hMe hr hu
      have h2 := pt_outer_g hσ hc0 hs (hκ s hs) hδ0 he0 he1 hMe hr hz
      have h3 := norm_sub_le (f z) (g z)
      simp only [f, g, b] at h3 ⊢
      linarith
  refine (norm_integral_le_of_norm_le hbint (Eventually.of_forall hpt)).trans ?_
  have hIb : ∫ z, b z = c1 * Γ + c2 * (Real.pi * e⁻¹) + c3 * Γ := by
    simp only [b]
    rw [integral_add (f := fun z => c1 * Ew (c0 / 4) z + c2 * (1 + (e * z) ^ 2)⁻¹)
      (g := fun z => c3 * Ew (c0 / 4) z) (hI1.add hI2) hI3,
      integral_add (f := fun z => c1 * Ew (c0 / 4) z) (g := fun z => c2 * (1 + (e * z) ^ 2)⁻¹) hI1 hI2,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, integral_inv_scaled he0]
  rw [hIb]
  have hΓ0 : 0 ≤ Γ := integral_nonneg (fun z => Ew_nonneg _ z)
  have g2 := geom_term hρ0 hCg1 hM he0 he1 hMe
  have g3 := exp_term (a := c0 * δ ^ 2 / 4) hCg2 he0 he1 hMe
  have e2 : c2 * (Real.pi * e⁻¹) ≤ 32 * K ^ 4 * Real.pi * (Cg1 / ρ ^ 4) * e ^ 5 := by
    have : c2 * (Real.pi * e⁻¹) = 32 * K ^ 4 * Real.pi * (ρ ^ (M - 4) * M * e⁻¹) := by
      simp only [c2]; ring
    rw [this]
    have hK : 0 ≤ 32 * K ^ 4 * Real.pi := by positivity
    calc 32 * K ^ 4 * Real.pi * (ρ ^ (M - 4) * M * e⁻¹) ≤ 32 * K ^ 4 * Real.pi * (Cg1 / ρ ^ 4 * e ^ 5) :=
          mul_le_mul_of_nonneg_left g2 hK
      _ = _ := by ring
  have e3 : c3 * Γ ≤ 10 * (1 + Kp σ) ^ 4 * Γ * Cg2 * e ^ 5 := by
    have hK : 0 ≤ 10 * (1 + Kp σ) ^ 4 * Γ := by have := Kp_nonneg hσ; positivity
    calc c3 * Γ = Real.exp (-(c0 * δ ^ 2 / 4) * M) * (10 * (1 + Kp σ) ^ 4 * Γ) := by
          simp only [c3]; ring
      _ ≤ Cg2 * e ^ 5 * (10 * (1 + Kp σ) ^ 4 * Γ) := mul_le_mul_of_nonneg_right g3 hK
      _ = _ := by ring
  have e1 : c1 * Γ = Cin σ * Γ * e ^ 5 := by simp only [c1]; ring
  calc c1 * Γ + c2 * (Real.pi * e⁻¹) + c3 * Γ
      ≤ Cin σ * Γ * e ^ 5 + 32 * K ^ 4 * Real.pi * (Cg1 / ρ ^ 4) * e ^ 5 +
        10 * (1 + Kp σ) ^ 4 * Γ * Cg2 * e ^ 5 := by linarith
    _ = _ := by ring

end EulerianBridge.Saddle
