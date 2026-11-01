import Bridge.Saddle.Expansion

/-!
# Lemma 5.5, part 9: the inner-region estimate for `χ(s, εz)^M`

`χ(s,u) = A(s+iu)/A(s) · e^{-iuκ₁(s)}` (eq. (119)), `Ψ = log χ` (eq. (122)), `a_n = κ_n/n!`.
For `|s| ≤ σ`, `M ε² = 1` and `ε|z| ≤ δ` (with `δ` small in terms of `σ` only):
`|χ(s,εz)^M - e^{-κ₂z²/2} T(z)| ≤ ε⁵ C_in (1+z²)^{24} e^{-c₀z²/4}` (`inner_pointwise`).
-/

open MeasureTheory Set Complex Filter Topology Metric
open scoped Nat

namespace EulerianBridge.Saddle

/-- Taylor coefficients `a_n(s) = κ_n(s)/n!`. -/
noncomputable def ac (n : ℕ) (s : ℝ) : ℂ := ((n ! : ℂ))⁻¹ * κc n s

/-- `χ(s,u) = A(s+iu)/A(s) · e^{-iuκ₁(s)}`. -/
noncomputable def χ (s u : ℝ) : ℂ := A ((s:ℂ) + u * I) / A s * cexp (-((u:ℂ) * I) * κc 1 s)

/-- `Ψ(s,u) = Λ(s+iu) - Λ(s) - iuΛ'(s)`. -/
noncomputable def Ψ (s u : ℝ) : ℂ := Lc ((s:ℂ) + u * I) - Lc s - (u:ℂ) * I * κc 1 s

theorem norm_uI (u : ℝ) : ‖(u:ℂ) * I‖ = |u| := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem χ_eq_exp {σ s u : ℝ} (hσ : 0 ≤ σ) (hs : |s| ≤ σ) (hu : |u| ≤ Rσ σ) :
    χ s u = cexp (Ψ s u) := by
  have h1 : (s:ℂ) + u * I ∈ Udom := by
    apply mem_Udom_of hσ hs
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_uI]; exact hu
  have h0 : (s:ℂ) ∈ Udom := ofReal_mem_Udom s
  rw [show Ψ s u = Lc ((s:ℂ) + u * I) + (-Lc s) + (-((u:ℂ) * I) * κc 1 s) by unfold Ψ; ring]
  rw [Complex.exp_add, Complex.exp_add, exp_Lc h1, Complex.exp_neg, exp_Lc h0]
  unfold χ; ring

theorem κc_zero_eq (s : ℝ) : κc 0 s = Lc s := by rw [κc_zero]

theorem Ψ_taylor {σ s u : ℝ} (hσ : 0 ≤ σ) (hs : |s| ≤ σ) (hu : |u| ≤ Rσ σ / 2) :
    ‖Ψ s u - (ac 2 s * ((u:ℂ) * I) ^ 2 + ac 3 s * ((u:ℂ) * I) ^ 3 + ac 4 s * ((u:ℂ) * I) ^ 4 +
      ac 5 s * ((u:ℂ) * I) ^ 5 + ac 6 s * ((u:ℂ) * I) ^ 6)‖ ≤ 2 * Bσ σ * (|u| / Rσ σ) ^ 7 := by
  have h := taylor_Lc hσ hs 7 (w := (u:ℂ) * I) (by rw [norm_uI]; exact hu)
  rw [norm_uI] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Ψ, ac, κc_zero_eq]
  simp only [Nat.factorial]; push_cast; ring

theorem norm_ac_le {σ s : ℝ} (hσ : 0 ≤ σ) (hs : |s| ≤ σ) (n : ℕ) : ‖ac n s‖ ≤ Bσ σ / Rσ σ ^ n :=
  coeff_bound hσ hs n

theorem ac_two (s : ℝ) : ac 2 s = ((κ 2 s / 2 : ℝ) : ℂ) := by
  rw [ac, κc_ofReal]; simp [Nat.factorial]; ring

/-! ## Constants -/

/-- `K_P = Σ_{n=3}^{6} B/R^n`. -/
noncomputable def Kp (σ : ℝ) : ℝ :=
  Bσ σ / Rσ σ ^ 3 + Bσ σ / Rσ σ ^ 4 + Bσ σ / Rσ σ ^ 5 + Bσ σ / Rσ σ ^ 6

/-- `K_W = K_P + 2B/R⁷`. -/
noncomputable def Kw (σ : ℝ) : ℝ := Kp σ + 2 * Bσ σ / Rσ σ ^ 7

/-- The constant of the inner estimate. -/
noncomputable def Cin (σ : ℝ) : ℝ :=
  Kw σ ^ 5 + 8 * Bσ σ / Rσ σ ^ 7 * (1 + Kw σ) ^ 3 + 55 * (1 + Kp σ) ^ 4

theorem Bσ_pos {σ : ℝ} (hσ : 0 ≤ σ) : 0 < Bσ σ := by
  unfold Bσ; have := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num); positivity

theorem Kp_nonneg {σ : ℝ} (hσ : 0 ≤ σ) : 0 ≤ Kp σ := by
  unfold Kp; have := Bσ_pos hσ; have := Rσ_pos σ; positivity

theorem Kw_nonneg {σ : ℝ} (hσ : 0 ≤ σ) : 0 ≤ Kw σ := by
  unfold Kw; have := Kp_nonneg hσ; have := Bσ_pos hσ; have := Rσ_pos σ; positivity

/-! ## The inner estimate -/

/-- The cubic and higher coefficients `b_n = a_n (iz)^n`. -/
noncomputable def bz (n : ℕ) (s z : ℝ) : ℂ := ac n s * ((z:ℂ) * I) ^ n

/-- `T(s, ε, z)` of (129). -/
noncomputable def Tz (s e z : ℝ) : ℂ := Tpoly e (bz 3 s z) (bz 4 s z) (bz 5 s z) (bz 6 s z)

theorem norm_bz_le {σ s : ℝ} (hσ : 0 ≤ σ) (hs : |s| ≤ σ) {n : ℕ} (hn : n ≤ 6) (z : ℝ) :
    ‖bz n s z‖ ≤ Bσ σ / Rσ σ ^ n * (1 + z ^ 2) ^ 6 := by
  unfold bz
  rw [norm_mul, norm_pow, norm_uI]
  have hω : |z| ≤ 1 + z ^ 2 := abs_le_one_add_sq z
  have h1 : (1:ℝ) ≤ 1 + z ^ 2 := by nlinarith [sq_nonneg z]
  have : |z| ^ n ≤ (1 + z ^ 2) ^ 6 :=
    (pow_le_pow_left₀ (abs_nonneg z) hω n).trans (pow_le_pow_right₀ h1 hn)
  exact mul_le_mul (norm_ac_le hσ hs n) this (by positivity)
    (div_nonneg (Bσ_pos hσ).le (pow_nonneg (Rσ_pos σ).le _))

/-- `MΨ(s, εz) = -κ₂z²/2 + P + Q`, with `Q = M · (Taylor remainder)`. -/
theorem MΨ_decomp {M : ℕ} {e : ℝ} (hMe : (M:ℝ) * e ^ 2 = 1) (s z : ℝ) :
    (M:ℂ) * Ψ s (e * z) = -((κ 2 s * z ^ 2 / 2 : ℝ) : ℂ) +
      Ppoly e (bz 3 s z) (bz 4 s z) (bz 5 s z) (bz 6 s z) +
      (M:ℂ) * (Ψ s (e * z) - (ac 2 s * (((e * z : ℝ):ℂ) * I) ^ 2 + ac 3 s * (((e * z : ℝ):ℂ) * I) ^ 3 +
        ac 4 s * (((e * z : ℝ):ℂ) * I) ^ 4 + ac 5 s * (((e * z : ℝ):ℂ) * I) ^ 5 +
        ac 6 s * (((e * z : ℝ):ℂ) * I) ^ 6)) := by
  have hMe' : (M:ℂ) * (e:ℂ) ^ 2 = 1 := by exact_mod_cast hMe
  have h2 := ac_two s
  unfold Ppoly bz
  rw [h2]
  push_cast
  have hI : I ^ 2 = -1 := Complex.I_sq
  linear_combination ((((κ 2 s:ℂ) / 2) * (z:ℂ) ^ 2 * I ^ 2) + ac 3 s * (e:ℂ) * (z:ℂ) ^ 3 * I ^ 3 +
    ac 4 s * (e:ℂ) ^ 2 * (z:ℂ) ^ 4 * I ^ 4 + ac 5 s * (e:ℂ) ^ 3 * (z:ℂ) ^ 5 * I ^ 5 +
    ac 6 s * (e:ℂ) ^ 4 * (z:ℂ) ^ 6 * I ^ 6) * hMe' + ((κ 2 s:ℂ) / 2 * (z:ℂ) ^ 2) * hI

set_option maxHeartbeats 1000000 in
theorem inner_pointwise {σ c0 δ : ℝ} (hσ : 0 ≤ σ) (hc0 : 0 < c0)
    (hκ : ∀ s, |s| ≤ σ → c0 ≤ κ 2 s) (hδ0 : 0 < δ) (hδR : δ ≤ Rσ σ / 2) (hδ1 : δ ≤ 1)
    (hδK : Kw σ * δ ≤ c0 / 4) {s : ℝ} (hs : |s| ≤ σ) {M : ℕ} {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1)
    (hMe : (M:ℝ) * e ^ 2 = 1) {z : ℝ} (hz : e * |z| ≤ δ) :
    ‖χ s (e * z) ^ M - (Real.exp (-(κ 2 s * z ^ 2) / 2) : ℂ) * Tz s e z‖ ≤
      e ^ 5 * Cin σ * (1 + z ^ 2) ^ 24 * Real.exp (-(c0 / 4) * z ^ 2) := by
  set B := Bσ σ
  set R := Rσ σ
  have hB : 0 < B := Bσ_pos hσ
  have hR : 0 < R := Rσ_pos σ
  have hez : |e * z| = e * |z| := by rw [abs_mul, abs_of_pos he0]
  have hu2 : |e * z| ≤ R / 2 := by rw [hez]; linarith
  have hu : |e * z| ≤ R := by linarith [hR]
  have hez1 : e * |z| ≤ 1 := hz.trans hδ1
  set ω : ℝ := 1 + z ^ 2
  have hω1 : 1 ≤ ω := by simp only [ω]; nlinarith [sq_nonneg z]
  have hzω : |z| ≤ ω := abs_le_one_add_sq z
  have hκ2 := hκ s hs
  -- the decomposition
  set P := Ppoly e (bz 3 s z) (bz 4 s z) (bz 5 s z) (bz 6 s z)
  set Q : ℂ := (M:ℂ) * (Ψ s (e * z) - (ac 2 s * (((e * z : ℝ):ℂ) * I) ^ 2 +
    ac 3 s * (((e * z : ℝ):ℂ) * I) ^ 3 + ac 4 s * (((e * z : ℝ):ℂ) * I) ^ 4 +
    ac 5 s * (((e * z : ℝ):ℂ) * I) ^ 5 + ac 6 s * (((e * z : ℝ):ℂ) * I) ^ 6))
  have hdec := MΨ_decomp hMe s z
  have hchi : χ s (e * z) ^ M = (Real.exp (-(κ 2 s * z ^ 2) / 2) : ℂ) * cexp (P + Q) := by
    rw [χ_eq_exp hσ hs hu, ← Complex.exp_nat_mul, hdec, add_assoc, Complex.exp_add]
    congr 1
    push_cast; ring_nf
  -- bounds on Q, P, P + Q
  have hMe5 : (M:ℝ) * e ^ 7 = e ^ 5 := by
    calc (M:ℝ) * e ^ 7 = ((M:ℝ) * e ^ 2) * e ^ 5 := by ring
      _ = e ^ 5 := by rw [hMe, one_mul]
  set q : ℝ := 2 * B * e ^ 5 * |z| ^ 7 / R ^ 7
  have hQ : ‖Q‖ ≤ q := by
    have ht := Ψ_taylor hσ hs hu2
    simp only [Q]
    rw [norm_mul, Complex.norm_natCast]
    calc (M:ℝ) * ‖_‖ ≤ (M:ℝ) * (2 * B * (|e * z| / R) ^ 7) :=
          mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
      _ = 2 * B * ((M:ℝ) * e ^ 7) * |z| ^ 7 / R ^ 7 := by rw [hez]; field_simp
      _ = q := by rw [hMe5]
  set X : ℝ := Kw σ * e * |z| ^ 3
  have hX0 : 0 ≤ X := by have := Kw_nonneg hσ; positivity
  have hb : ∀ n : ℕ, ‖bz n s z‖ ≤ B / R ^ n * |z| ^ n := by
    intro n
    unfold bz
    rw [norm_mul, norm_pow, norm_uI]
    exact mul_le_mul_of_nonneg_right (norm_ac_le hσ hs n) (pow_nonneg (abs_nonneg _) _)
  have hE : ‖(e:ℂ)‖ = e := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos he0]
  have hpow : ∀ k : ℕ, (e * |z|) ^ k ≤ 1 := fun k => pow_le_one₀ (by positivity) hez1
  have hP : ‖P‖ ≤ Kp σ * e * |z| ^ 3 := by
    simp only [P, Ppoly]
    have t3 : ‖(e:ℂ) * bz 3 s z‖ ≤ B / R ^ 3 * (e * |z| ^ 3) := by
      rw [norm_mul, hE]
      calc e * ‖bz 3 s z‖ ≤ e * (B / R ^ 3 * |z| ^ 3) := mul_le_mul_of_nonneg_left (hb 3) he0.le
        _ = B / R ^ 3 * (e * |z| ^ 3) := by ring
    have t4 : ‖(e:ℂ) ^ 2 * bz 4 s z‖ ≤ B / R ^ 4 * (e * |z| ^ 3) := by
      rw [norm_mul, norm_pow, hE]
      calc e ^ 2 * ‖bz 4 s z‖ ≤ e ^ 2 * (B / R ^ 4 * |z| ^ 4) :=
            mul_le_mul_of_nonneg_left (hb 4) (by positivity)
        _ = B / R ^ 4 * (e * |z| ^ 3) * (e * |z|) := by ring
        _ ≤ B / R ^ 4 * (e * |z| ^ 3) * 1 := by gcongr
        _ = B / R ^ 4 * (e * |z| ^ 3) := mul_one _
    have t5 : ‖(e:ℂ) ^ 3 * bz 5 s z‖ ≤ B / R ^ 5 * (e * |z| ^ 3) := by
      rw [norm_mul, norm_pow, hE]
      calc e ^ 3 * ‖bz 5 s z‖ ≤ e ^ 3 * (B / R ^ 5 * |z| ^ 5) :=
            mul_le_mul_of_nonneg_left (hb 5) (by positivity)
        _ = B / R ^ 5 * (e * |z| ^ 3) * (e * |z|) ^ 2 := by ring
        _ ≤ B / R ^ 5 * (e * |z| ^ 3) * 1 := by gcongr; try exact hpow 2
        _ = B / R ^ 5 * (e * |z| ^ 3) := mul_one _
    have t6 : ‖(e:ℂ) ^ 4 * bz 6 s z‖ ≤ B / R ^ 6 * (e * |z| ^ 3) := by
      rw [norm_mul, norm_pow, hE]
      calc e ^ 4 * ‖bz 6 s z‖ ≤ e ^ 4 * (B / R ^ 6 * |z| ^ 6) :=
            mul_le_mul_of_nonneg_left (hb 6) (by positivity)
        _ = B / R ^ 6 * (e * |z| ^ 3) * (e * |z|) ^ 3 := by ring
        _ ≤ B / R ^ 6 * (e * |z| ^ 3) * 1 := by gcongr; try exact hpow 3
        _ = B / R ^ 6 * (e * |z| ^ 3) := mul_one _
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (‖(e:ℂ) * bz 3 s z + (e:ℂ) ^ 2 * bz 4 s z‖ + ‖(e:ℂ) ^ 3 * bz 5 s z‖) +
            ‖(e:ℂ) ^ 4 * bz 6 s z‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖(e:ℂ) * bz 3 s z‖ + ‖(e:ℂ) ^ 2 * bz 4 s z‖) + ‖(e:ℂ) ^ 3 * bz 5 s z‖) +
            ‖(e:ℂ) ^ 4 * bz 6 s z‖ := by gcongr; exact norm_add_le _ _
      _ ≤ B / R ^ 3 * (e * |z| ^ 3) + B / R ^ 4 * (e * |z| ^ 3) + B / R ^ 5 * (e * |z| ^ 3) +
            B / R ^ 6 * (e * |z| ^ 3) := by gcongr
      _ = Kp σ * e * |z| ^ 3 := by simp only [Kp, B, R]; ring
  have hq' : q ≤ 2 * B / R ^ 7 * (e * |z| ^ 3) := by
    simp only [q]
    have : 2 * B * e ^ 5 * |z| ^ 7 / R ^ 7 = 2 * B / R ^ 7 * (e * |z| ^ 3) * (e * |z|) ^ 4 := by
      field_simp
    rw [this]
    have : 0 ≤ 2 * B / R ^ 7 * (e * |z| ^ 3) := by positivity
    calc 2 * B / R ^ 7 * (e * |z| ^ 3) * (e * |z|) ^ 4 ≤ 2 * B / R ^ 7 * (e * |z| ^ 3) * 1 :=
          mul_le_mul_of_nonneg_left (hpow 4) this
      _ = _ := mul_one _
  have hPX : ‖P‖ ≤ X := by
    have : Kp σ * e * |z| ^ 3 ≤ X := by
      simp only [X, Kw]
      have : 0 ≤ 2 * B / R ^ 7 * (e * |z| ^ 3) := by positivity
      nlinarith
    linarith
  have hWX : ‖P + Q‖ ≤ X := by
    calc ‖P + Q‖ ≤ ‖P‖ + ‖Q‖ := norm_add_le _ _
      _ ≤ Kp σ * e * |z| ^ 3 + 2 * B / R ^ 7 * (e * |z| ^ 3) := add_le_add hP (hQ.trans hq')
      _ = X := by simp only [X, Kw, B, R]; ring
  -- β-bounds
  set β : ℝ := Kp σ * ω ^ 6
  have hbβ : ∀ n : ℕ, 3 ≤ n → n ≤ 6 → ‖bz n s z‖ ≤ β := by
    intro n h3 h6
    have h := norm_bz_le hσ hs h6 z
    have hKn : B / R ^ n ≤ Kp σ := by
      have t3 := div_nonneg hB.le (pow_nonneg hR.le 3)
      have t4 := div_nonneg hB.le (pow_nonneg hR.le 4)
      have t5 := div_nonneg hB.le (pow_nonneg hR.le 5)
      have t6 := div_nonneg hB.le (pow_nonneg hR.le 6)
      interval_cases n <;> simp only [Kp] <;> linarith
    exact h.trans (mul_le_mul_of_nonneg_right hKn (by positivity))
  have hcore := exp_sub_T_bound he0.le he1 (hbβ 3 le_rfl (by norm_num)) (hbβ 4 (by norm_num) (by norm_num))
    (hbβ 5 (by norm_num) (by norm_num)) (hbβ 6 (by norm_num) le_rfl) hQ hWX hPX
  -- Gaussian factor
  have hXz : X ≤ κ 2 s / 4 * z ^ 2 := by
    have h1 : X = Kw σ * (e * |z|) * z ^ 2 := by
      simp only [X]; rw [show |z| ^ 3 = |z| * z ^ 2 by rw [pow_succ', sq_abs]]; ring
    rw [h1]
    have hK := Kw_nonneg hσ
    calc Kw σ * (e * |z|) * z ^ 2 ≤ Kw σ * δ * z ^ 2 := by gcongr
      _ ≤ c0 / 4 * z ^ 2 := by gcongr
      _ ≤ κ 2 s / 4 * z ^ 2 := by gcongr
  have hg1 : Real.exp (-(κ 2 s * z ^ 2) / 2) * Real.exp X ≤ Real.exp (-(c0 / 4) * z ^ 2) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg z]
  have hg2 : Real.exp (-(κ 2 s * z ^ 2) / 2) ≤ Real.exp (-(c0 / 4) * z ^ 2) := by
    apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg z]
  rw [hchi, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hTz : Tz s e z = Tpoly e (bz 3 s z) (bz 4 s z) (bz 5 s z) (bz 6 s z) := rfl
  rw [hTz]
  set G := Real.exp (-(κ 2 s * z ^ 2) / 2)
  have hG0 : 0 ≤ G := (Real.exp_pos _).le
  have hc4 : 0 ≤ Real.exp (-(c0 / 4) * z ^ 2) := (Real.exp_pos _).le
  -- the three terms
  have hz15 : |z| ^ 15 ≤ ω ^ 24 :=
    (pow_le_pow_left₀ (abs_nonneg z) hzω 15).trans (pow_le_pow_right₀ hω1 (by norm_num))
  have term1 : G * (X ^ 5 * Real.exp X) ≤ e ^ 5 * Kw σ ^ 5 * ω ^ 24 * Real.exp (-(c0 / 4) * z ^ 2) := by
    have hX5 : X ^ 5 = Kw σ ^ 5 * e ^ 5 * |z| ^ 15 := by simp only [X]; ring
    calc G * (X ^ 5 * Real.exp X) = X ^ 5 * (G * Real.exp X) := by ring
      _ ≤ X ^ 5 * Real.exp (-(c0 / 4) * z ^ 2) := mul_le_mul_of_nonneg_left hg1 (by positivity)
      _ = Kw σ ^ 5 * e ^ 5 * |z| ^ 15 * Real.exp (-(c0 / 4) * z ^ 2) := by rw [hX5]
      _ ≤ Kw σ ^ 5 * e ^ 5 * ω ^ 24 * Real.exp (-(c0 / 4) * z ^ 2) := by
          have := Kw_nonneg hσ; gcongr
      _ = _ := by ring
  have term2 : G * (4 * q * (1 + X) ^ 3) ≤
      e ^ 5 * (8 * B / R ^ 7 * (1 + Kw σ) ^ 3) * ω ^ 24 * Real.exp (-(c0 / 4) * z ^ 2) := by
    have hX' : 1 + X ≤ (1 + Kw σ) * ω ^ 3 := by
      have hK := Kw_nonneg hσ
      have h1 : X ≤ Kw σ * ω ^ 3 := by
        simp only [X]
        have : e * |z| ^ 3 ≤ ω ^ 3 := by
          calc e * |z| ^ 3 ≤ 1 * |z| ^ 3 := by gcongr
            _ ≤ ω ^ 3 := by rw [one_mul]; exact pow_le_pow_left₀ (abs_nonneg z) hzω 3
        calc Kw σ * e * |z| ^ 3 = Kw σ * (e * |z| ^ 3) := by ring
          _ ≤ Kw σ * ω ^ 3 := by gcongr
      have h2 : (1:ℝ) ≤ ω ^ 3 := one_le_pow₀ hω1
      nlinarith
    have hz7 : |z| ^ 7 ≤ ω ^ 7 := pow_le_pow_left₀ (abs_nonneg z) hzω 7
    have hq4 : 4 * q = e ^ 5 * (8 * B / R ^ 7) * |z| ^ 7 := by simp only [q]; field_simp; ring
    calc G * (4 * q * (1 + X) ^ 3) ≤ Real.exp (-(c0 / 4) * z ^ 2) * (4 * q * (1 + X) ^ 3) :=
          mul_le_mul_of_nonneg_right hg2 (by positivity)
      _ = e ^ 5 * (8 * B / R ^ 7) * |z| ^ 7 * (1 + X) ^ 3 * Real.exp (-(c0 / 4) * z ^ 2) := by
          rw [hq4]; ring
      _ ≤ e ^ 5 * (8 * B / R ^ 7) * ω ^ 7 * ((1 + Kw σ) * ω ^ 3) ^ 3 * Real.exp (-(c0 / 4) * z ^ 2) := by
          gcongr
      _ = e ^ 5 * (8 * B / R ^ 7 * (1 + Kw σ) ^ 3) * ω ^ 16 * Real.exp (-(c0 / 4) * z ^ 2) := by ring
      _ ≤ e ^ 5 * (8 * B / R ^ 7 * (1 + Kw σ) ^ 3) * ω ^ 24 * Real.exp (-(c0 / 4) * z ^ 2) := by
          have := Kw_nonneg hσ
          have hω24 : ω ^ 16 ≤ ω ^ 24 := pow_le_pow_right₀ hω1 (by norm_num)
          gcongr
  have term3 : G * (55 * e ^ 5 * (1 + β) ^ 4) ≤
      e ^ 5 * (55 * (1 + Kp σ) ^ 4) * ω ^ 24 * Real.exp (-(c0 / 4) * z ^ 2) := by
    have hβ' : 1 + β ≤ (1 + Kp σ) * ω ^ 6 := by
      have hK := Kp_nonneg hσ
      have h2 : (1:ℝ) ≤ ω ^ 6 := one_le_pow₀ hω1
      simp only [β]; nlinarith
    have hK := Kp_nonneg hσ
    have hβ0 : 0 ≤ 1 + β := by simp only [β]; positivity
    calc G * (55 * e ^ 5 * (1 + β) ^ 4) ≤ Real.exp (-(c0 / 4) * z ^ 2) * (55 * e ^ 5 * (1 + β) ^ 4) :=
          mul_le_mul_of_nonneg_right hg2 (by positivity)
      _ ≤ Real.exp (-(c0 / 4) * z ^ 2) * (55 * e ^ 5 * ((1 + Kp σ) * ω ^ 6) ^ 4) := by gcongr
      _ = _ := by ring
  calc G * ‖cexp (P + Q) - Tpoly e (bz 3 s z) (bz 4 s z) (bz 5 s z) (bz 6 s z)‖
      ≤ G * (X ^ 5 * Real.exp X + 4 * q * (1 + X) ^ 3 + 55 * e ^ 5 * (1 + β) ^ 4) :=
        mul_le_mul_of_nonneg_left hcore hG0
    _ = G * (X ^ 5 * Real.exp X) + G * (4 * q * (1 + X) ^ 3) + G * (55 * e ^ 5 * (1 + β) ^ 4) := by ring
    _ ≤ e ^ 5 * Kw σ ^ 5 * ω ^ 24 * Real.exp (-(c0 / 4) * z ^ 2) +
        e ^ 5 * (8 * B / R ^ 7 * (1 + Kw σ) ^ 3) * ω ^ 24 * Real.exp (-(c0 / 4) * z ^ 2) +
        e ^ 5 * (55 * (1 + Kp σ) ^ 4) * ω ^ 24 * Real.exp (-(c0 / 4) * z ^ 2) :=
        add_le_add (add_le_add term1 term2) term3
    _ = e ^ 5 * Cin σ * ω ^ 24 * Real.exp (-(c0 / 4) * z ^ 2) := by
        simp only [Cin, B, R]; ring

end EulerianBridge.Saddle
