import UniformLanczos.Rate514Monotone
import UniformLanczos.Theorem514

/-! # Manuscript 12, Theorem 5.14: hybrid bound, residual identity and assembly

* `hybrid_tail`: the change of residual from `b` to `b̃` (bonds differing only off the
  window `W = [j-L, j+L]`, by at most one) is at most `C_f Z₂ (1+D_k)^{-3}`; this is
  (164), with the exponent `3` that the kernel decay `(1+|k-m|)^{-5}` gives with integer
  powers, which suffices for (166).
* `residual_difference`, `mu_lower`: `h_k = Σ_m B̄_{km} d_m + μ_k d_k` with
  `μ_k = k/(M a_k b_k) ≥ 4 t` when `k/M ≥ t`.
* `rate_assembly`: weighted strong monotonicity on `W` gives `|d_j| ≤ K/M`.
* `theorem_5_14_conclusion`: with `a_j = √β_j^{[M]}/M`, `b_j = ξ_{j/M}/2`, the two bounds
  (160) of Theorem 5.14. -/

namespace UniformLanczos.Rate514Assembly

open Finset UniformLanczos.Rate514

/-! ## The hybrid bound (164) -/

theorem dist_le_of_not_mem (j : ℤ) (L : ℕ) {k m : ℤ} (hk : k ∈ Finset.Icc (j - L) (j + L))
    (hm : m ∉ Finset.Icc (j - L) (j + L)) : Rate514.Dist L j k ≤ |(k:ℝ) - m| := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hk hm
  unfold Rate514.Dist
  have hkj : |(k:ℝ) - j| ≤ L := by
    rw [abs_le]; constructor
    · have : ((j - L : ℤ):ℝ) ≤ k := by exact_mod_cast hk.1
      push_cast at this; linarith
    · have : (k:ℝ) ≤ ((j + L : ℤ):ℝ) := by exact_mod_cast hk.2
      push_cast at this; linarith
  have hmj : (L:ℝ) + 1 ≤ |(m:ℝ) - j| := by
    rcases hm with h | h
    · have : m + 1 ≤ j - L := by omega
      have : ((m + 1 : ℤ):ℝ) ≤ ((j - L : ℤ):ℝ) := by exact_mod_cast this
      push_cast at this; rw [abs_of_neg (by linarith)]; linarith
    · have : j + L + 1 ≤ m := by omega
      have : ((j + L + 1 : ℤ):ℝ) ≤ (m:ℝ) := by exact_mod_cast this
      push_cast at this; rw [abs_of_pos (by linarith)]; linarith
  have htri : |(m:ℝ) - j| ≤ |(k:ℝ) - m| + |(k:ℝ) - j| := by
    have := abs_sub_le (m:ℝ) k j
    rw [abs_sub_comm (m:ℝ) k] at this; linarith
  linarith

theorem dist_ge_one (j : ℤ) (L : ℕ) {k : ℤ} (hk : k ∈ Finset.Icc (j - L) (j + L)) :
    1 ≤ Rate514.Dist L j k := by
  simp only [Finset.mem_Icc] at hk
  unfold Rate514.Dist
  have : |(k:ℝ) - j| ≤ L := by
    rw [abs_le]; constructor
    · have : ((j - L : ℤ):ℝ) ≤ k := by exact_mod_cast hk.1
      push_cast at this; linarith
    · have : (k:ℝ) ≤ ((j + L : ℤ):ℝ) := by exact_mod_cast hk.2
      push_cast at this; linarith
  linarith

/-- **(164).** If `c_m = 0` on `W` and `|c_m| ≤ 1`, then
`Σ_m |c_m| C_f (1+|k-m|)^{-5} ≤ C_f Z₂ (1+D_k)^{-3}` for `k ∈ W`. -/
theorem hybrid_tail (j : ℤ) (L : ℕ) {k : ℤ} (hk : k ∈ Finset.Icc (j - L) (j + L))
    (c : ℤ → ℝ) {Cf : ℝ} (hCf : 0 ≤ Cf) (hc0 : ∀ m ∈ Finset.Icc (j - L) (j + L), c m = 0)
    (hc : ∀ m, |c m| ≤ 1)
    (hsum : Summable fun m : ℤ => |c m| * (Cf * ((1 + |(k:ℝ) - m|) ^ 5)⁻¹)) :
    ∑' m : ℤ, |c m| * (Cf * ((1 + |(k:ℝ) - m|) ^ 5)⁻¹) ≤
      Cf * Z2 * ((1 + Rate514.Dist L j k) ^ 3)⁻¹ := by
  set D := Rate514.Dist L j k
  have hD1 := dist_ge_one j L hk
  set g : ℤ → ℝ := fun n => ((1 + 1 * |(n:ℝ)|) ^ 2)⁻¹
  have hgs : Summable g := summable_profile one_pos le_rfl
  have hg' : Summable fun m : ℤ => Cf * ((1 + D) ^ 3)⁻¹ * g (m - k) :=
    ((Equiv.subRight k).summable_iff.mpr hgs).mul_left _
  have hpt : ∀ m : ℤ, |c m| * (Cf * ((1 + |(k:ℝ) - m|) ^ 5)⁻¹) ≤
      Cf * ((1 + D) ^ 3)⁻¹ * g (m - k) := by
    intro m
    have hgm : g (m - k) = ((1 + |(k:ℝ) - m|) ^ 2)⁻¹ := by
      simp only [g, one_mul]; push_cast; rw [abs_sub_comm]
    rw [hgm]
    by_cases hm : m ∈ Finset.Icc (j - L) (j + L)
    · rw [hc0 m hm, abs_zero, zero_mul]; positivity
    · have hdm := dist_le_of_not_mem j L hk hm
      set x := |(k:ℝ) - m|
      have hx : 1 + D ≤ 1 + x := by linarith
      have hpos : 0 < 1 + D := by linarith
      have h5 : ((1 + x) ^ 5)⁻¹ ≤ ((1 + D) ^ 3)⁻¹ * ((1 + x) ^ 2)⁻¹ := by
        rw [← mul_inv]
        apply inv_anti₀ (by positivity)
        rw [show (1 + x) ^ 5 = (1 + x) ^ 3 * (1 + x) ^ 2 by ring]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hpos.le hx 3) (by positivity)
      calc |c m| * (Cf * ((1 + x) ^ 5)⁻¹) ≤ 1 * (Cf * ((1 + x) ^ 5)⁻¹) :=
            mul_le_mul_of_nonneg_right (hc m) (by positivity)
        _ ≤ Cf * (((1 + D) ^ 3)⁻¹ * ((1 + x) ^ 2)⁻¹) := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_left h5 hCf
        _ = Cf * ((1 + D) ^ 3)⁻¹ * ((1 + x) ^ 2)⁻¹ := by ring
  calc ∑' m : ℤ, |c m| * (Cf * ((1 + |(k:ℝ) - m|) ^ 5)⁻¹)
      ≤ ∑' m : ℤ, Cf * ((1 + D) ^ 3)⁻¹ * g (m - k) := hsum.tsum_le_tsum hpt hg'
    _ = Cf * ((1 + D) ^ 3)⁻¹ * Z2 := by
        rw [tsum_mul_left]; congr 1; exact (Equiv.subRight k).tsum_eq g
    _ = Cf * Z2 * ((1 + D) ^ 3)⁻¹ := by ring

/-! ## The residual identity `h = B̄ d + μ d` -/

theorem residual_difference {Fa Fb ak bk k M S : ℝ} (hM : M ≠ 0) (ha : ak ≠ 0) (hb : bk ≠ 0)
    (hF : Fa - Fb = S) :
    (Fa - k / (M * ak)) - (Fb - k / (M * bk)) = S + k / (M * ak * bk) * (ak - bk) := by
  rw [← hF]; field_simp; ring

theorem mu_lower {ak bk k M t : ℝ} (hM : 0 < M) (ha : 0 < ak) (ha2 : ak ≤ 1 / 2)
    (hb : 0 < bk) (hb2 : bk ≤ 1 / 2) (ht : 0 ≤ t) (hkM : t ≤ k / M) :
    4 * t ≤ k / (M * ak * bk) := by
  have hab : ak * bk ≤ 1 / 4 := by nlinarith
  have habp : 0 < ak * bk := mul_pos ha hb
  rw [show k / (M * ak * bk) = (k / M) / (ak * bk) by field_simp, le_div_iff₀ habp]
  nlinarith

/-! ## The weighted residual sum with the exponent of (164) -/

theorem ω_dist_le3 (L : ℕ) (hL : 2 ≤ L) (j k : ℤ) (hk : k ∈ Finset.Icc (j - L) (j + L))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ω ε j k * ((1 + Rate514.Dist L j k) ^ 6)⁻¹ ≤
      4 / (ε ^ 2 * (L:ℝ) ^ 2) * ((1 + Rate514.Dist L j k) ^ 2)⁻¹ := by
  have h8 := ω_dist_le L hL j k hk hε hε1
  have hD1 : 1 ≤ 1 + Rate514.Dist L j k := by linarith [dist_ge_one j L hk]
  -- `(1+D)^{-6} = (1+D)^{-8} (1+D)^2` and the comparison of `ω_dist_le` with exponent 8
  have hkR := hk
  simp only [Finset.mem_Icc] at hkR
  set D := Rate514.Dist L j k
  set a := |(k:ℝ) - j|
  have ha : 0 ≤ a := abs_nonneg _
  have hD : D = (L:ℝ) + 1 - a := rfl
  have hLr : (2:ℝ) ≤ L := by exact_mod_cast hL
  have haL : a ≤ L := by linarith [dist_ge_one j L hk]
  have hω : ω ε j k = ((1 + ε * a) ^ 2)⁻¹ := by simp only [ω, sw, inv_pow]; rfl
  have hεL : 0 < ε ^ 2 * (L:ℝ) ^ 2 := by positivity
  have hp2 : 0 < (1 + D) ^ 2 := by positivity
  rw [hω, show (1 + D) ^ 6 = (1 + D) ^ 4 * (1 + D) ^ 2 by ring, mul_inv]
  by_cases hcase : a ≤ L / 2
  · have hbig : (L:ℝ) / 2 ≤ 1 + D := by rw [hD]; linarith
    have h4 : ε ^ 2 * (L:ℝ) ^ 2 ≤ 4 * (1 + D) ^ 4 := by
      have h1 : (L:ℝ) ^ 2 ≤ 4 * (1 + D) ^ 2 := by nlinarith
      have h2 : (1 + D) ^ 2 ≤ (1 + D) ^ 4 := pow_le_pow_right₀ hD1 (by norm_num)
      have h3 : ε ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (L:ℝ)]
    have hω1 : ((1 + ε * a) ^ 2)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀; nlinarith [mul_nonneg hε.le ha]
    calc ((1 + ε * a) ^ 2)⁻¹ * (((1 + D) ^ 4)⁻¹ * ((1 + D) ^ 2)⁻¹)
        ≤ 1 * (((1 + D) ^ 4)⁻¹ * ((1 + D) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_right hω1 (by positivity)
      _ ≤ 4 / (ε ^ 2 * (L:ℝ) ^ 2) * ((1 + D) ^ 2)⁻¹ := by
          rw [one_mul]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hεL]
          linarith
  · push_neg at hcase
    have hω2 : ((1 + ε * a) ^ 2)⁻¹ ≤ 4 / (ε ^ 2 * (L:ℝ) ^ 2) := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hεL]
      have : ε * (L / 2) ≤ 1 + ε * a := by nlinarith
      nlinarith [mul_pos hε (show (0:ℝ) < L / 2 by linarith)]
    have h4 : ((1 + D) ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hD1)
    calc ((1 + ε * a) ^ 2)⁻¹ * (((1 + D) ^ 4)⁻¹ * ((1 + D) ^ 2)⁻¹)
        ≤ 4 / (ε ^ 2 * (L:ℝ) ^ 2) * (1 * ((1 + D) ^ 2)⁻¹) := by
          apply mul_le_mul hω2 _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = 4 / (ε ^ 2 * (L:ℝ) ^ 2) * ((1 + D) ^ 2)⁻¹ := by rw [one_mul]

theorem residual_sum3 (j : ℤ) (L : ℕ) (hL : 2 ≤ L) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {M Ch c : ℝ} (hM : 0 < M) (hc : 0 < c) (hLM : c * M ≤ L) (h : ℤ → ℝ)
    (hh : ∀ k ∈ Finset.Icc (j - L) (j + L),
      |h k| ≤ Ch * (1 / M + ((1 + Rate514.Dist L j k) ^ 3)⁻¹)) :
    ∑ k ∈ Finset.Icc (j - L) (j + L), ω ε j k * h k ^ 2 ≤
      2 * Ch ^ 2 * (Ωε ε + 8 * Z2 / (ε ^ 2 * c ^ 2)) / M ^ 2 := by
  set W := Finset.Icc (j - L) (j + L)
  have hsq : ∀ k ∈ W, h k ^ 2 ≤ 2 * Ch ^ 2 * (1 / M ^ 2 + ((1 + Rate514.Dist L j k) ^ 6)⁻¹) := by
    intro k hk
    have hx : 0 ≤ ((1 + Rate514.Dist L j k) ^ 3)⁻¹ := by
      have := dist_ge_one j L hk; positivity
    have habs : h k ^ 2 ≤ (Ch * (1 / M + ((1 + Rate514.Dist L j k) ^ 3)⁻¹)) ^ 2 := by
      rw [← sq_abs (h k)]; exact pow_le_pow_left₀ (abs_nonneg _) (hh k hk) 2
    have h6 : (((1 + Rate514.Dist L j k) ^ 3)⁻¹) ^ 2 = ((1 + Rate514.Dist L j k) ^ 6)⁻¹ := by
      rw [inv_pow, ← pow_mul]
    have hM2 : (1 / M) ^ 2 = 1 / M ^ 2 := by rw [div_pow, one_pow]
    calc h k ^ 2 ≤ (Ch * (1 / M + ((1 + Rate514.Dist L j k) ^ 3)⁻¹)) ^ 2 := habs
      _ ≤ 2 * Ch ^ 2 * ((1 / M) ^ 2 + (((1 + Rate514.Dist L j k) ^ 3)⁻¹) ^ 2) := by
          nlinarith [sq_nonneg (1 / M - ((1 + Rate514.Dist L j k) ^ 3)⁻¹), sq_nonneg Ch]
      _ = 2 * Ch ^ 2 * (1 / M ^ 2 + ((1 + Rate514.Dist L j k) ^ 6)⁻¹) := by rw [h6, hM2]
  have hB : ∑ k ∈ W, ω ε j k * ((1 + Rate514.Dist L j k) ^ 6)⁻¹ ≤ 8 * Z2 / (ε ^ 2 * (L:ℝ) ^ 2) := by
    calc ∑ k ∈ W, ω ε j k * ((1 + Rate514.Dist L j k) ^ 6)⁻¹
        ≤ ∑ k ∈ W, 4 / (ε ^ 2 * (L:ℝ) ^ 2) * ((1 + Rate514.Dist L j k) ^ 2)⁻¹ :=
          Finset.sum_le_sum fun k hk => ω_dist_le3 L hL j k hk hε hε1
      _ = 4 / (ε ^ 2 * (L:ℝ) ^ 2) * ∑ k ∈ W, ((1 + Rate514.Dist L j k) ^ 2)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ 4 / (ε ^ 2 * (L:ℝ) ^ 2) * (2 * Z2) :=
          mul_le_mul_of_nonneg_left (sum_dist_le L j) (by positivity)
      _ = 8 * Z2 / (ε ^ 2 * (L:ℝ) ^ 2) := by ring
  have hA : 1 / M ^ 2 * ∑ k ∈ W, ω ε j k ≤ Ωε ε / M ^ 2 := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (sum_ω_le W hε j) (by positivity)
  have hZ : 0 ≤ Z2 := tsum_nonneg fun n => inv_nonneg.mpr (pow_nonneg (by positivity) _)
  have hcM : 0 < c * M := mul_pos hc hM
  have hL2 : (c * M) ^ 2 ≤ (L:ℝ) ^ 2 := pow_le_pow_left₀ hcM.le hLM 2
  have hfrac : 8 * Z2 / (ε ^ 2 * (L:ℝ) ^ 2) ≤ 8 * Z2 / (ε ^ 2 * c ^ 2) / M ^ 2 := by
    rw [div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [sq_nonneg ε, mul_le_mul_of_nonneg_left hL2 (sq_nonneg ε)]
  have h2C : 0 ≤ 2 * Ch ^ 2 := by positivity
  calc ∑ k ∈ W, ω ε j k * h k ^ 2
      ≤ ∑ k ∈ W, ω ε j k * (2 * Ch ^ 2 * (1 / M ^ 2 + ((1 + Rate514.Dist L j k) ^ 6)⁻¹)) :=
        Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hsq k hk) (ω_nonneg ε j k)
    _ = 2 * Ch ^ 2 * (1 / M ^ 2 * ∑ k ∈ W, ω ε j k +
          ∑ k ∈ W, ω ε j k * ((1 + Rate514.Dist L j k) ^ 6)⁻¹) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ ≤ 2 * Ch ^ 2 * (Ωε ε / M ^ 2 + 8 * Z2 / (ε ^ 2 * c ^ 2) / M ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA (hB.trans hfrac)) h2C
    _ = 2 * Ch ^ 2 * (Ωε ε + 8 * Z2 / (ε ^ 2 * c ^ 2)) / M ^ 2 := by ring

/-! ## Assembly -/

/-- **The pointwise rate.** On `W = [j-L, j+L]` with `L ≥ 2` and `L ≥ cM`: if
`h = B̄ d + μ d` with `B̄` symmetric, positive semidefinite, `|B̄_{km}| ≤ C_B (1+|k-m|)^{-5}`,
`μ ≥ μ₀ > 0`, `ε² C_B Z₃ ≤ μ₀`, and `|h_k| ≤ C_h (1/M + (1+D_k)^{-3})`, then
`d_j² ≤ (4/μ₀²) K/M²` with `K = 2 C_h² (Ω_ε + 8 Z₂/(ε² c²))`. -/
theorem rate_assembly (j : ℤ) (L : ℕ) (hL : 2 ≤ L) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {M Ch c μ₀ CB : ℝ} (hM : 0 < M) (hc : 0 < c) (hLM : c * M ≤ L) (hμ₀ : 0 < μ₀)
    (hCB : 0 ≤ CB) (B : ℤ → ℤ → ℝ) (d h μ : ℤ → ℝ)
    (hsym : ∀ k ∈ Finset.Icc (j - L) (j + L), ∀ m ∈ Finset.Icc (j - L) (j + L), B k m = B m k)
    (hpsd : ∀ x : ℤ → ℝ, 0 ≤ ∑ k ∈ Finset.Icc (j - L) (j + L),
      ∑ m ∈ Finset.Icc (j - L) (j + L), B k m * x k * x m)
    (hdecay : ∀ k m : ℤ, |B k m| ≤ CB * ((1 + |(k:ℝ) - m|) ^ 5)⁻¹)
    (hμ : ∀ k ∈ Finset.Icc (j - L) (j + L), μ₀ ≤ μ k)
    (hh : ∀ k ∈ Finset.Icc (j - L) (j + L),
      h k = ∑ m ∈ Finset.Icc (j - L) (j + L), B k m * d m + μ k * d k)
    (hsmall : ε ^ 2 * (CB * Z3) ≤ μ₀)
    (hres : ∀ k ∈ Finset.Icc (j - L) (j + L),
      |h k| ≤ Ch * (1 / M + ((1 + Rate514.Dist L j k) ^ 3)⁻¹)) :
    d j ^ 2 ≤ 4 / μ₀ ^ 2 * (2 * Ch ^ 2 * (Ωε ε + 8 * Z2 / (ε ^ 2 * c ^ 2)) / M ^ 2) := by
  have hj : j ∈ Finset.Icc (j - L) (j + L) := by
    simp only [Finset.mem_Icc]; constructor <;> linarith [(Nat.cast_nonneg L : (0:ℤ) ≤ L)]
  have hcb := centre_bound (Finset.Icc (j - L) (j + L)) j hj hε.le B d h μ hμ₀ hsym hpsd
    (fun k _ => row_moment_bound _ B hCB hdecay k) hμ hh hsmall
  have hsum := residual_sum3 j L hL hε hε1 hM hc hLM h hres
  exact hcb.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

/-- **Theorem 5.14, conclusion (160).** If `a_j = √β_j^{[M]}/M ≤ 1/2`,
`b_j = ξ_{j/M}/2` and `(a_j - b_j)² ≤ K²/M²`, then both bounds of (160) hold with `C = K`. -/
theorem theorem_5_14_conclusion {j M : ℕ} (hM : 0 < M) (hβ : 0 ≤ UniformLanczos.Theorem59.betaM M j)
    (ht : 0 < (j : ℝ) / M)
    (hbound : Real.sqrt (UniformLanczos.Theorem59.betaM M j) / (M : ℝ) ≤ 1 / 2) {K : ℝ}
    (hK : 0 ≤ K)
    (hd : (Real.sqrt (UniformLanczos.Theorem59.betaM M j) / (M : ℝ) -
      Profile.ξ ((j : ℝ) / M) / 2) ^ 2 ≤ K ^ 2 / (M : ℝ) ^ 2) :
    |Real.sqrt (UniformLanczos.Theorem59.betaM M j) / (M : ℝ) - Profile.ξ ((j : ℝ) / M) / 2|
        ≤ K / M ∧
      |UniformLanczos.Theorem59.betaM M j / (M : ℝ) ^ 2 - Profile.F ((j : ℝ) / M)| ≤ K / M := by
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have h1 : |Real.sqrt (UniformLanczos.Theorem59.betaM M j) / (M : ℝ) -
      Profile.ξ ((j : ℝ) / M) / 2| ≤ K / M := by
    rw [← div_pow] at hd
    exact abs_le_of_sq_le_sq' hd (by positivity) |> fun h => abs_le.mpr ⟨h.1, h.2⟩
  exact ⟨h1, UniformLanczos.Theorem514.beta_rate_of_sqrt_rate hM hβ ht hbound h1⟩

end UniformLanczos.Rate514Assembly

#print axioms UniformLanczos.Rate514Assembly.dist_le_of_not_mem
#print axioms UniformLanczos.Rate514Assembly.hybrid_tail
#print axioms UniformLanczos.Rate514Assembly.residual_difference
#print axioms UniformLanczos.Rate514Assembly.mu_lower
#print axioms UniformLanczos.Rate514Assembly.ω_dist_le3
#print axioms UniformLanczos.Rate514Assembly.residual_sum3
#print axioms UniformLanczos.Rate514Assembly.rate_assembly
#print axioms UniformLanczos.Rate514Assembly.theorem_5_14_conclusion
