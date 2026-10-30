/-
Uniform Lanczos note, Task L4 (2026-10-29): higher coefficients of the limit profile.

All polynomials below were produced by exact rational series arithmetic (Bernoulli numbers,
series reversion, Wallis moments) and are *verified* here by `ring`; the remainders are explicit.

* `exp18`, `sinh_cosh_approx18` : Taylor approximations of `exp`, `sinh`, `cosh` of order 17 on `[0,1]`
  with remainder `≤ u¹⁸ / 6·10¹⁵`;
* `Lp_taylor13`  : `|Λ'(s) - Σ_{k=1}^{7} B_{2k} s^{2k-1}/(2k)!| ≤ s¹⁵ / (2.5·10¹²)` for `0 ≤ s ≤ 2`;
* `Lp_slope_lower`, `abs_sub_le_of_Lp` : `Λ'' ≥ 1/32` on `(0,2]`, hence `|a - b| ≤ 32 |Λ'(a) - Λ'(b)|`
  on `[0,2]`;
* `LpPoly_IpPoly`, `Rcomp_bound` : the candidate inverse `IpPoly` satisfies
  `LpPoly (IpPoly x) - x = x¹⁵ Rcomp x` with `|Rcomp x| ≤ 6936` on `[0, 1/40]`;
* `Ip_expansion13` : `|I'(x) - (12x + (144/5)x³ + (19008/175)x⁵ + (393984/875)x⁷
  + (129143808/67375)x⁹ + (179132166144/21896875)x¹¹ + (3789966163968/109484375)x¹³)| ≤ 9·10⁵ x¹⁵`
  for `0 ≤ x ≤ 1/40`;
* `Hint_IpPoly`, `Hint_expansion14` : the Wallis moments give
  `H(a) = Φ(a²) + O(a¹⁶)` with `Φ(A) = 3A + (27/5)A² + (594/35)A³ + (1539/25)A⁴ + (2270106/9625)A⁵
  + (262400634/284375)A⁶ + (2775854124/765625)A⁷`;
* `GPoly_PhiPoly`, `R2_bound`, `GPoly_lipschitz`, `inversion7` : reversion of `Φ`;
* `F_expansion7` : for `0 ≤ a ≤ 1/40` and `α = H(a)`,
  `|a²/4 - (α/12 - α²/20 + 4α³/525 + 2α⁴/525 + 368α⁵/336875 - 544α⁶/1340625
  - 1886176α⁷/2299171875)| ≤ 225 α⁸`, i.e. `F(α) = α/12 - α²/20 + 4α³/525 + ⋯ + O(α⁸)`.
-/
import UniformLanczos.Expansion

open Set Real intervalIntegral

namespace UniformLanczos

/-! ### Taylor approximations of `exp`, `sinh`, `cosh` of order 17 -/

/-- `Σ_{k<18} x^k/k!`. -/
noncomputable def E18 (x : ℝ) : ℝ := @@E18@@

/-- odd part of `E18`. -/
noncomputable def S17 (u : ℝ) : ℝ := @@S17@@

/-- even part of `E18`. -/
noncomputable def C16 (u : ℝ) : ℝ := @@C16@@

lemma E18_eq_sum (x : ℝ) : ∑ m ∈ Finset.range 18, x ^ m / (m.factorial : ℝ) = E18 x := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  unfold E18
  push_cast
  ring

lemma exp18 {x : ℝ} (hx : |x| ≤ 1) : |exp x - E18 x| ≤ |x| ^ 18 / 6000000000000000 := by
  have h := Real.exp_bound hx (n := 18) (by norm_num)
  rw [E18_eq_sum] at h
  refine h.trans ?_
  have h18 : 0 ≤ |x| ^ 18 := pow_nonneg (abs_nonneg x) 18
  have hc : ((Nat.succ 18 : ℕ) : ℝ) / (((Nat.factorial 18 : ℕ) : ℝ) * ((18 : ℕ) : ℝ))
      ≤ 1 / 6000000000000000 := by
    norm_num [Nat.factorial]
  calc |x| ^ 18 * (((Nat.succ 18 : ℕ) : ℝ) / (((Nat.factorial 18 : ℕ) : ℝ) * ((18 : ℕ) : ℝ)))
      ≤ |x| ^ 18 * (1 / 6000000000000000) := mul_le_mul_of_nonneg_left hc h18
    _ = |x| ^ 18 / 6000000000000000 := by ring

lemma sinh_cosh_approx18 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    |sinh u - S17 u| ≤ u ^ 18 / 6000000000000000 ∧
    |cosh u - C16 u| ≤ u ^ 18 / 6000000000000000 := by
  have hp := exp18 (x := u) (by rw [abs_of_nonneg h0]; exact h1)
  have hm := exp18 (x := -u) (by rw [abs_neg, abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at hp
  rw [abs_neg, abs_of_nonneg h0] at hm
  have hs : sinh u - S17 u = ((exp u - E18 u) - (exp (-u) - E18 (-u))) / 2 := by
    rw [sinh_eq]; unfold S17 E18; ring
  have hc : cosh u - C16 u = ((exp u - E18 u) + (exp (-u) - E18 (-u))) / 2 := by
    rw [cosh_eq]; unfold C16 E18; ring
  rw [abs_le] at hp hm
  constructor
  · rw [hs, abs_le]; constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]
  · rw [hc, abs_le]; constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]

/-! ### Taylor expansion of `Λ'` through `s¹³` -/

/-- `Σ_{k=1}^{7} B_{2k} s^{2k-1}/(2k)!` (Bernoulli numbers `B₂,…,B₁₄`). -/
noncomputable def LpPoly (s : ℝ) : ℝ := @@LPPOLY@@

/-- `Wpoly u = 1 + 2u LpPoly(2u)`. -/
noncomputable def Wpoly (u : ℝ) : ℝ := @@WPOLY@@

/-- `u C16 u - S17 u · Wpoly u = u¹⁷ Tpoly u`. -/
noncomputable def Tpoly (u : ℝ) : ℝ := @@TPOLY@@

lemma Wpoly_eq (u : ℝ) : Wpoly u = 1 + 2 * u * LpPoly (2 * u) := by
  unfold Wpoly LpPoly; ring

lemma Tpoly_bound {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : |Tpoly u| ≤ 24 / 1000000000 := by
  have hp : ∀ n : ℕ, 0 ≤ u ^ n ∧ u ^ n ≤ 1 := fun n => ⟨pow_nonneg h0 n, pow_le_one₀ h0 h1⟩
@@T_HAVES@@
  unfold Tpoly
  rw [abs_le]; constructor <;> linarith

lemma Wpoly_bounds {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : 0 ≤ Wpoly u ∧ Wpoly u ≤ 7 / 5 := by
  have hp : ∀ n : ℕ, 0 ≤ u ^ n ∧ u ^ n ≤ 1 := fun n => ⟨pow_nonneg h0 n, pow_le_one₀ h0 h1⟩
@@W_HAVES@@
  unfold Wpoly
  constructor <;> linarith

lemma E17_identity (u : ℝ) :
    u * cosh u - sinh u - 2 * u * sinh u * LpPoly (2 * u) =
      u ^ 17 * Tpoly u + u * (cosh u - C16 u) - Wpoly u * (sinh u - S17 u) := by
  unfold Tpoly Wpoly LpPoly C16 S17; ring

lemma E17_bound {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    |u * cosh u - sinh u - 2 * u * sinh u * LpPoly (2 * u)| ≤ u ^ 17 / 40000000 := by
  obtain ⟨hs, hc⟩ := sinh_cosh_approx18 h0 h1
  obtain ⟨hW0, hW1⟩ := Wpoly_bounds h0 h1
  have hT := Tpoly_bound h0 h1
  rw [E17_identity]
  have h17 : 0 ≤ u ^ 17 := pow_nonneg h0 17
  have h18 : u ^ 18 ≤ u ^ 17 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have e1 : |u ^ 17 * Tpoly u| ≤ u ^ 17 * (24 / 1000000000) := by
    rw [abs_mul, abs_of_nonneg h17]; exact mul_le_mul_of_nonneg_left hT h17
  have e2 : |u * (cosh u - C16 u)| ≤ u ^ 17 / 6000000000000000 := by
    rw [abs_mul, abs_of_nonneg h0]
    calc u * |cosh u - C16 u| ≤ 1 * (u ^ 18 / 6000000000000000) :=
          mul_le_mul h1 hc (abs_nonneg _) (by norm_num)
      _ ≤ u ^ 17 / 6000000000000000 := by linarith
  have e3 : |Wpoly u * (sinh u - S17 u)| ≤ 7 / 5 * (u ^ 17 / 6000000000000000) := by
    rw [abs_mul, abs_of_nonneg hW0]
    calc Wpoly u * |sinh u - S17 u| ≤ 7 / 5 * (u ^ 18 / 6000000000000000) :=
          mul_le_mul hW1 hs (abs_nonneg _) (by norm_num)
      _ ≤ 7 / 5 * (u ^ 17 / 6000000000000000) := by linarith
  rw [abs_le] at e1 e2 e3 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

/-- `|Λ'(s) - LpPoly s| ≤ s¹⁵ / (2.5·10¹²)` for `0 ≤ s ≤ 2`. -/
theorem Lp_taylor13 {s : ℝ} (h0 : 0 ≤ s) (h2 : s ≤ 2) :
    |Lp s - LpPoly s| ≤ s ^ 15 / 2500000000000 := by
  rcases eq_or_lt_of_le h0 with hz | hpos
  · rw [← hz, Lp_zero]; norm_num [LpPoly]
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = s / 2 := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u ≤ 1 := by rw [hu]; linarith
  have hsu : s = 2 * u := by rw [hu]; ring
  have hsh : 0 < sinh u := sinh_pos_iff.mpr hu0
  have hsl : u < sinh u := self_lt_sinh_iff.mpr hu0
  have hE := E17_bound hu0.le hu1
  have hD : 0 < 2 * u * sinh u := by positivity
  have hrepr : Lp s - LpPoly s =
      (u * cosh u - sinh u - 2 * u * sinh u * LpPoly (2 * u)) / (2 * u * sinh u) := by
    rw [Lp_hyp hpos.ne', hsu]
    have e : 2 * u / 2 = u := by ring
    rw [e]
    field_simp
  rw [hrepr, abs_div, abs_of_pos hD, div_le_iff₀ hD]
  have hD2 : 2 * u ^ 2 ≤ 2 * u * sinh u := by nlinarith
  have h15 : 0 ≤ s ^ 15 := pow_nonneg h0 15
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  calc |u * cosh u - sinh u - 2 * u * sinh u * LpPoly (2 * u)| ≤ u ^ 17 / 40000000 := hE
    _ = s ^ 15 / 2621440000000 * (2 * u ^ 2) := by rw [hsu]; ring
    _ ≤ s ^ 15 / 2500000000000 * (2 * u * sinh u) := by
        nlinarith [mul_le_mul_of_nonneg_left hD2 h15, mul_nonneg h15 hu2]

/-! ### `Λ'' ≥ 1/32` on `(0,2]` and the Lipschitz bound for the inverse -/

lemma sinh_bounds {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    u + u ^ 3 / 6 ≤ sinh u ∧ sinh u ≤ 3 / 2 * u := by
  obtain ⟨hs, -⟩ := sinh_cosh_approx h0 h1
  rw [abs_le] at hs
  have h3 : u ^ 3 ≤ u := by
    calc u ^ 3 ≤ u ^ 1 := pow_le_pow_of_le_one h0 h1 (by norm_num)
      _ = u := pow_one u
  have h5 : u ^ 5 ≤ u := by
    calc u ^ 5 ≤ u ^ 1 := pow_le_pow_of_le_one h0 h1 (by norm_num)
      _ = u := pow_one u
  have h7 : u ^ 7 ≤ u := by
    calc u ^ 7 ≤ u ^ 1 := pow_le_pow_of_le_one h0 h1 (by norm_num)
      _ = u := pow_one u
  have h9 : u ^ 9 ≤ u := by
    calc u ^ 9 ≤ u ^ 1 := pow_le_pow_of_le_one h0 h1 (by norm_num)
      _ = u := pow_one u
  have h95 : u ^ 9 ≤ u ^ 5 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have h70 : 0 ≤ u ^ 7 := pow_nonneg h0 7
  constructor <;> linarith [hs.1, hs.2]

lemma Lpp_ge {s : ℝ} (h0 : 0 < s) (h2 : s ≤ 2) : 1 / 32 ≤ Lpp s := by
  unfold Lpp
  rw [exp_div_sq_eq h0.ne']
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = s / 2 := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u ≤ 1 := by rw [hu]; linarith
  have hsu : s = 2 * u := by rw [hu]; ring
  rw [← hu, hsu]
  obtain ⟨hlo, hhi⟩ := sinh_bounds hu0.le hu1
  have hsh : 0 < sinh u := sinh_pos_iff.mpr hu0
  have hsq_lo : u ^ 2 + u ^ 4 / 3 ≤ sinh u ^ 2 := by
    have h3 : 0 ≤ u ^ 3 := pow_nonneg hu0.le 3
    nlinarith [mul_le_mul hlo hlo (by positivity) hsh.le]
  have hsq_hi : sinh u ^ 2 ≤ 9 / 4 * u ^ 2 := by
    nlinarith [mul_le_mul hhi hhi hsh.le (by positivity)]
  have hu2 : 0 < u ^ 2 := by positivity
  have hS2 : 0 < sinh u ^ 2 := by positivity
  rw [div_sub_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hsq_hi hu2.le, mul_le_mul_of_nonneg_left hsq_lo hu2.le]

theorem Lp_slope_lower {σ σ' : ℝ} (hσ : 0 ≤ σ) (h : σ ≤ σ') (h2 : σ' ≤ 2) :
    (σ' - σ) / 32 ≤ Lp σ' - Lp σ := by
  rcases eq_or_lt_of_le h with h1 | h1
  · rw [h1]; simp
  have hcont : ContinuousOn Lp (Icc σ σ') := Lp_continuous.continuousOn
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope Lp Lpp h1 hcont
    (fun x hx => hasDerivAt_Lp (by linarith [hx.1] : x ≠ 0))
  have hcpos : 0 < c := lt_of_le_of_lt hσ hc.1
  have hle := Lpp_ge hcpos (by linarith [hc.2])
  rw [hceq, le_div_iff₀ (by linarith)] at hle
  linarith

theorem abs_sub_le_of_Lp {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha2 : a ≤ 2) (hb2 : b ≤ 2) :
    |a - b| ≤ 32 * |Lp a - Lp b| := by
  rcases le_total a b with hab | hab
  · have := Lp_slope_lower ha hab hb2
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have := Lp_slope_lower hb hab ha2
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

/-! ### Reversion of `LpPoly`: the expansion of `I'` through `x¹³` -/

/-- the inverse series of `Λ'` through `x¹³`:
`12x + (144/5)x³ + (19008/175)x⁵ + (393984/875)x⁷ + (129143808/67375)x⁹
+ (179132166144/21896875)x¹¹ + (3789966163968/109484375)x¹³`. -/
noncomputable def IpPoly (x : ℝ) : ℝ := @@IPPOLY@@

/-- `(LpPoly (IpPoly x) - x) / x¹⁵`, an explicit polynomial of degree 154 (even powers only). -/
noncomputable def Rcomp (x : ℝ) : ℝ := @@RCOMP@@

set_option maxHeartbeats 4000000 in
theorem LpPoly_IpPoly (x : ℝ) : LpPoly (IpPoly x) - x = x ^ 15 * Rcomp x := by
  unfold LpPoly IpPoly Rcomp
  ring

set_option maxRecDepth 100000 in
theorem Rcomp_bound {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 40) : |Rcomp x| ≤ 6936 := by
  have hp : ∀ n : ℕ, 0 ≤ x ^ n ∧ x ^ n ≤ (1 / 40 : ℝ) ^ n :=
    fun n => ⟨pow_nonneg h0 n, pow_le_pow_left₀ h0 h1 n⟩
@@RCOMP_HAVES@@
  unfold Rcomp
  rw [abs_le]; constructor <;> linarith

lemma IpPoly_bounds {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 40) :
    0 ≤ IpPoly x ∧ IpPoly x ≤ 13 * x := by
  have hp : ∀ n : ℕ, 0 ≤ x ^ n ∧ x ^ n ≤ (1 / 40 : ℝ) ^ n :=
    fun n => ⟨pow_nonneg h0 n, pow_le_pow_left₀ h0 h1 n⟩
@@Q_HAVES@@
  constructor
  · unfold IpPoly; positivity
  · have hb : (144 / 5 : ℝ) * x ^ 2 + (19008 / 175 : ℝ) * x ^ 4 + (393984 / 875 : ℝ) * x ^ 6
        + (129143808 / 67375 : ℝ) * x ^ 8 + (179132166144 / 21896875 : ℝ) * x ^ 10
        + (3789966163968 / 109484375 : ℝ) * x ^ 12 ≤ 1 := by linarith
    have := mul_le_mul_of_nonneg_left hb h0
    unfold IpPoly
    nlinarith [this]

/-- `|I'(x) - IpPoly x| ≤ 9·10⁵ x¹⁵` for `0 ≤ x ≤ 1/40`. -/
theorem Ip_expansion13 {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 40) :
    |Ip x - IpPoly x| ≤ 900000 * x ^ 15 := by
  have hL1 : 1 / 40 ≤ Lp 1 := by
    have := abs_le.mp (Lp_taylor one_pos (by norm_num))
    linarith [this.1]
  have hL2 : Lp 1 < 1 / 2 := Lp_lt_half one_pos
  have hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith, by linarith⟩
  have h1m : Lp 1 ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith [Lp_pos one_pos], hL2⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = Ip x := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = IpPoly x := ⟨_, rfl⟩
  rw [← hσdef, ← hydef]
  have hσ0 : 0 ≤ σ := by rw [hσdef]; exact Ip_nonneg h0 (by linarith)
  have hσ1 : σ ≤ 1 := by
    have := Ip_strictMonoOn.monotoneOn hx h1m (by linarith : x ≤ Lp 1)
    rwa [Ip_Lp, ← hσdef] at this
  have hxσ : Lp σ = x := by rw [hσdef]; exact Lp_Ip hx
  obtain ⟨hy0, hy13⟩ := IpPoly_bounds h0 h1
  rw [← hydef] at hy0 hy13
  have hT := Lp_taylor13 hy0 (by linarith)
  have hC := LpPoly_IpPoly x
  rw [← hydef] at hC
  have hR := Rcomp_bound h0 h1
  have hy15 : y ^ 15 ≤ (13 * x) ^ 15 := pow_le_pow_left₀ hy0 hy13 15
  have hx15 : 0 ≤ x ^ 15 := pow_nonneg h0 15
  have hslope := abs_sub_le_of_Lp hσ0 hy0 (by linarith) (by linarith)
  rw [hxσ] at hslope
  have e1 : |x - LpPoly y| ≤ 6936 * x ^ 15 := by
    have e : x - LpPoly y = -(x ^ 15 * Rcomp x) := by linarith
    rw [e, abs_neg, abs_mul, abs_of_nonneg hx15]
    calc x ^ 15 * |Rcomp x| ≤ x ^ 15 * 6936 := mul_le_mul_of_nonneg_left hR hx15
      _ = 6936 * x ^ 15 := by ring
  have e2 : |LpPoly y - Lp y| ≤ 13 ^ 15 * x ^ 15 / 2500000000000 := by
    rw [abs_sub_comm]
    refine hT.trans ?_
    rw [mul_pow] at hy15
    linarith
  have e3 : |x - Lp y| ≤ 6936 * x ^ 15 + 13 ^ 15 * x ^ 15 / 2500000000000 := by
    rw [abs_le] at e1 e2 ⊢
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  calc |σ - y| ≤ 32 * |x - Lp y| := hslope
    _ ≤ 32 * (6936 * x ^ 15 + 13 ^ 15 * x ^ 15 / 2500000000000) := by gcongr
    _ ≤ 900000 * x ^ 15 := by norm_num; linarith

/-! ### Wallis moments and the expansion of `H(a) = (1/π)∫₀^{π/2} a sin θ I'(a sin θ) dθ` -/

lemma wallis_step (n : ℕ) :
    ∫ θ in (0 : ℝ)..(π / 2), sin θ ^ (n + 2) =
      ((n : ℝ) + 1) / ((n : ℝ) + 2) * ∫ θ in (0 : ℝ)..(π / 2), sin θ ^ n := by
  rw [integral_sin_pow]
  simp [sin_zero, cos_pi_div_two]

lemma integral_sin_six : ∫ θ in (0 : ℝ)..(π / 2), sin θ ^ 6 = 5 * π / 32 := by
  rw [wallis_step 4, integral_sin_four_half_pi]; push_cast; ring

lemma integral_sin_eight : ∫ θ in (0 : ℝ)..(π / 2), sin θ ^ 8 = 35 * π / 256 := by
  rw [wallis_step 6, integral_sin_six]; push_cast; ring

lemma integral_sin_ten : ∫ θ in (0 : ℝ)..(π / 2), sin θ ^ 10 = 63 * π / 512 := by
  rw [wallis_step 8, integral_sin_eight]; push_cast; ring

lemma integral_sin_twelve : ∫ θ in (0 : ℝ)..(π / 2), sin θ ^ 12 = 231 * π / 2048 := by
  rw [wallis_step 10, integral_sin_ten]; push_cast; ring

lemma integral_sin_fourteen : ∫ θ in (0 : ℝ)..(π / 2), sin θ ^ 14 = 429 * π / 4096 := by
  rw [wallis_step 12, integral_sin_twelve]; push_cast; ring

lemma integral_sin_combo (c₂ c₄ c₆ c₈ c₁₀ c₁₂ c₁₄ : ℝ) :
    ∫ θ in (0 : ℝ)..(π / 2), (c₂ * sin θ ^ 2 + c₄ * sin θ ^ 4 + c₆ * sin θ ^ 6 + c₈ * sin θ ^ 8
      + c₁₀ * sin θ ^ 10 + c₁₂ * sin θ ^ 12 + c₁₄ * sin θ ^ 14) =
    c₂ * (π / 4) + c₄ * (3 * π / 16) + c₆ * (5 * π / 32) + c₈ * (35 * π / 256)
      + c₁₀ * (63 * π / 512) + c₁₂ * (231 * π / 2048) + c₁₄ * (429 * π / 4096) := by
  rw [integral_add, integral_add, integral_add, integral_add, integral_add, integral_add]
  · simp only [integral_const_mul]
    rw [integral_sin_sq_half_pi, integral_sin_four_half_pi, integral_sin_six, integral_sin_eight,
      integral_sin_ten, integral_sin_twelve, integral_sin_fourteen]
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- `Φ(A) = 3A + (27/5)A² + (594/35)A³ + (1539/25)A⁴ + (2270106/9625)A⁵ + (262400634/284375)A⁶
+ (2775854124/765625)A⁷`, so that `H(a) = Φ(a²) + O(a¹⁶)`. -/
noncomputable def PhiPoly (A : ℝ) : ℝ := @@PHIPOLY@@

lemma Hint_IpPoly (a : ℝ) : Hint (fun y => y * IpPoly y) a = PhiPoly (a ^ 2) := by
  unfold Hint
  have e : (fun θ => a * sin θ * IpPoly (a * sin θ)) = fun θ =>
      (12 * a ^ 2) * sin θ ^ 2 + (144 / 5 * a ^ 4) * sin θ ^ 4 + (19008 / 175 * a ^ 6) * sin θ ^ 6
      + (393984 / 875 * a ^ 8) * sin θ ^ 8 + (129143808 / 67375 * a ^ 10) * sin θ ^ 10
      + (179132166144 / 21896875 * a ^ 12) * sin θ ^ 12
      + (3789966163968 / 109484375 * a ^ 14) * sin θ ^ 14 := by
    funext θ; unfold IpPoly; ring
  rw [e, integral_sin_combo]
  unfold PhiPoly
  field_simp
  ring

theorem Hint_expansion14 {I1 : ℝ → ℝ} {b C : ℝ} (hC : 0 ≤ C)
    (hIc : ContinuousOn I1 (Icc 0 b))
    (hexp : ∀ x ∈ Icc 0 b, |I1 x - IpPoly x| ≤ C * x ^ 15) :
    ∀ a ∈ Icc 0 b, |Hint (fun y => y * I1 y) a - PhiPoly (a ^ 2)| ≤ C * a ^ 16 / 2 := by
  intro a ha
  rw [← Hint_IpPoly]
  have ha0 : a ∈ Icc 0 a := ⟨ha.1, le_rfl⟩
  have hab : Icc 0 a ⊆ Icc 0 b := Icc_subset_Icc le_rfl ha.2
  have hpc : ContinuousOn (fun y : ℝ => y * IpPoly y) (Icc 0 a) := by
    unfold IpPoly; fun_prop
  have hIc' : ContinuousOn (fun y => y * I1 y) (Icc 0 a) := continuousOn_id.mul (hIc.mono hab)
  have hclose : ∀ y ∈ Icc 0 a, |y * I1 y - y * IpPoly y| ≤ C * a ^ 16 := by
    intro y hy
    rw [← mul_sub, abs_mul, abs_of_nonneg hy.1]
    have h1 := hexp y (hab hy)
    have hy15 : y ^ 15 ≤ a ^ 15 := pow_le_pow_left₀ hy.1 hy.2 15
    calc y * |I1 y - IpPoly y| ≤ a * (C * a ^ 15) :=
          mul_le_mul hy.2 (h1.trans (mul_le_mul_of_nonneg_left hy15 hC)) (abs_nonneg _) ha.1
      _ = C * a ^ 16 := by ring
  have := Hint_close ha.1 hIc' hpc hclose a ha0
  linarith [this]

/-! ### Reversion of `Φ` and the profile `F(α) = a²/4` through `α⁷` -/

/-- the inverse series of `Φ` through `α⁷` (`A = GPoly α + O(α⁸)`). -/
noncomputable def GPoly (α : ℝ) : ℝ := @@GPOLY@@

/-- derivative of `GPoly`. -/
noncomputable def GPolyD (α : ℝ) : ℝ := @@GDPOLY@@

/-- `FPoly α = GPoly α / 4`: the printed coefficients of `F`. -/
noncomputable def FPoly (α : ℝ) : ℝ := @@FPOLY@@

/-- `(GPoly (PhiPoly A) - A) / A⁸`, an explicit polynomial of degree 41. -/
noncomputable def R2 (A : ℝ) : ℝ := @@R2@@

set_option maxHeartbeats 1000000 in
theorem GPoly_PhiPoly (A : ℝ) : GPoly (PhiPoly A) - A = A ^ 8 * R2 A := by
  unfold GPoly PhiPoly R2
  ring

set_option maxRecDepth 100000 in
theorem R2_bound {A : ℝ} (h0 : 0 ≤ A) (h1 : A ≤ 1 / 1600) : |R2 A| ≤ 4711 := by
  have hp : ∀ n : ℕ, 0 ≤ A ^ n ∧ A ^ n ≤ (1 / 1600 : ℝ) ^ n :=
    fun n => ⟨pow_nonneg h0 n, pow_le_pow_left₀ h0 h1 n⟩
@@R2_HAVES@@
  unfold R2
  rw [abs_le]; constructor <;> linarith

lemma FPoly_eq (α : ℝ) : FPoly α = GPoly α / 4 := by unfold FPoly GPoly; ring

lemma hasDerivAt_GPoly (t : ℝ) : HasDerivAt GPoly (GPolyD t) t := by
  have h := (((((((hasDerivAt_id t).const_mul (1 / 3 : ℝ)).add
    ((hasDerivAt_pow 2 t).const_mul (-1 / 5 : ℝ))).add
    ((hasDerivAt_pow 3 t).const_mul (16 / 525 : ℝ))).add
    ((hasDerivAt_pow 4 t).const_mul (8 / 525 : ℝ))).add
    ((hasDerivAt_pow 5 t).const_mul (1472 / 336875 : ℝ))).add
    ((hasDerivAt_pow 6 t).const_mul (-2176 / 1340625 : ℝ))).add
    ((hasDerivAt_pow 7 t).const_mul (-7544704 / 2299171875 : ℝ))
  convert h using 1
  · funext y; simp only [Pi.add_apply, GPoly, id]
  · simp only [GPolyD]; push_cast; ring

lemma GPolyD_bound {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 500) : |GPolyD t| ≤ 1 / 2 := by
  have hp : ∀ n : ℕ, 0 ≤ t ^ n ∧ t ^ n ≤ (1 / 500 : ℝ) ^ n :=
    fun n => ⟨pow_nonneg h0 n, pow_le_pow_left₀ h0 h1 n⟩
@@GD_HAVES@@
  unfold GPolyD
  rw [abs_le]; constructor <;> linarith

lemma GPoly_lip_aux {α β : ℝ} (hα0 : 0 ≤ α) (h : α < β) (hβ : β ≤ 1 / 500) :
    |GPoly β - GPoly α| ≤ 1 / 2 * (β - α) := by
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope GPoly GPolyD h
    (fun t _ => (hasDerivAt_GPoly t).continuousAt.continuousWithinAt)
    (fun t _ => hasDerivAt_GPoly t)
  have hb := GPolyD_bound (t := c) (by linarith [hc.1]) (by linarith [hc.2])
  have hd : 0 < β - α := by linarith
  rw [hceq, abs_div, abs_of_pos hd, div_le_iff₀ hd] at hb
  linarith

lemma GPoly_lipschitz {α β : ℝ} (hα : α ∈ Icc (0 : ℝ) (1 / 500)) (hβ : β ∈ Icc (0 : ℝ) (1 / 500)) :
    |GPoly α - GPoly β| ≤ 1 / 2 * |α - β| := by
  rcases lt_trichotomy α β with h | h | h
  · rw [abs_sub_comm, abs_sub_comm α, abs_of_pos (by linarith : 0 < β - α)]
    exact GPoly_lip_aux hα.1 h hβ.2
  · rw [h]; simp
  · rw [abs_of_pos (by linarith : 0 < α - β)]
    exact GPoly_lip_aux hβ.1 h hα.2

lemma small8 {A : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1 / 1600) : 450000 * A ^ 8 ≤ A := by
  have h7 : A ^ 7 ≤ (1 / 1600 : ℝ) ^ 7 := pow_le_pow_left₀ hA0 hA1 7
  have h78 : A ^ 8 = A ^ 7 * A := by ring
  rw [h78]
  nlinarith [mul_le_mul_of_nonneg_right h7 hA0]

theorem inversion7 {A α r : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1 / 1600)
    (hα : α = PhiPoly A + r) (hr : |r| ≤ 450000 * A ^ 8) :
    |A - GPoly α| ≤ 230000 * A ^ 8 := by
  have hp : ∀ n : ℕ, 0 ≤ A ^ n ∧ A ^ n ≤ (1 / 1600 : ℝ) ^ n :=
    fun n => ⟨pow_nonneg hA0 n, pow_le_pow_left₀ hA0 hA1 n⟩
@@PHI_HAVES@@
  have h8 := hp 8
  have hr' := abs_le.mp hr
  have hsmall := small8 hA0 hA1
  have hΦ0 : 0 ≤ PhiPoly A := by unfold PhiPoly; positivity
  have hΦ3 : 3 * A ≤ PhiPoly A := by unfold PhiPoly; linarith
  have hΦ1 : PhiPoly A ≤ 19 / 10000 := by unfold PhiPoly; linarith
  have hr1 : 450000 * A ^ 8 ≤ 1 / 10000 := by linarith
  have hαmem : α ∈ Icc (0 : ℝ) (1 / 500) := ⟨by rw [hα]; linarith, by rw [hα]; linarith⟩
  have hΦmem : PhiPoly A ∈ Icc (0 : ℝ) (1 / 500) := ⟨hΦ0, by linarith⟩
  have hlip := GPoly_lipschitz hΦmem hαmem
  have hid := GPoly_PhiPoly A
  have hR := R2_bound hA0 hA1
  have e1 : |A ^ 8 * R2 A| ≤ 4711 * A ^ 8 := by
    rw [abs_mul, abs_of_nonneg h8.1]
    calc A ^ 8 * |R2 A| ≤ A ^ 8 * 4711 := mul_le_mul_of_nonneg_left hR h8.1
      _ = 4711 * A ^ 8 := by ring
  have e2 : |PhiPoly A - α| = |r| := by
    rw [hα, show PhiPoly A - (PhiPoly A + r) = -r by ring, abs_neg]
  rw [e2] at hlip
  have e3 : A - GPoly α = -(A ^ 8 * R2 A) + (GPoly (PhiPoly A) - GPoly α) := by linarith
  rw [e3]
  rw [abs_le] at e1 hlip ⊢
  constructor <;> linarith [hr'.1, hr'.2, e1.1, e1.2, hlip.1, hlip.2]

lemma A_le_half_alpha7 {A α r : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1 / 1600)
    (hα : α = PhiPoly A + r) (hr : |r| ≤ 450000 * A ^ 8) : 2 * A ≤ α := by
  have hp : ∀ n : ℕ, 0 ≤ A ^ n ∧ A ^ n ≤ (1 / 1600 : ℝ) ^ n :=
    fun n => ⟨pow_nonneg hA0 n, pow_le_pow_left₀ hA0 hA1 n⟩
@@PHI_HAVES@@
  have hr' := abs_le.mp hr
  have hsmall := small8 hA0 hA1
  rw [hα]
  unfold PhiPoly
  linarith [hr'.1]

/-- **Task L4.** For `0 ≤ a ≤ 1/40` and `α = H(a)`:
`|a²/4 - FPoly α| ≤ 225 α⁸`, where
`FPoly α = α/12 - α²/20 + 4α³/525 + 2α⁴/525 + 368α⁵/336875 - 544α⁶/1340625 - 1886176α⁷/2299171875`. -/
theorem F_expansion7 : ∀ a ∈ Icc (0 : ℝ) (1 / 40),
    |a ^ 2 / 4 - FPoly (Hint (fun y => y * Ip y) a)| ≤ 225 * Hint (fun y => y * Ip y) a ^ 8 := by
  intro a ha
  have hIc : ContinuousOn Ip (Icc 0 (1 / 40)) :=
    Ip_continuousOn.mono fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hexp : ∀ x ∈ Icc (0 : ℝ) (1 / 40), |Ip x - IpPoly x| ≤ 900000 * x ^ 15 :=
    fun x hx => Ip_expansion13 hx.1 hx.2
  have hH := Hint_expansion14 (by norm_num) hIc hexp a ha
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = Hint (fun y => y * Ip y) a := ⟨_, rfl⟩
  rw [← hα] at hH ⊢
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = a ^ 2 := ⟨_, rfl⟩
  rw [← hA] at hH ⊢
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hA1 : A ≤ 1 / 1600 := by rw [hA]; nlinarith [ha.1, ha.2]
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = α - PhiPoly A := ⟨_, rfl⟩
  have hαr : α = PhiPoly A + r := by rw [hr]; ring
  have hrA : |r| ≤ 450000 * A ^ 8 := by
    rw [hr]
    have e : 900000 * a ^ 16 / 2 = 450000 * A ^ 8 := by rw [hA]; ring
    rw [← e]; exact hH
  have hinv := inversion7 hA0 hA1 hαr hrA
  have h2A := A_le_half_alpha7 hA0 hA1 hαr hrA
  have hA8 : A ^ 8 ≤ α ^ 8 / 256 := by
    have := pow_le_pow_left₀ (by linarith : 0 ≤ 2 * A) h2A 8
    linarith
  have hα8 : 0 ≤ α ^ 8 := by positivity
  rw [FPoly_eq]
  have e : |A / 4 - GPoly α / 4| = |A - GPoly α| / 4 := by
    rw [show A / 4 - GPoly α / 4 = (A - GPoly α) / 4 by ring, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  rw [e]
  linarith

/-- the same statement with the polynomial written out. -/
theorem F_expansion7_explicit : ∀ a ∈ Icc (0 : ℝ) (1 / 40),
    |a ^ 2 / 4 - (Hint (fun y => y * Ip y) a / 12 - Hint (fun y => y * Ip y) a ^ 2 / 20
      + 4 * Hint (fun y => y * Ip y) a ^ 3 / 525 + 2 * Hint (fun y => y * Ip y) a ^ 4 / 525
      + 368 * Hint (fun y => y * Ip y) a ^ 5 / 336875 - 544 * Hint (fun y => y * Ip y) a ^ 6 / 1340625
      - 1886176 * Hint (fun y => y * Ip y) a ^ 7 / 2299171875)|
      ≤ 225 * Hint (fun y => y * Ip y) a ^ 8 := by
  intro a ha
  have h := F_expansion7 a ha
  unfold FPoly at h
  convert h using 3
  ring

/-- the expansion of `I'` with the polynomial written out. -/
theorem Ip_expansion13_explicit {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 40) :
    |Ip x - (12 * x + 144 / 5 * x ^ 3 + 19008 / 175 * x ^ 5 + 393984 / 875 * x ^ 7
      + 129143808 / 67375 * x ^ 9 + 179132166144 / 21896875 * x ^ 11
      + 3789966163968 / 109484375 * x ^ 13)| ≤ 900000 * x ^ 15 := by
  have h := Ip_expansion13 h0 h1
  unfold IpPoly at h
  convert h using 3

end UniformLanczos
