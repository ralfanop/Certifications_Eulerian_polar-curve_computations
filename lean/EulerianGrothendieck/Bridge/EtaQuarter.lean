import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Exponential

/-!
# Lean certificate of the saddlepoint value `η(1/4) ≈ -0.184391`

Manuscript V173, Lemma 5.5, eq. (114): `η = (κ₄/v² - 5κ₃²/(3v³))/8` with
`v = Λ''(s(x))`, `κ_r = Λ^{(r)}(s(x))`, `Λ(s) = log(sinh(s/2)/(s/2))`, and `s(x)` the inverse of `Λ'`.

We write `g(s) = 1/(e^s - 1)`, `h = g + g²` (so `h = 1/(4 sinh²(s/2))`), and prove for `s > 0`
`Λ' = 1/2 + g - 1/s`, `Λ'' = 1/s² - h`, `Λ''' = h(1+2g) - 2/s³`, `Λ'''' = 6/s⁴ - h((1+2g)² + 2h)`
as genuine derivatives. `Λ'` is strictly increasing on `(0,∞)`; the root `s(1/4)` of `Λ'(s) = 1/4`
is enclosed in a rational interval of width `10^{-13}`, and interval arithmetic gives
`|η(1/4) + 0.184391| < 5·10^{-7}`.
-/

open Real

namespace EulerianBridge.EtaQuarter

noncomputable def g (s : ℝ) : ℝ := 1 / (exp s - 1)
noncomputable def h (s : ℝ) : ℝ := g s + g s ^ 2

noncomputable def Λ (s : ℝ) : ℝ := log (sinh (s / 2) / (s / 2))
noncomputable def L1 (s : ℝ) : ℝ := 1 / 2 + g s - 1 / s
noncomputable def L2 (s : ℝ) : ℝ := 1 / s ^ 2 - h s
noncomputable def L3 (s : ℝ) : ℝ := h s * (1 + 2 * g s) - 2 / s ^ 3
noncomputable def L4 (s : ℝ) : ℝ := 6 / s ^ 4 - h s * ((1 + 2 * g s) ^ 2 + 2 * h s)

/-- The saddlepoint correction `η` as a function of `s`. -/
noncomputable def etaS (s : ℝ) : ℝ := (L4 s / L2 s ^ 2 - 5 * L3 s ^ 2 / (3 * L2 s ^ 3)) / 8

theorem expm1_pos {s : ℝ} (hs : 0 < s) : 0 < exp s - 1 := by linarith [add_one_lt_exp hs.ne']

theorem hasDerivAt_g {s : ℝ} (hs : 0 < s) : HasDerivAt g (-(g s + g s ^ 2)) s := by
  have hne := (expm1_pos hs).ne'
  have := ((hasDerivAt_exp s).sub_const 1).inv hne
  unfold g
  simp only [one_div]
  convert this using 1
  have he : exp s = (exp s - 1) + 1 := by ring
  field_simp
  ring

theorem hasDerivAt_h {s : ℝ} (hs : 0 < s) : HasDerivAt h (-(h s * (1 + 2 * g s))) s := by
  have hg := hasDerivAt_g hs
  have := hg.add (hg.pow 2)
  unfold h
  convert this using 1
  simp; ring

theorem hasDerivAt_L1 {s : ℝ} (hs : 0 < s) : HasDerivAt L1 (L2 s) s := by
  have := ((hasDerivAt_g hs).const_add (1 / 2)).sub ((hasDerivAt_id s).inv hs.ne')
  unfold L1 L2 h
  simp only [one_div] at this ⊢
  convert this using 1
  simp; ring

theorem hasDerivAt_L2 {s : ℝ} (hs : 0 < s) : HasDerivAt L2 (L3 s) s := by
  have hp : HasDerivAt (fun s : ℝ => 1 / s ^ 2) (-2 / s ^ 3) s := by
    have := ((hasDerivAt_pow 2 s).inv (pow_ne_zero 2 hs.ne'))
    simp only [one_div]
    convert this using 1
    field_simp; ring
  have := hp.sub (hasDerivAt_h hs)
  unfold L2 L3
  convert this using 1
  ring

theorem hasDerivAt_L3 {s : ℝ} (hs : 0 < s) : HasDerivAt L3 (L4 s) s := by
  have hp : HasDerivAt (fun s : ℝ => 2 / s ^ 3) (-6 / s ^ 4) s := by
    have := ((hasDerivAt_pow 3 s).inv (pow_ne_zero 3 hs.ne')).const_mul 2
    simp only [div_eq_mul_inv]
    convert this using 1
    field_simp; ring
  have hg := hasDerivAt_g hs
  have hh := hasDerivAt_h hs
  have := (hh.mul ((hg.const_mul 2).const_add 1)).sub hp
  unfold L3 L4
  convert this using 1
  simp only [h]; ring

/-- `Λ' = L1` on `(0,∞)`: `d/ds log(sinh(s/2)/(s/2)) = (1/2)coth(s/2) - 1/s = 1/2 + 1/(e^s-1) - 1/s`. -/
theorem coth_half (u : ℝ) (hu : 0 < u) :
    cosh u / (2 * sinh u) = 1 / 2 + 1 / (exp (2 * u) - 1) := by
  have he : exp (2 * u) = exp u * exp u := by rw [← exp_add]; ring_nf
  have hn : exp (-u) = 1 / exp u := by rw [exp_neg, one_div]
  have hp := exp_pos u
  have h1 : 1 < exp u := one_lt_exp_iff.mpr hu
  have hd : exp u * exp u - 1 ≠ 0 := by nlinarith
  have hs : exp u - 1 / exp u ≠ 0 := by
    intro h0; field_simp at h0; nlinarith
  rw [cosh_eq, sinh_eq, he, hn]
  have hd2 : -1 + exp u ^ 2 ≠ 0 := by nlinarith
  rw [eq_comm, ← sub_eq_zero]
  field_simp
  have hx : (-1 + exp u ^ 2)⁻¹ * (-1 + exp u ^ 2) = 1 := inv_mul_cancel₀ hd2
  linear_combination (-1:ℝ) * hx

theorem hasDerivAt_Λ {s : ℝ} (hs : 0 < s) : HasDerivAt Λ (L1 s) s := by
  have hs2 : 0 < s / 2 := by positivity
  have hsh : 0 < sinh (s / 2) := sinh_pos_iff.mpr hs2
  have hq : 0 < sinh (s / 2) / (s / 2) := div_pos hsh hs2
  have d1 : HasDerivAt (fun s => sinh (s / 2)) (cosh (s / 2) / 2) s := by
    have := (hasDerivAt_sinh (s / 2)).comp s ((hasDerivAt_id s).div_const 2)
    simpa [div_eq_mul_inv, mul_comm] using this
  have d2 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) s := (hasDerivAt_id s).div_const 2
  have hl := (d1.div d2 hs2.ne').log hq.ne'
  unfold Λ
  convert hl using 1
  simp only [Pi.div_apply]
  · have hc := coth_half (s / 2) hs2
    rw [show 2 * (s / 2) = s by ring] at hc
    unfold L1 g
    rw [← hc]
    field_simp

/-- `Λ'' > 0` on `(0,∞)`: `4 sinh²(s/2) > s²`. -/
theorem L2_pos {s : ℝ} (hs : 0 < s) : 0 < L2 s := by
  -- h = e^s/(e^s-1)^2 and 1/s^2 - e^s/(e^s-1)^2 > 0 ⇔ (e^s - 1)^2 > s^2 e^s ⇔ e^{s/2} - e^{-s/2} > s
  have hE := expm1_pos hs
  unfold L2 h g
  have key : s ^ 2 * exp s < (exp s - 1) ^ 2 := by
    have hu : 0 < s / 2 := by positivity
    have hsh : s / 2 < sinh (s / 2) := by
      have := sinh_lt_cosh (s / 2)
      -- standard: x < sinh x for x > 0
      exact Real.self_lt_sinh_iff.mpr hu
    rw [sinh_eq] at hsh
    have h1 : exp (s / 2) * exp (s / 2) = exp s := by rw [← exp_add]; ring_nf
    have h2 : exp (s / 2) * exp (-(s / 2)) = 1 := by rw [← exp_add]; simp
    have hp := exp_pos (s / 2)
    -- s e^{s/2} < e^s - 1
    have h3 : s * exp (s / 2) < exp s - 1 := by nlinarith
    have h4 : 0 < s * exp (s / 2) := by positivity
    nlinarith [h3, h4, h1]
  have hs2 : 0 < s ^ 2 := by positivity
  rw [sub_pos]
  have : 1 / (exp s - 1) + (1 / (exp s - 1)) ^ 2 = exp s / (exp s - 1) ^ 2 := by
    field_simp; ring
  rw [this, div_lt_div_iff₀ (by positivity) hs2]
  nlinarith

theorem L1_strictMonoOn : StrictMonoOn L1 (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro s hs; exact (hasDerivAt_L1 hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    rw [(hasDerivAt_L1 hs).deriv]
    exact L2_pos hs

/-! ## Rational enclosures -/

/-- The bracketing rationals for `s(1/4)`. -/
def sa : ℚ := 35935119694474 / 10 ^ 13
def sb : ℚ := 35935119694475 / 10 ^ 13

/-- Taylor enclosure of `exp q` for `0 ≤ q ≤ 1` with `30` terms. -/
theorem exp_enclose {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ i ∈ Finset.range 30, q ^ i / (Nat.factorial i)) - q ^ 30 * (31 / (Nat.factorial 30 * 30)) ≤ exp q ∧
      exp q ≤ (∑ i ∈ Finset.range 30, q ^ i / (Nat.factorial i)) + q ^ 30 * (31 / (Nat.factorial 30 * 30)) := by
  have h := Real.exp_bound (x := q) (by rw [abs_of_nonneg hq0]; exact hq1) (n := 30) (by norm_num)
  rw [abs_le, abs_of_nonneg hq0] at h
  constructor <;> push_cast at h ⊢ <;> linarith [h.1, h.2]

/-! ## Numerical certificate -/

theorem exp_q_bounds {q lo hi : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hlo : lo ≤ (∑ i ∈ Finset.range 30, q ^ i / (Nat.factorial i)) - q ^ 30 * (31 / (Nat.factorial 30 * 30)))
    (hhi : (∑ i ∈ Finset.range 30, q ^ i / (Nat.factorial i)) + q ^ 30 * (31 / (Nat.factorial 30 * 30)) ≤ hi) :
    lo ≤ exp q ∧ exp q ≤ hi := by
  have := exp_enclose hq0 hq1
  exact ⟨hlo.trans this.1, this.2.trans hhi⟩

theorem exp_sa : (2.455616849870919834792738394409:ℝ) ≤ exp ((sa:ℝ) / 4) ∧ exp ((sa:ℝ) / 4) ≤ (2.455616849870919834792738394410:ℝ) := by
  apply exp_q_bounds (by norm_num [sa]) (by norm_num [sa]) <;>
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num [sa]

theorem exp_sb : (2.455616849870981225213985168173:ℝ) ≤ exp ((sb:ℝ) / 4) ∧ exp ((sb:ℝ) / 4) ≤ (2.455616849870981225213985168174:ℝ) := by
  apply exp_q_bounds (by norm_num [sb]) (by norm_num [sb]) <;>
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num [sb]

theorem exp_four (s : ℝ) : exp s = exp (s / 4) ^ 4 := by
  rw [← exp_nat_mul]; congr 1; push_cast; ring

theorem L1_sa_lt : L1 sa < 1 / 4 := by
  have h := exp_sa.1
  have hE : (2.455616849870919834792738394409:ℝ) ^ 4 ≤ exp (sa:ℝ) := by
    rw [exp_four]; exact pow_le_pow_left₀ (by norm_num) h 4
  unfold L1 g
  have hpos : (0:ℝ) < (2.455616849870919834792738394409:ℝ) ^ 4 - 1 := by norm_num
  have : 1 / (exp (sa:ℝ) - 1) ≤ 1 / ((2.455616849870919834792738394409:ℝ) ^ 4 - 1) :=
    one_div_le_one_div_of_le hpos (by linarith)
  have : (1:ℝ) / 2 + 1 / ((2.455616849870919834792738394409:ℝ) ^ 4 - 1) - 1 / (sa:ℝ) < 1 / 4 := by norm_num [sa]
  linarith

theorem L1_sb_gt : 1 / 4 < L1 sb := by
  have h := exp_sb.2
  have hE : exp (sb:ℝ) ≤ (2.455616849870981225213985168174:ℝ) ^ 4 := by
    rw [exp_four]; exact pow_le_pow_left₀ (exp_pos _).le h 4
  have hE1 : 0 < exp (sb:ℝ) - 1 := expm1_pos (by norm_num [sb])
  unfold L1 g
  have : 1 / ((2.455616849870981225213985168174:ℝ) ^ 4 - 1) ≤ 1 / (exp (sb:ℝ) - 1) :=
    one_div_le_one_div_of_le hE1 (by linarith)
  have : (1:ℝ) / 4 < 1 / 2 + 1 / ((2.455616849870981225213985168174:ℝ) ^ 4 - 1) - 1 / (sb:ℝ) := by norm_num [sb]
  linarith

/-- Any `s > 0` with `Λ'(s) = 1/4` lies in `[sa, sb]`. -/
theorem root_mem {s : ℝ} (hs : 0 < s) (h : L1 s = 1 / 4) : (sa:ℝ) ≤ s ∧ s ≤ sb := by
  have hsa : (0:ℝ) < sa := by norm_num [sa]
  have hsb : (0:ℝ) < sb := by norm_num [sb]
  constructor
  · by_contra hc; push_neg at hc
    have := L1_strictMonoOn hs hsa hc
    linarith [L1_sa_lt]
  · by_contra hc; push_neg at hc
    have := L1_strictMonoOn hsb hs hc
    linarith [L1_sb_gt]


theorem iv_mul {x y a b c d : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (h1 : a ≤ x) (h2 : x ≤ b) (h3 : c ≤ y)
    (h4 : y ≤ d) : a * c ≤ x * y ∧ x * y ≤ b * d :=
  ⟨mul_le_mul h1 h3 hc (le_trans ha h1),
    mul_le_mul h2 h4 (le_trans hc h3) (le_trans ha (h1.trans h2))⟩

set_option maxHeartbeats 8000000 in
/-- Interval arithmetic for `η` on `[sa, sb]`. -/
theorem eta_bounds {s : ℝ} (h1 : (sa:ℝ) ≤ s) (h2 : s ≤ sb) :
    -0.1843915 < etaS s ∧ etaS s < -0.1843905 := by
  have hs : 0 < s := lt_of_lt_of_le (by norm_num [sa]) h1
  have hea : exp (sa:ℝ) ≤ exp s := exp_le_exp.mpr h1
  have heb : exp s ≤ exp (sb:ℝ) := exp_le_exp.mpr h2
  have hEa : (2.455616849870919834792738394409:ℝ) ^ 4 ≤ exp (sa:ℝ) := by
    rw [exp_four]; exact pow_le_pow_left₀ (by norm_num) exp_sa.1 4
  have hEb : exp (sb:ℝ) ≤ (2.455616849870981225213985168174:ℝ) ^ 4 := by
    rw [exp_four]; exact pow_le_pow_left₀ (exp_pos _).le exp_sb.2 4
  have hE1 : 0 < exp s - 1 := expm1_pos hs
  have hg1 : (0.028279301280235379218275142233:ℝ) ≤ g s := by
    unfold g
    calc (0.028279301280235379218275142233:ℝ) ≤ 1 / ((2.455616849870981225213985168174:ℝ) ^ 4 - 1) := by norm_num
      _ ≤ 1 / (exp s - 1) := one_div_le_one_div_of_le hE1 (by linarith)
  have hg2 : g s ≤ (0.028279301280238287120291255758:ℝ) := by
    unfold g
    calc 1 / (exp s - 1) ≤ 1 / ((2.455616849870919834792738394409:ℝ) ^ 4 - 1) :=
          one_div_le_one_div_of_le (by norm_num) (by linarith)
      _ ≤ (0.028279301280238287120291255758:ℝ) := by norm_num
  have hw1 : (0.278279301280231804531133389268:ℝ) ≤ 1 / s := by
    calc (0.278279301280231804531133389268:ℝ) ≤ 1 / (sb:ℝ) := by norm_num [sb]
      _ ≤ 1 / s := one_div_le_one_div_of_le hs h2
  have hw2 : 1 / s ≤ (0.278279301280239548468085490887:ℝ) := by
    calc 1 / s ≤ 1 / (sa:ℝ) := one_div_le_one_div_of_le (by norm_num [sa]) h1
      _ ≤ (0.278279301280239548468085490887:ℝ) := by norm_num [sa]
  have hL2 : L2 s = (1 / s) * (1 / s) - (g s + g s * g s) := by unfold L2 h; ring
  have hL3 : L3 s = (g s + g s * g s) * (1 + 2 * g s) - 2 * ((1 / s) * (1 / s) * (1 / s)) := by
    unfold L3 h; field_simp
  have hL4 : L4 s = 6 * ((1 / s) * (1 / s) * ((1 / s) * (1 / s)))
      - (g s + g s * g s) * ((1 + 2 * g s) * (1 + 2 * g s) + 2 * (g s + g s * g s)) := by
    unfold L4 h; field_simp
  generalize g s = G at hg1 hg2 hL2 hL3 hL4
  generalize 1 / s = W at hw1 hw2 hL2 hL3 hL4
  have hG0 : (0:ℝ) ≤ (0.028279301280235379218275142233:ℝ) := by norm_num
  have hW0 : (0:ℝ) ≤ (0.278279301280231804531133389268:ℝ) := by norm_num
  obtain ⟨gg1, gg2⟩ := iv_mul hG0 hG0 hg1 hg2 hg1 hg2
  have hH1 : (0.029079020161133701576332504894:ℝ) ≤ G + G * G := by
    have : (0.029079020161133701576332504894:ℝ) ≤ (0.028279301280235379218275142233:ℝ) + (0.028279301280235379218275142233:ℝ) * (0.028279301280235379218275142233:ℝ) := by norm_num
    linarith
  have hH2 : G + G * G ≤ (0.029079020161136773945223032585:ℝ) := by
    have : (0.028279301280238287120291255758:ℝ) + (0.028279301280238287120291255758:ℝ) * (0.028279301280238287120291255758:ℝ) ≤ (0.029079020161136773945223032585:ℝ) := by norm_num
    linarith
  obtain ⟨ww1, ww2⟩ := iv_mul hW0 hW0 hw1 hw2 hw1 hw2
  have hA1 : (0.048360349359877248499091696292:ℝ) ≤ L2 s := by
    rw [hL2]; have : (0.048360349359877248499091696292:ℝ) ≤ (0.278279301280231804531133389268:ℝ) * (0.278279301280231804531133389268:ℝ) - (0.029079020161136773945223032585:ℝ) := by norm_num
    linarith
  have hA2 : L2 s ≤ (0.048360349359884630822710602057:ℝ) := by
    rw [hL2]; have : (0.278279301280239548468085490887:ℝ) * (0.278279301280239548468085490887:ℝ) - (0.029079020161133701576332504894:ℝ) ≤ (0.048360349359884630822710602057:ℝ) := by norm_num
    linarith
  have hU1 : 1 + 2 * (0.028279301280235379218275142233:ℝ) ≤ 1 + 2 * G := by linarith
  have hU2 : 1 + 2 * G ≤ 1 + 2 * (0.028279301280238287120291255758:ℝ) := by linarith
  have hH0 : (0:ℝ) ≤ (0.029079020161133701576332504894:ℝ) := by norm_num
  have hU0 : (0:ℝ) ≤ 1 + 2 * (0.028279301280235379218275142233:ℝ) := by norm_num
  obtain ⟨pp1, pp2⟩ := iv_mul hH0 hU0 hH1 hH2 hU1 hU2
  have hWW0 : (0:ℝ) ≤ (0.278279301280231804531133389268:ℝ) * (0.278279301280231804531133389268:ℝ) := by norm_num
  obtain ⟨w31, w32⟩ := iv_mul hWW0 hW0 ww1 ww2 hw1 hw2
  have hB1 : (-0.012375858378507341635952126234:ℝ) ≤ L3 s := by
    rw [hL3]
    have : (-0.012375858378507341635952126234:ℝ) ≤ (0.029079020161133701576332504894:ℝ) * (1 + 2 * (0.028279301280235379218275142233:ℝ)) - 2 * ((0.278279301280239548468085490887:ℝ) * (0.278279301280239548468085490887:ℝ) * (0.278279301280239548468085490887:ℝ)) := by norm_num
    linarith
  have hB2 : L3 s ≤ (-0.012375858378500328266716806186:ℝ) := by
    rw [hL3]
    have : (0.029079020161136773945223032585:ℝ) * (1 + 2 * (0.028279301280238287120291255758:ℝ)) - 2 * ((0.278279301280231804531133389268:ℝ) * (0.278279301280231804531133389268:ℝ) * (0.278279301280231804531133389268:ℝ)) ≤ (-0.012375858378500328266716806186:ℝ) := by norm_num
    linarith
  obtain ⟨uu1, uu2⟩ := iv_mul hU0 hU0 hU1 hU2 hU1 hU2
  have hV1 : (1 + 2 * (0.028279301280235379218275142233:ℝ)) * (1 + 2 * (0.028279301280235379218275142233:ℝ)) + 2 * (0.029079020161133701576332504894:ℝ) ≤ (1 + 2 * G) * (1 + 2 * G) + 2 * (G + G * G) := by linarith
  have hV2 : (1 + 2 * G) * (1 + 2 * G) + 2 * (G + G * G) ≤ (1 + 2 * (0.028279301280238287120291255758:ℝ)) * (1 + 2 * (0.028279301280238287120291255758:ℝ)) + 2 * (0.029079020161136773945223032585:ℝ) := by linarith
  have hV0 : (0:ℝ) ≤ (1 + 2 * (0.028279301280235379218275142233:ℝ)) * (1 + 2 * (0.028279301280235379218275142233:ℝ)) + 2 * (0.029079020161133701576332504894:ℝ) := by norm_num
  obtain ⟨qq1, qq2⟩ := iv_mul hH0 hV0 hH1 hH2 hV1 hV2
  obtain ⟨w41, w42⟩ := iv_mul hWW0 hWW0 ww1 ww2 ww1 ww2
  have hC1 : (0.001828579068545365519131686683:ℝ) ≤ L4 s := by
    rw [hL4]
    have : (0.001828579068545365519131686683:ℝ) ≤ 6 * ((0.278279301280231804531133389268:ℝ) * (0.278279301280231804531133389268:ℝ) * ((0.278279301280231804531133389268:ℝ) * (0.278279301280231804531133389268:ℝ))) - (0.029079020161136773945223032585:ℝ) * ((1 + 2 * (0.028279301280238287120291255758:ℝ)) * (1 + 2 * (0.028279301280238287120291255758:ℝ)) + 2 * (0.029079020161136773945223032585:ℝ)) := by norm_num
    linarith
  have hC2 : L4 s ≤ (0.001828579068553515107867092215:ℝ) := by
    rw [hL4]
    have : 6 * ((0.278279301280239548468085490887:ℝ) * (0.278279301280239548468085490887:ℝ) * ((0.278279301280239548468085490887:ℝ) * (0.278279301280239548468085490887:ℝ))) - (0.029079020161133701576332504894:ℝ) * ((1 + 2 * (0.028279301280235379218275142233:ℝ)) * (1 + 2 * (0.028279301280235379218275142233:ℝ)) + 2 * (0.029079020161133701576332504894:ℝ)) ≤ (0.001828579068553515107867092215:ℝ) := by norm_num
    linarith
  have hA0 : (0:ℝ) < (0.048360349359877248499091696292:ℝ) := by norm_num
  have hAp : 0 < L2 s := lt_of_lt_of_le hA0 hA1
  obtain ⟨a21, a22⟩ := iv_mul hA0.le hA0.le hA1 hA2 hA1 hA2
  have hAA0 : (0:ℝ) ≤ (0.048360349359877248499091696292:ℝ) * (0.048360349359877248499091696292:ℝ) := by norm_num
  obtain ⟨a31, a32⟩ := iv_mul hAA0 hA0.le a21 a22 hA1 hA2
  have hX1 : (0.781870603509506669621325661298:ℝ) ≤ L4 s / (L2 s * L2 s) := by
    calc (0.781870603509506669621325661298:ℝ) ≤ (0.001828579068545365519131686683:ℝ) / ((0.048360349359884630822710602057:ℝ) * (0.048360349359884630822710602057:ℝ)) := by norm_num
      _ ≤ L4 s / (L2 s * L2 s) := div_le_div₀ (le_trans (by norm_num) hC1) hC1 (by positivity) a22
  have hX2 : L4 s / (L2 s * L2 s) ≤ (0.781870603513230009780160408176:ℝ) := by
    calc L4 s / (L2 s * L2 s) ≤ (0.001828579068553515107867092215:ℝ) / ((0.048360349359877248499091696292:ℝ) * (0.048360349359877248499091696292:ℝ)) :=
          div_le_div₀ (by norm_num) hC2 (by norm_num) a21
      _ ≤ (0.781870603513230009780160408176:ℝ) := by norm_num
  have hn1 : -(-0.012375858378500328266716806186:ℝ) ≤ -L3 s := by linarith
  have hn2 : -L3 s ≤ -(-0.012375858378507341635952126234:ℝ) := by linarith
  have hn0 : (0:ℝ) ≤ -(-0.012375858378500328266716806186:ℝ) := by norm_num
  obtain ⟨s1, s2⟩ := iv_mul hn0 hn0 hn1 hn2 hn1 hn2
  have hsq : L3 s * L3 s = (-L3 s) * (-L3 s) := by ring
  have hY1 : (1.354198639352837320798549059428:ℝ) ≤ L3 s * L3 s / (L2 s * L2 s * L2 s) := by
    calc (1.354198639352837320798549059428:ℝ) ≤ (-(-0.012375858378500328266716806186:ℝ)) * (-(-0.012375858378500328266716806186:ℝ)) / ((0.048360349359884630822710602057:ℝ) * (0.048360349359884630822710602057:ℝ) * (0.048360349359884630822710602057:ℝ)) := by norm_num
      _ ≤ L3 s * L3 s / (L2 s * L2 s * L2 s) := by
        rw [hsq]; exact div_le_div₀ (by positivity) s1 (by positivity) a32
  have hY2 : L3 s * L3 s / (L2 s * L2 s * L2 s) ≤ (1.354198639354992328070951461303:ℝ) := by
    calc L3 s * L3 s / (L2 s * L2 s * L2 s) ≤ (-(-0.012375858378507341635952126234:ℝ)) * (-(-0.012375858378507341635952126234:ℝ)) / ((0.048360349359877248499091696292:ℝ) * (0.048360349359877248499091696292:ℝ) * (0.048360349359877248499091696292:ℝ)) := by
          rw [hsq]; exact div_le_div₀ (by norm_num) s2 (by norm_num) a31
      _ ≤ (1.354198639354992328070951461303:ℝ) := by norm_num
  have hE : etaS s = (L4 s / (L2 s * L2 s) - 5 / 3 * (L3 s * L3 s / (L2 s * L2 s * L2 s))) / 8 := by
    unfold etaS; ring
  rw [hE]
  constructor
  · have : (-0.1843915:ℝ) < ((0.781870603509506669621325661298:ℝ) - 5 / 3 * (1.354198639354992328070951461303:ℝ)) / 8 := by norm_num
    linarith
  · have : ((0.781870603513230009780160408176:ℝ) - 5 / 3 * (1.354198639352837320798549059428:ℝ)) / 8 < (-0.1843905:ℝ) := by norm_num
    linarith

/-- **`η(1/4) ≈ -0.184391`**: for the (unique) `s > 0` with `Λ'(s) = 1/4`,
`|η(s) + 0.184391| < 5·10^{-7}`. -/
theorem eta_quarter {s : ℝ} (hs : 0 < s) (h : L1 s = 1 / 4) : |etaS s - (-0.184391)| < 5 / 10 ^ 7 := by
  obtain ⟨h1, h2⟩ := root_mem hs h
  obtain ⟨e1, e2⟩ := eta_bounds h1 h2
  rw [abs_lt]; constructor <;> linarith

/-- Existence of `s(1/4)`: `Λ'` takes the value `1/4` on `(0,∞)`. -/
theorem exists_root : ∃ s, 0 < s ∧ L1 s = 1 / 4 := by
  have hc : ContinuousOn L1 (Set.Icc (sa:ℝ) sb) := by
    intro x hx
    have : 0 < x := lt_of_lt_of_le (by norm_num [sa]) hx.1
    exact (hasDerivAt_L1 this).continuousAt.continuousWithinAt
  obtain ⟨s, hs, hv⟩ := intermediate_value_Icc (by norm_num [sa, sb]) hc ⟨L1_sa_lt.le, L1_sb_gt.le⟩
  exact ⟨s, lt_of_lt_of_le (by norm_num [sa]) hs.1, hv⟩

end EulerianBridge.EtaQuarter
