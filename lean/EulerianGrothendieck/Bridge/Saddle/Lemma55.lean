import Bridge.Saddle.Main2

/-!
# Lemma 5.5 of manuscript V173 (saddlepoint estimate with two derivatives)

`lemma_5_5`: for every `b ∈ (0, 1/2)` there are `M₀ ∈ ℕ` and `C` such that for all `M ≥ M₀`
and all `x ∈ [-b, b]`, the function
`E_M = log g_M + MI - ½ log(M/(2πv)) - η/M`
is twice differentiable at `x` (with derivatives `E1 M x`, `E2 M x`) and
`|E_M(x)| ≤ C/(M√M)`, `|E_M'(x)| ≤ C/(M√M)`, `|E_M''(x)| ≤ C/(M√M)`  — eq. (68).
-/

open MeasureTheory Set Complex Filter Topology Metric
open scoped Nat

namespace EulerianBridge.Saddle

theorem Yr_close {s : ℝ} {M r : ℕ} {e Cr B : ℝ} (heM : e = epsM M) (he0 : 0 < e)
    (h : ‖Ir s M e r - (Real.sqrt (2 * Real.pi / κ 2 s) : ℂ) * Nexp s e r‖ ≤ Cr * e ^ 5)
    (hB : cN s * |Cr| ≤ B) : ‖Yr s M r - Nexp s e r‖ ≤ B * e ^ 5 := by
  have hcc : (cN s : ℂ) * (Real.sqrt (2 * Real.pi / κ 2 s) : ℂ) = 1 := by
    exact_mod_cast cN_mul_sqrt s
  have : Yr s M r - Nexp s e r =
      (cN s : ℂ) * (Ir s M e r - (Real.sqrt (2 * Real.pi / κ 2 s) : ℂ) * Nexp s e r) := by
    unfold Yr; rw [← heM, mul_sub, ← mul_assoc, hcc, one_mul]
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cN_pos s)]
  have hc := cN_pos s
  have h5 : 0 ≤ e ^ 5 := by positivity
  calc cN s * ‖_‖ ≤ cN s * (Cr * e ^ 5) := mul_le_mul_of_nonneg_left h hc.le
    _ ≤ cN s * (|Cr| * e ^ 5) := by gcongr; exact le_abs_self _
    _ = (cN s * |Cr|) * e ^ 5 := by ring
    _ ≤ B * e ^ 5 := by gcongr

/-- All hypotheses of `final_bounds` hold uniformly on `|s| ≤ σ` for `M ≥ M₀`. -/
theorem uniform_data {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ K Cρ : ℝ, 1 ≤ K ∧ 0 ≤ Cρ ∧ ∀ M : ℕ, 4 ≤ M → (4 * (Cρ + 2 * K) ≤ M) → ∀ s, |s| ≤ σ →
      FinalData (epsM M) K Cρ (Yr s M 0) (Yr s M 1) (Yr s M 2) (etaS s) (G04 s) (G11 s) (G13 s)
        (G20 s) (G22 s) (G24 s) (L1 s) (L2 s) (eta1 s) (eta2 s) := by
  obtain ⟨C0, hC0⟩ := Ir_expansion hσ (r := 0) (by norm_num)
  obtain ⟨C1, hC1⟩ := Ir_expansion hσ (r := 1) (by norm_num)
  obtain ⟨C2, hC2⟩ := Ir_expansion hσ (r := 2) (by norm_num)
  obtain ⟨K, hK1, hK⟩ := exists_coeff_bound σ
  set Cρ : ℝ := (|C0| + |C1| + |C2|) * (Real.sqrt K / Real.sqrt (2 * Real.pi))
  have hCρ : 0 ≤ Cρ := by positivity
  refine ⟨K, Cρ, hK1, hCρ, fun M hM hMK s hs => ?_⟩
  obtain ⟨b02, b04, b11, b13, b20, b22, b24, bL2, bη1, bη2, bk2⟩ := hK s hs
  have hM1 : 1 ≤ M := by omega
  have he0 : 0 < epsM M := epsM_pos hM1
  have hMe : (M:ℝ) * epsM M ^ 2 = 1 := epsM_sq hM1
  have hM4 : (4:ℝ) ≤ M := by exact_mod_cast hM
  have he1 : epsM M ≤ 1 := by
    by_contra h; push_neg at h
    have : (1:ℝ) < epsM M ^ 2 := by nlinarith
    nlinarith
  have hcN : cN s ≤ Real.sqrt K / Real.sqrt (2 * Real.pi) := by
    unfold cN; gcongr
  have hcn0 := (cN_pos s).le
  have hB : ∀ Cr : ℝ, |Cr| ≤ |C0| + |C1| + |C2| → cN s * |Cr| ≤ Cρ := by
    intro Cr h
    calc cN s * |Cr| ≤ (Real.sqrt K / Real.sqrt (2 * Real.pi)) * (|C0| + |C1| + |C2|) :=
          mul_le_mul hcN h (abs_nonneg _) (by positivity)
      _ = Cρ := by ring
  have y0 := Yr_close rfl he0 (hC0 s hs M hM (epsM M) he0 hMe) (hB C0 (by
    have := abs_nonneg C1; have := abs_nonneg C2; linarith))
  have y1 := Yr_close rfl he0 (hC1 s hs M hM (epsM M) he0 hMe) (hB C1 (by
    have := abs_nonneg C0; have := abs_nonneg C2; linarith))
  have y2 := Yr_close rfl he0 (hC2 s hs M hM (epsM M) he0 hMe) (hB C2 (by
    have := abs_nonneg C0; have := abs_nonneg C1; linarith))
  rw [Nexp_zero, id_G02] at y0
  rw [Nexp_one] at y1
  rw [Nexp_two] at y2
  have hη : ‖((etaS s : ℝ) : ℂ)‖ ≤ K := by rw [← id_G02]; exact b02
  refine ⟨he0, he1, hK1, hCρ, hη, b04, b11, b13, b20, b22, b24, bL2, bη1, bη2, y0, y1, y2, ?_,
    id_G11 s, id_G13 s, ?_, ?_⟩
  · -- smallness of `Y₀ - 1`
    set e := epsM M
    have hK0 : 0 ≤ K := by linarith
    have he2 : e ^ 2 ≤ 1 / (4 * (Cρ + 2 * K)) := by
      have hpos : 0 < 4 * (Cρ + 2 * K) := by positivity
      rw [le_div_iff₀ hpos]
      calc e ^ 2 * (4 * (Cρ + 2 * K)) ≤ e ^ 2 * M := by gcongr
        _ = 1 := by rw [mul_comm]; exact hMe
    have e52 : e ^ 5 ≤ e ^ 2 := pow_le_pow_of_le_one he0.le he1 (by norm_num)
    have e42 : e ^ 4 ≤ e ^ 2 := pow_le_pow_of_le_one he0.le he1 (by norm_num)
    have hsplit : Yr s M 0 - 1 = (Yr s M 0 - (1 + (e:ℂ) ^ 2 * (etaS s : ℂ) + (e:ℂ) ^ 4 * G04 s)) +
        ((e:ℂ) ^ 2 * (etaS s : ℂ) + (e:ℂ) ^ 4 * G04 s) := by ring
    rw [hsplit]
    have t1 := nmul (le_of_eq (npow he0.le 2)) hη
    have t2 := nmul (le_of_eq (npow he0.le 4)) b04
    have hsum := (norm_add_le _ _).trans (add_le_add y0 ((norm_add_le _ _).trans (add_le_add t1 t2)))
    have : Cρ * e ^ 5 + (e ^ 2 * K + e ^ 4 * K) ≤ e ^ 2 * (Cρ + 2 * K) := by nlinarith
    have : e ^ 2 * (Cρ + 2 * K) ≤ 1 / 4 := by
      have hpos : 0 < Cρ + 2 * K := by positivity
      calc e ^ 2 * (Cρ + 2 * K) ≤ 1 / (4 * (Cρ + 2 * K)) * (Cρ + 2 * K) := by gcongr
        _ = 1 / 4 := by field_simp
    linarith
  · have := id_G22 s; exact this
  · have := id_G24 s; exact this

/-- **Lemma 5.5** (eq. (68)). -/
theorem lemma_5_5 {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    ∃ M0 : ℕ, ∃ C : ℝ, ∀ M : ℕ, M0 ≤ M → ∀ x ∈ Icc (-b) b,
      0 < w M (M * x) ∧ HasDerivAt (EM M) (E1 M x) x ∧ HasDerivAt (deriv (EM M)) (E2 M x) x ∧
      |EM M x| ≤ C / (M * Real.sqrt M) ∧ |deriv (EM M) x| ≤ C / (M * Real.sqrt M) ∧
      |deriv (deriv (EM M)) x| ≤ C / (M * Real.sqrt M) := by
  set b' := (b + 1 / 2) / 2
  have hbb' : b < b' := by simp only [b']; linarith
  have hb' : b' < 1 / 2 := by simp only [b']; linarith
  set σ := UL.Ip b'
  have hσ : 0 ≤ σ := UL.Ip_nonneg (by linarith) hb'
  obtain ⟨K, Cρ, hK1, hCρ, hD⟩ := uniform_data hσ
  have hK0 : 0 ≤ K := by linarith
  set M0 : ℕ := max 4 ⌈4 * (Cρ + 2 * K)⌉₊
  set Ca := 2 * (Cρ + 2 * K) ^ 2 + (K + Cρ)
  set Cb := 2 * (3 * K ^ 2 + Cρ + 2 * K * Cρ)
  set Cc := 4 * (21 * K ^ 3 + Cρ * (10 * K + 2 * Cρ + 6 * K ^ 2 + K * Cρ) + 2 * K * Cρ * (6 * K + Cρ))
  have hCa : 0 ≤ Ca := by positivity
  have hCb : 0 ≤ Cb := by positivity
  have hCc : 0 ≤ Cc := by positivity
  refine ⟨M0, Ca + Cb + Cc, fun M hM x hx => ?_⟩
  have hM4 : 4 ≤ M := le_trans (le_max_left _ _) hM
  have hMK : 4 * (Cρ + 2 * K) ≤ M := by
    have h1 : (⌈4 * (Cρ + 2 * K)⌉₊ : ℝ) ≤ M := by exact_mod_cast le_trans (le_max_right _ _) hM
    exact (Nat.le_ceil _).trans h1
  have hM1 : 1 ≤ M := by omega
  set e := epsM M
  have he0 : 0 < e := epsM_pos hM1
  have hMe : (M:ℝ) * e ^ 2 = 1 := epsM_sq hM1
  have he3 : e ^ 3 = 1 / (M * Real.sqrt M) := epsM_cube hM1
  -- positivity of `w_M(My)` on `|y| ≤ b'`
  have hpos : ∀ y, |y| ≤ b' → 0 < w M (M * y) ∧ ∃ y0 : ℝ, (y0 : ℂ) = Yr (UL.Ip y) M 0 ∧ 0 < y0 ∧
      gM M y = y0 * (Real.sqrt M / (Real.sqrt (2 * Real.pi) * Real.sqrt (κ 2 (UL.Ip y)))) *
        Real.exp (M * (Lr (UL.Ip y) - UL.Ip y * y)) := by
    intro y hy
    have hyI : y ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
      rw [abs_le] at hy; exact ⟨by linarith, by linarith⟩
    have hs := abs_Ip_le hb' hy
    have D := hD M hM4 hMK (UL.Ip y) hs
    have hY0n := D.Y0_ne
    have hY0 : Yr (UL.Ip y) M 0 ≠ 0 := by intro h; rw [h, norm_zero] at hY0n; linarith
    obtain ⟨y0, hy0, hg, -, -⟩ := pt_identities hM4 hyI hY0
    have hy0pos : 0 < y0 := by
      have h := D.hsmall
      rw [← hy0] at h
      have : ‖((y0 - 1 : ℝ) : ℂ)‖ ≤ 1 / 2 := by push_cast; exact h
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith [neg_abs_le (y0 - 1)]
    have hgpos : 0 < gM M y := by
      rw [hg]
      have := Real.sqrt_pos.mpr (show (0:ℝ) < M by exact_mod_cast (show 0 < M by omega))
      have := Real.sqrt_pos.mpr (show (0:ℝ) < 2 * Real.pi by positivity)
      have := Real.sqrt_pos.mpr (κ_two_pos (UL.Ip y))
      positivity
    refine ⟨?_, y0, hy0, hy0pos, hg⟩
    unfold gM at hgpos
    have : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    exact pos_of_mul_pos_right hgpos this.le
  have hxb : |x| ≤ b := abs_le.mpr hx
  have hxb' : |x| ≤ b' := by linarith
  have hxI : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    rw [abs_le] at hxb'; exact ⟨by linarith, by linarith⟩
  -- derivatives
  have hder : ∀ y, |y| < b' → HasDerivAt (EM M) (E1 M y) y := by
    intro y hy
    have hyI : y ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
      rw [abs_lt] at hy; exact ⟨by linarith, by linarith⟩
    exact hasDerivAt_EM hM4 hyI (hpos y hy.le).1
  have hxlt : |x| < b' := by linarith
  have h1 := hder x hxlt
  have hev : deriv (EM M) =ᶠ[𝓝 x] E1 M := by
    have hopen : IsOpen {y : ℝ | |y| < b'} := isOpen_lt continuous_abs continuous_const
    filter_upwards [hopen.mem_nhds hxlt] with y hy
    exact (hder y hy).deriv
  have h2 : HasDerivAt (deriv (EM M)) (E2 M x) x :=
    (hasDerivAt_E1 hM4 hxI (hpos x hxb').1).congr_of_eventuallyEq hev
  refine ⟨(hpos x hxb').1, h1, h2, ?_, ?_, ?_⟩
  · -- |E_M|
    obtain ⟨-, y0, hy0, hy0pos, hg⟩ := hpos x hxb'
    rw [EM_eq hM1 hy0pos hg]
    have D := hD M hM4 hMK (UL.Ip x) (abs_Ip_le hb' hxb')
    have ha := final_a D
    have hsm := D.hsmall
    rw [← hy0] at ha hsm
    have hM' : etaS (UL.Ip x) / M = e ^ 2 * etaS (UL.Ip x) := by
      have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
      rw [div_eq_iff hMpos.ne']
      calc etaS (UL.Ip x) = etaS (UL.Ip x) * ((M:ℝ) * e ^ 2) := by rw [hMe, mul_one]
        _ = e ^ 2 * etaS (UL.Ip x) * M := by ring
    rw [hM']
    have ha' : |y0 - 1 - e ^ 2 * etaS (UL.Ip x)| ≤ (K + Cρ) * e ^ 4 := by
      have : ‖((y0 - 1 - e ^ 2 * etaS (UL.Ip x) : ℝ) : ℂ)‖ ≤ (K + Cρ) * e ^ 4 := by push_cast; exact ha
      rwa [Complex.norm_real, Real.norm_eq_abs] at this
    have hsm' : |y0 - 1| ≤ e ^ 2 * (Cρ + 2 * K) := by
      -- from the proof of smallness
      have D0 := D.hY0
      rw [← hy0] at D0
      have t1 := nmul (le_of_eq (npow he0.le 2)) D.hη
      have t2 := nmul (le_of_eq (npow he0.le 4)) D.hp
      have hsplit : ((y0 - 1 : ℝ) : ℂ) = ((y0 : ℂ) - (1 + (e:ℂ) ^ 2 * (etaS (UL.Ip x) : ℂ) +
          (e:ℂ) ^ 4 * G04 (UL.Ip x))) + ((e:ℂ) ^ 2 * (etaS (UL.Ip x) : ℂ) + (e:ℂ) ^ 4 * G04 (UL.Ip x)) := by
        push_cast; ring
      have := (norm_add_le _ _).trans (add_le_add D0 ((norm_add_le _ _).trans (add_le_add t1 t2)))
      rw [← hsplit, Complex.norm_real, Real.norm_eq_abs] at this
      have he1 : e ≤ 1 := D.he1
      have e52 : e ^ 5 ≤ e ^ 2 := pow_le_pow_of_le_one he0.le he1 (by norm_num)
      have e42 : e ^ 4 ≤ e ^ 2 := pow_le_pow_of_le_one he0.le he1 (by norm_num)
      nlinarith
    have hsm'' : |y0 - 1| ≤ 1 / 2 := by
      have : ‖((y0 - 1 : ℝ) : ℂ)‖ ≤ 1 / 2 := by push_cast; exact hsm
      rwa [Complex.norm_real, Real.norm_eq_abs] at this
    have hlog := log_bound hsm''
    have he1 : e ≤ 1 := D.he1
    have e43 : e ^ 4 ≤ e ^ 3 := pow_le_pow_of_le_one he0.le he1 (by norm_num)
    have hsq : (y0 - 1) ^ 2 ≤ (e ^ 2 * (Cρ + 2 * K)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hsm' 2
    calc |Real.log y0 - e ^ 2 * etaS (UL.Ip x)|
        = |(Real.log y0 - (y0 - 1)) + (y0 - 1 - e ^ 2 * etaS (UL.Ip x))| := by ring_nf
      _ ≤ |Real.log y0 - (y0 - 1)| + |y0 - 1 - e ^ 2 * etaS (UL.Ip x)| := abs_add_le _ _
      _ ≤ 2 * (e ^ 2 * (Cρ + 2 * K)) ^ 2 + (K + Cρ) * e ^ 4 := by nlinarith
      _ = Ca * e ^ 4 := by simp only [Ca]; ring
      _ ≤ Ca * e ^ 3 := by gcongr
      _ ≤ (Ca + Cb + Cc) * e ^ 3 := by gcongr; linarith
      _ = (Ca + Cb + Cc) / (M * Real.sqrt M) := by rw [he3]; ring
  · -- |E_M'|
    rw [h1.deriv]
    have hY0 : Yr (UL.Ip x) M 0 ≠ 0 := by
      have D := hD M hM4 hMK (UL.Ip x) (abs_Ip_le hb' hxb')
      have := D.Y0_ne; intro h; rw [h, norm_zero] at this; linarith
    obtain ⟨-, -, -, hE1, -⟩ := pt_identities hM4 hxI hY0
    have D := hD M hM4 hMK (UL.Ip x) (abs_Ip_le hb' hxb')
    have hb := final_b D
    rw [← hE1, Complex.norm_real, Real.norm_eq_abs] at hb
    calc |E1 M x| ≤ Cb * e ^ 3 := hb
      _ ≤ (Ca + Cb + Cc) * e ^ 3 := by gcongr; linarith
      _ = (Ca + Cb + Cc) / (M * Real.sqrt M) := by rw [he3]; ring
  · -- |E_M''|
    rw [h2.deriv]
    have hY0 : Yr (UL.Ip x) M 0 ≠ 0 := by
      have D := hD M hM4 hMK (UL.Ip x) (abs_Ip_le hb' hxb')
      have := D.Y0_ne; intro h; rw [h, norm_zero] at this; linarith
    obtain ⟨-, -, -, -, hE2⟩ := pt_identities hM4 hxI hY0
    have D := hD M hM4 hMK (UL.Ip x) (abs_Ip_le hb' hxb')
    have hc := final_c D
    rw [← hE2, Complex.norm_real, Real.norm_eq_abs] at hc
    calc |E2 M x| ≤ Cc * e ^ 3 := hc
      _ ≤ (Ca + Cb + Cc) * e ^ 3 := by gcongr; linarith
      _ = (Ca + Cb + Cc) / (M * Real.sqrt M) := by rw [he3]; ring

end EulerianBridge.Saddle
