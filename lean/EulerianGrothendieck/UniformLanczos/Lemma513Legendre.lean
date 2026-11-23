import Mathlib

/-! # Manuscript 12, Lemma 5.13 (localisation): the weighted endpoint inequality (159)

Second paragraph of the proof of Lemma 5.13. For a nonnegative continuous `P = |p|²`
satisfying the endpoint inequality `P(x) ≤ K/(x-s) ∫_s^x P` on `[r, b]` (for a polynomial
of degree `m`, `K = (m+1)²`: the classical Christoffel bound from the orthonormal Legendre
basis, a published result cited), and a weight `g` that is nonincreasing on `[s, b]`,
nonnegative at `b` and differentiable there with integrable derivative `g' ≤ 0` on `[r, b]`,

  `∫_r^b P(x) (-g'(x)) dx ≤ K/(r-s) ∫_s^b P(y) g(y) dy`,                      (159)

which is `legendre_tail`. The manuscript exchanges the order of integration (Tonelli); here
the same bound follows by one integration by parts against `Q(x) = ∫_s^x P`. -/

namespace UniformLanczos.Lemma513Legendre

open intervalIntegral Set

theorem legendre_tail (P g g' : ℝ → ℝ) {s r b K : ℝ} (hsr : s < r) (hrb : r ≤ b)
    (hK : 0 ≤ K) (hP : Continuous P) (hP0 : ∀ x, 0 ≤ P x)
    (hg : ∀ x ∈ Icc s b, HasDerivAt g (g' x) x)
    (hg' : IntervalIntegrable g' MeasureTheory.volume r b)
    (hmono : AntitoneOn g (Icc s b)) (hgb : 0 ≤ g b)
    (hneg : ∀ x ∈ Icc r b, g' x ≤ 0)
    (hLeg : ∀ x ∈ Icc r b, P x ≤ K / (x - s) * ∫ y in s..x, P y) :
    ∫ x in r..b, P x * (-g' x) ≤ K / (r - s) * ∫ y in s..b, P y * g y := by
  set Q : ℝ → ℝ := fun x => ∫ y in s..x, P y
  set h : ℝ → ℝ := fun x => g x - g b
  have hsb : s ≤ b := by linarith
  have hgc : ContinuousOn g (Icc s b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hQd : ∀ x, HasDerivAt Q (P x) x := fun x => (hP.integral_hasStrictDerivAt s x).hasDerivAt
  have hQc : Continuous Q := continuous_iff_continuousAt.mpr fun x => (hQd x).continuousAt
  have hQ0 : ∀ x, s ≤ x → 0 ≤ Q x := fun x hx =>
    intervalIntegral.integral_nonneg hx fun y _ => hP0 y
  have hsub : uIcc r b ⊆ Icc s b := by
    rw [uIcc_of_le hrb]; exact Icc_subset_Icc hsr.le le_rfl
  have hhd : ∀ x ∈ uIcc r b, HasDerivAt h (g' x) x := fun x hx => by
    simpa [h] using (hg x (hsub hx)).sub_const (g b)
  -- Step 1: the endpoint inequality and `x - s ≥ r - s`
  have hint1 : IntervalIntegrable (fun x => P x * (-g' x)) MeasureTheory.volume r b :=
    hg'.neg.continuousOn_mul hP.continuousOn
  have hint2 : IntervalIntegrable (fun x => K / (r - s) * (Q x * (-g' x)))
      MeasureTheory.volume r b :=
    (hg'.neg.continuousOn_mul hQc.continuousOn).const_mul _
  have hstep1 : ∫ x in r..b, P x * (-g' x) ≤ ∫ x in r..b, K / (r - s) * (Q x * (-g' x)) := by
    apply intervalIntegral.integral_mono_on hrb hint1 hint2
    intro x hx
    have hx' : x ∈ Icc r b := hx
    have hxs : 0 < x - s := by linarith [hx'.1]
    have hng : 0 ≤ -g' x := by linarith [hneg x hx']
    have hQx : 0 ≤ Q x := hQ0 x (by linarith [hx'.1])
    have hfrac : K / (x - s) ≤ K / (r - s) :=
      div_le_div_of_nonneg_left hK (by linarith) (by linarith [hx'.1])
    calc P x * (-g' x) ≤ K / (x - s) * Q x * (-g' x) :=
          mul_le_mul_of_nonneg_right (hLeg x hx') hng
      _ ≤ K / (r - s) * Q x * (-g' x) := by
          apply mul_le_mul_of_nonneg_right _ hng
          exact mul_le_mul_of_nonneg_right hfrac hQx
      _ = K / (r - s) * (Q x * (-g' x)) := by ring
  -- Step 2: integration by parts, `∫_r^b Q (-g') = Q(r) h(r) + ∫_r^b P h`
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := r) (b := b)
    (fun x _ => hQd x) hhd (hP.intervalIntegrable r b) hg'
  have hhb : h b = 0 := by simp [h]
  rw [hhb, mul_zero, zero_sub] at hparts
  have hneg_int : ∫ x in r..b, Q x * (-g' x) = Q r * h r + ∫ x in r..b, P x * h x := by
    have : ∫ x in r..b, Q x * (-g' x) = -∫ x in r..b, Q x * g' x := by
      rw [← intervalIntegral.integral_neg]; congr 1; funext x; ring
    rw [this, hparts]; ring
  -- Step 3: `Q(r) h(r) ≤ ∫_s^r P h`, because `h` is nonincreasing on `[s, r]`
  have hhc : ContinuousOn h (Icc s b) := hgc.sub continuousOn_const
  have hPh : ∀ c d, c ∈ Icc s b → d ∈ Icc s b →
      IntervalIntegrable (fun x => P x * h x) MeasureTheory.volume c d := by
    intro c d hc hd
    apply ContinuousOn.intervalIntegrable
    apply hP.continuousOn.mul
    exact hhc.mono (uIcc_subset_Icc hc hd)
  have hs_mem : s ∈ Icc s b := ⟨le_rfl, hsb⟩
  have hr_mem : r ∈ Icc s b := ⟨hsr.le, hrb⟩
  have hb_mem : b ∈ Icc s b := ⟨hsb, le_rfl⟩
  have hstep3 : Q r * h r ≤ ∫ y in s..r, P y * h y := by
    have hQr : Q r * h r = ∫ y in s..r, P y * h r := by
      simp only [Q]; rw [intervalIntegral.integral_mul_const]
    rw [hQr]
    apply intervalIntegral.integral_mono_on hsr.le
    · exact (hP.intervalIntegrable s r).mul_const _
    · exact hPh s r hs_mem hr_mem
    · intro y hy
      have hy' : y ∈ Icc s b := ⟨hy.1, le_trans hy.2 hrb⟩
      have hhy : h r ≤ h y := by
        simp only [h]; linarith [hmono hy' hr_mem hy.2]
      exact mul_le_mul_of_nonneg_left hhy (hP0 y)
  -- Step 4: `∫_s^b P h ≤ ∫_s^b P g`, as `g(b) ≥ 0`
  have hstep4 : ∫ y in s..b, P y * h y ≤ ∫ y in s..b, P y * g y := by
    apply intervalIntegral.integral_mono_on hsb (hPh s b hs_mem hb_mem)
    · exact (hP.continuousOn.mul hgc).intervalIntegrable_of_Icc hsb
    · intro y _
      have : h y ≤ g y := by simp only [h]; linarith
      exact mul_le_mul_of_nonneg_left this (hP0 y)
  have hadd : (∫ y in s..r, P y * h y) + ∫ y in r..b, P y * h y = ∫ y in s..b, P y * h y :=
    intervalIntegral.integral_add_adjacent_intervals (hPh s r hs_mem hr_mem)
      (hPh r b hr_mem hb_mem)
  have hKrs : 0 ≤ K / (r - s) := div_nonneg hK (by linarith)
  calc ∫ x in r..b, P x * (-g' x)
      ≤ ∫ x in r..b, K / (r - s) * (Q x * (-g' x)) := hstep1
    _ = K / (r - s) * (Q r * h r + ∫ x in r..b, P x * h x) := by
        rw [intervalIntegral.integral_const_mul, hneg_int]
    _ ≤ K / (r - s) * ((∫ y in s..r, P y * h y) + ∫ y in r..b, P y * h y) := by
        apply mul_le_mul_of_nonneg_left _ hKrs; linarith
    _ = K / (r - s) * ∫ y in s..b, P y * h y := by rw [hadd]
    _ ≤ K / (r - s) * ∫ y in s..b, P y * g y := mul_le_mul_of_nonneg_left hstep4 hKrs

/-- **Second bound in (158), one half-line.** With `|φ'_M| g_M = -g'_M/M` on `(0, 1/2)` and
`|p_k p_{k-1}| ≤ (p_k² + p_{k-1}²)/2`, (159) for `p_k` and `p_{k-1}` (degree at most `k`,
`K = (k+1)²`) and the unweighted tails `∫_s^b p² g ≤ T` give
`∫_r^b |p_k p_{k-1}| (-g'/M) ≤ K T / (M (r-s))`. -/
theorem second_tail_half (pk pk1 g g' : ℝ → ℝ) {s r b K T M : ℝ} (hsr : s < r) (hrb : r ≤ b)
    (hK : 0 ≤ K) (hM : 0 < M) (hpk : Continuous pk) (hpk1 : Continuous pk1)
    (hg : ∀ x ∈ Icc s b, HasDerivAt g (g' x) x)
    (hg' : IntervalIntegrable g' MeasureTheory.volume r b)
    (hmono : AntitoneOn g (Icc s b)) (hgb : 0 ≤ g b)
    (hneg : ∀ x ∈ Icc r b, g' x ≤ 0)
    (hLeg : ∀ x ∈ Icc r b, pk x ^ 2 ≤ K / (x - s) * ∫ y in s..x, pk y ^ 2)
    (hLeg1 : ∀ x ∈ Icc r b, pk1 x ^ 2 ≤ K / (x - s) * ∫ y in s..x, pk1 y ^ 2)
    (hT : ∫ y in s..b, pk y ^ 2 * g y ≤ T) (hT1 : ∫ y in s..b, pk1 y ^ 2 * g y ≤ T) :
    ∫ x in r..b, |pk x * pk1 x| * (-g' x / M) ≤ K * T / (M * (r - s)) := by
  have hP : Continuous fun x => pk x ^ 2 := hpk.pow 2
  have hP1 : Continuous fun x => pk1 x ^ 2 := hpk1.pow 2
  have h1 := legendre_tail (fun x => pk x ^ 2) g g' hsr hrb hK hP (fun x => sq_nonneg _)
    hg hg' hmono hgb hneg hLeg
  have h2 := legendre_tail (fun x => pk1 x ^ 2) g g' hsr hrb hK hP1 (fun x => sq_nonneg _)
    hg hg' hmono hgb hneg hLeg1
  have hKrs : 0 ≤ K / (r - s) := div_nonneg hK (by linarith)
  have hi1 : IntervalIntegrable (fun x => pk x ^ 2 * (-g' x)) MeasureTheory.volume r b :=
    hg'.neg.continuousOn_mul hP.continuousOn
  have hi2 : IntervalIntegrable (fun x => pk1 x ^ 2 * (-g' x)) MeasureTheory.volume r b :=
    hg'.neg.continuousOn_mul hP1.continuousOn
  have hiL : IntervalIntegrable (fun x => |pk x * pk1 x| * (-g' x / M))
      MeasureTheory.volume r b := by
    have : (fun x => |pk x * pk1 x| * (-g' x / M)) = fun x => -g' x * (|pk x * pk1 x| / M) := by
      funext x; ring
    rw [this]
    exact hg'.neg.mul_continuousOn ((hpk.mul hpk1).abs.div_const M).continuousOn
  have hiR : IntervalIntegrable (fun x => (pk x ^ 2 * (-g' x) + pk1 x ^ 2 * (-g' x)) / (2 * M))
      MeasureTheory.volume r b := (hi1.add hi2).div_const _
  have hpt : ∀ x ∈ Icc r b, |pk x * pk1 x| * (-g' x / M) ≤
      (pk x ^ 2 * (-g' x) + pk1 x ^ 2 * (-g' x)) / (2 * M) := by
    intro x hx
    have hng : 0 ≤ -g' x := by linarith [hneg x hx]
    have hab : |pk x * pk1 x| ≤ (pk x ^ 2 + pk1 x ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|pk x| - |pk1 x|), sq_abs (pk x), sq_abs (pk1 x)]
    rw [show (pk x ^ 2 * (-g' x) + pk1 x ^ 2 * (-g' x)) / (2 * M) =
      (pk x ^ 2 + pk1 x ^ 2) / 2 * (-g' x / M) by field_simp; ring]
    exact mul_le_mul_of_nonneg_right hab (div_nonneg hng hM.le)
  calc ∫ x in r..b, |pk x * pk1 x| * (-g' x / M)
      ≤ ∫ x in r..b, (pk x ^ 2 * (-g' x) + pk1 x ^ 2 * (-g' x)) / (2 * M) :=
        intervalIntegral.integral_mono_on hrb hiL hiR hpt
    _ = ((∫ x in r..b, pk x ^ 2 * (-g' x)) + ∫ x in r..b, pk1 x ^ 2 * (-g' x)) / (2 * M) := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_add hi1 hi2]
    _ ≤ (K / (r - s) * T + K / (r - s) * T) / (2 * M) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have e1 := h1.trans (mul_le_mul_of_nonneg_left hT hKrs)
        have e2 := h2.trans (mul_le_mul_of_nonneg_left hT1 hKrs)
        linarith
    _ = K * T / (M * (r - s)) := by
        have : r - s ≠ 0 := by linarith
        field_simp; ring

/-- With `K = (k+1)²`, `T = e^{-cM}` and `M (r-s) ≥ 1`, each half-line contributes at most
`(k+1)² e^{-cM}`, so the two together give the second bound `2 (k+1)² e^{-cM}` of (158). -/
theorem second_tail_exp {k : ℕ} {c M r s : ℝ} (hrs : 1 ≤ M * (r - s)) :
    ((k:ℝ) + 1) ^ 2 * Real.exp (-c * M) / (M * (r - s)) ≤
      ((k:ℝ) + 1) ^ 2 * Real.exp (-c * M) := by
  have hpos : 0 ≤ ((k:ℝ) + 1) ^ 2 * Real.exp (-c * M) := by positivity
  exact div_le_self hpos hrs

end UniformLanczos.Lemma513Legendre

#print axioms UniformLanczos.Lemma513Legendre.legendre_tail
#print axioms UniformLanczos.Lemma513Legendre.second_tail_half
#print axioms UniformLanczos.Lemma513Legendre.second_tail_exp
