import EulerianGrothendieck.OccupancySharpRemainder
import EulerianGrothendieck.CriticalSubcriticalVacuum
import EulerianGrothendieck.CentralFactorialMoments

/-! # Task G1, part 2: Theorem 9.5 with the printed functions `F, A, B`

For `c > 1/12`, `t = 1/(12c)`, `s = t²` and every `M ≥ 1`, for the actual probability integral
`N = E exp(S_M T_M/(cM))`:

  `0 ≤ N - F(s) + A(s)/M ≤ B(s)/M²`   (`explicit_norm_remainder`),
  `|1/N - (1/F + A/(F² M))| ≤ (B + A²)/(F² M²)`   (`explicit_vacuum_remainder`),

with exactly the printed
`F = (1-s)^{-1/2}`, `A = 3s²/(10(1-s)²√(1-s))`,
`B = (27/50){105 s⁴/(16(1-s)⁴√(1-s)) + 15 s³/(2(1-s)³√(1-s)) + 3s²/(2(1-s)²√(1-s))}`. -/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Finset
namespace EulerianGrothendieck

def remF (s : ℝ) : ℝ := 1 / Real.sqrt (1 - s)
def remA (s : ℝ) : ℝ := 3 * s ^ 2 / (10 * (1 - s) ^ 2 * Real.sqrt (1 - s))
def remB (s : ℝ) : ℝ := 27 / 50 * (105 * s ^ 4 / (16 * (1 - s) ^ 4 * Real.sqrt (1 - s)) +
  15 * s ^ 3 / (2 * (1 - s) ^ 3 * Real.sqrt (1 - s)) + 3 * s ^ 2 / (2 * (1 - s) ^ 2 * Real.sqrt (1 - s)))

theorem centralFactorialMoment_closed (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    centralFactorialMoment s 2 = 3/4 * s ^ 2 / ((1 - s) ^ 2 * Real.sqrt (1 - s)) ∧
    centralFactorialMoment s 3 = 15/8 * s ^ 3 / ((1 - s) ^ 3 * Real.sqrt (1 - s)) ∧
    centralFactorialMoment s 4 = 105/16 * s ^ 4 / ((1 - s) ^ 4 * Real.sqrt (1 - s)) := by
  have h0 := centralFactorialMoment_zero s hs0 hs1
  have r0 := centralFactorialMoment_recurrence s hs0 hs1 0
  have r1 := centralFactorialMoment_recurrence s hs0 hs1 1
  have r2 := centralFactorialMoment_recurrence s hs0 hs1 2
  have r3 := centralFactorialMoment_recurrence s hs0 hs1 3
  have hd : 0 < 1 - s := by linarith
  have hq : 0 < Real.sqrt (1 - s) := Real.sqrt_pos.mpr hd
  have e1 : centralFactorialMoment s 1 = s * (1/2) * centralFactorialMoment s 0 / (1 - s) := by
    rw [eq_div_iff hd.ne']; push_cast at r0; linarith
  have e2 : centralFactorialMoment s 2 = s * (3/2) * centralFactorialMoment s 1 / (1 - s) := by
    rw [eq_div_iff hd.ne']; push_cast at r1; linarith
  have e3 : centralFactorialMoment s 3 = s * (5/2) * centralFactorialMoment s 2 / (1 - s) := by
    rw [eq_div_iff hd.ne']; push_cast at r2; linarith
  have e4 : centralFactorialMoment s 4 = s * (7/2) * centralFactorialMoment s 3 / (1 - s) := by
    rw [eq_div_iff hd.ne']; push_cast at r3; linarith
  have hd' : (1 - s) ≠ 0 := hd.ne'
  have hq' : Real.sqrt (1 - s) ≠ 0 := hq.ne'
  have c2 : centralFactorialMoment s 2 = 3/4 * s ^ 2 / ((1 - s) ^ 2 * Real.sqrt (1 - s)) := by
    rw [e2, e1, h0]; field_simp <;> ring
  have c3 : centralFactorialMoment s 3 = 15/8 * s ^ 3 / ((1 - s) ^ 3 * Real.sqrt (1 - s)) := by
    rw [e3, c2]; field_simp <;> ring
  refine ⟨c2, c3, ?_⟩
  rw [e4, c3]; field_simp <;> ring

theorem fallingReal_two (x : ℝ) : fallingReal 2 x = x * (x - 1) := by
  simp only [fallingReal]; push_cast; ring
theorem fallingReal_three (x : ℝ) : fallingReal 3 x = x * (x - 1) * (x - 2) := by
  simp only [fallingReal]; push_cast; ring
theorem fallingReal_four (x : ℝ) : fallingReal 4 x = x * (x - 1) * (x - 2) * (x - 3) := by
  simp only [fallingReal]; push_cast; ring

theorem binomialWeight_eq_central (t : ℝ) (k : ℕ) :
    binomialWeight t k = centralCoefficient k * (t ^ 2) ^ k := by
  unfold binomialWeight centralCoefficient
  rw [Nat.centralBinom_eq_two_mul_choose, ← pow_mul]

theorem weighted_falling_hasSum (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (q : ℕ) :
    HasSum (fun k : ℕ => binomialWeight t k * fallingReal q k) (centralFactorialMoment (t^2) q) := by
  have hs0 : 0 < t ^ 2 := by positivity
  have hs1 : t ^ 2 < 1 := by nlinarith
  have h := (centralFactorialMoment_summable (t^2) hs0 hs1 q).hasSum
  refine h.congr_fun (fun k => ?_)
  rw [binomialWeight_eq_central]; ring

/-- **Theorem 9.5** (explicit form): `0 ≤ N - F(s) + A(s)/M ≤ B(s)/M²` for every `M ≥ 1`,
with `s = (1/(12c))²`. -/
theorem explicit_norm_remainder_aux
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (c : ℝ) (hc : 1/12 < c) (M : ℕ) (hM : M ≠ 0) :
    0 ≤ (∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) /
        (c * (M:ℝ))) ∂μ.prod μ) - remF ((1/(12*c))^2) + remA ((1/(12*c))^2) / M ∧
    (∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) /
        (c * (M:ℝ))) ∂μ.prod μ) - remF ((1/(12*c))^2) + remA ((1/(12*c))^2) / M ≤
      remB ((1/(12*c))^2) / (M:ℝ) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hN := raw_uniform_kernel_hasSum U hU hind hlaw c hc0.ne' M hM
  have ht := normalized_scale_mem c hc
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) *
      (∑ i ∈ range M, U i xy.2) / (c * (M:ℝ))) ∂μ.prod μ := ⟨_, rfl⟩
  rw [← hNdef] at hN ⊢
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = 1/(12*c) := ⟨_, rfl⟩
  rw [← htdef] at hN ht ⊢
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = t ^ 2 := ⟨_, rfl⟩
  rw [← hsdef]
  have hs0 : 0 < s := by rw [hsdef]; exact pow_pos ht.1 2
  have hs1 : s < 1 := by rw [hsdef]; nlinarith [ht.1, ht.2]
  have hm : (0:ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hm' : (M:ℝ) ≠ 0 := hm.ne'
  have hd : 0 < 1 - s := by linarith
  have hd' : (1 - s) ≠ 0 := hd.ne'
  have hq : 0 < Real.sqrt (1 - s) := Real.sqrt_pos.mpr hd
  have hq' : Real.sqrt (1 - s) ≠ 0 := hq.ne'
  obtain ⟨c2, c3, c4⟩ := centralFactorialMoment_closed s hs0 hs1
  have hF := weighted_falling_hasSum t ht.1 ht.2 0
  have h2 := weighted_falling_hasSum t ht.1 ht.2 2
  have h3 := weighted_falling_hasSum t ht.1 ht.2 3
  have h4 := weighted_falling_hasSum t ht.1 ht.2 4
  rw [← hsdef] at hF h2 h3 h4
  simp only [fallingReal, mul_one] at hF
  rw [centralFactorialMoment_zero s hs0 hs1] at hF
  -- the centred series
  have hD := (hN.sub hF).add (h2.mul_left (2/5 / (M:ℝ)))
  have hBs := ((h4.add (h3.mul_left 4)).add (h2.mul_left 2)).mul_left (27 / (50 * (M:ℝ) ^ 2))
  have hFeq : 1 / Real.sqrt (1 - s) = remF s := rfl
  have hAeq : 2/5 / (M:ℝ) * centralFactorialMoment s 2 = remA s / M := by
    rw [c2, remA]; field_simp <;> ring
  have hBeq : 27 / (50 * (M:ℝ) ^ 2) * (centralFactorialMoment s 4 +
      4 * centralFactorialMoment s 3 + 2 * centralFactorialMoment s 2) = remB s / (M:ℝ) ^ 2 := by
    rw [c2, c3, c4, remB]; field_simp <;> ring
  rw [hFeq, hAeq] at hD
  rw [hBeq] at hBs
  have hterm : ∀ k : ℕ, binomialWeight t k * uniformMomentRatio M k ^ 2 - binomialWeight t k +
      2/5 / (M:ℝ) * (binomialWeight t k * fallingReal 2 k) =
      binomialWeight t k * (uniformMomentRatio M k ^ 2 - (1 - 2 * (k * ((k:ℝ) - 1) / 5) / M)) := by
    intro k; rw [fallingReal_two]; ring
  have hD' : HasSum (fun k : ℕ => binomialWeight t k *
      (uniformMomentRatio M k ^ 2 - (1 - 2 * (k * ((k:ℝ) - 1) / 5) / M)))
      (N - remF s + remA s / M) :=
    hD.congr_fun (fun k => (hterm k).symm)
  have hR := fun k => Occupancy.occupancy_square_bound M k hM
  constructor
  · exact hasSum_le (fun k => mul_nonneg (binomialWeight_nonneg t k) (hR k).1) hasSum_zero hD'
  · refine hasSum_le (fun k => ?_) hD' hBs
    rw [fallingReal_two, fallingReal_three, fallingReal_four]
    have hw := binomialWeight_nonneg t k
    have := mul_le_mul_of_nonneg_left (hR k).2 hw
    calc binomialWeight t k * (uniformMomentRatio M k ^ 2 - (1 - 2 * (k * ((k:ℝ) - 1) / 5) / M))
        ≤ binomialWeight t k * (27 / (50 * (M:ℝ) ^ 2) * ((k:ℝ) ^ 2 * ((k:ℝ) - 1) ^ 2)) := this
      _ = _ := by ring

/-- **Theorem 9.5**: `0 ≤ N - F(s) + A(s)/M ≤ B(s)/M²` for every `M ≥ 1`. -/
theorem explicit_norm_remainder
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (c : ℝ) (hc : 1/12 < c) (M : ℕ) (hM : M ≠ 0) :
    let N := ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) /
      (c * (M:ℝ))) ∂μ.prod μ
    let s := (1/(12*c)) ^ 2
    0 ≤ N - remF s + remA s / M ∧ N - remF s + remA s / M ≤ remB s / (M:ℝ) ^ 2 := by
  intro N s
  exact explicit_norm_remainder_aux U hU hind hlaw c hc M hM

/-- The printed inversion estimate `|1/N - (1/F + A/(F²M))| ≤ (B + A²)/(F²M²)` (explicit form). -/
theorem explicit_vacuum_remainder_aux
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (c : ℝ) (hc : 1/12 < c) (M : ℕ) (hM : M ≠ 0) :
    |1 / (∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) /
        (c * (M:ℝ))) ∂μ.prod μ) -
      (1 / remF ((1/(12*c))^2) + remA ((1/(12*c))^2) / (remF ((1/(12*c))^2) ^ 2 * M))| ≤
      (remB ((1/(12*c))^2) + remA ((1/(12*c))^2) ^ 2) / (remF ((1/(12*c))^2) ^ 2 * (M:ℝ) ^ 2) := by
  have hc0 : 0 < c := by linarith
  have ht := normalized_scale_mem c hc
  obtain ⟨hlow, hup⟩ := explicit_norm_remainder_aux U hU hind hlaw c hc M hM
  have hNid := raw_uniform_kernel_identity U hU hind hlaw c hc0.ne' M hM
  have hN := raw_uniform_kernel_hasSum U hU hind hlaw c hc0.ne' M hM
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) *
      (∑ i ∈ range M, U i xy.2) / (c * (M:ℝ))) ∂μ.prod μ := ⟨_, rfl⟩
  rw [← hNdef] at hlow hup hNid hN ⊢
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = 1/(12*c) := ⟨_, rfl⟩
  rw [← htdef] at hlow hup hNid hN ht ⊢
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = t ^ 2 := ⟨_, rfl⟩
  rw [← hsdef] at hlow hup ⊢
  have hs0 : 0 < s := by rw [hsdef]; exact pow_pos ht.1 2
  have hs1 : s < 1 := by rw [hsdef]; nlinarith [ht.1, ht.2]
  have hm : (0:ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hm' : (M:ℝ) ≠ 0 := hm.ne'
  have hN1 : 1 ≤ N := by rw [hNid]; exact uniformNormSeries_ge_one M hM t ht.1 ht.2
  have hNF : N ≤ remF s := by
    have hF := weighted_falling_hasSum t ht.1 ht.2 0
    rw [← hsdef] at hF
    simp only [fallingReal, mul_one] at hF
    rw [centralFactorialMoment_zero s hs0 hs1] at hF
    refine hasSum_le (fun k => ?_) hN hF
    have h0 := uniformMomentRatio_nonneg M k
    have h1 := uniformMomentRatio_le_one M k hM
    have hw := binomialWeight_nonneg t k
    exact mul_le_of_le_one_right hw (pow_le_one₀ h0 h1)
  have hFpos : 0 < remF s := by
    unfold remF
    have := Real.sqrt_pos.mpr (show 0 < 1 - s by linarith)
    positivity
  have hF' : remF s ≠ 0 := hFpos.ne'
  have hA0 : 0 ≤ remA s := by unfold remA; positivity
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = remF s - N := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by linarith
  have hxA : x ≤ remA s / M := by linarith
  have hE : remA s / M - x ≤ remB s / (M:ℝ) ^ 2 := by linarith
  have hE0 : 0 ≤ remA s / M - x := by linarith
  have hNpos : 0 < N := by linarith
  have hN' : N ≠ 0 := hNpos.ne'
  have key : 1 / N - (1 / remF s + remA s / (remF s ^ 2 * M)) =
      (x ^ 2 / N - (remA s / M - x)) / remF s ^ 2 := by
    rw [hx]; field_simp; ring
  rw [key, abs_div, abs_of_pos (by positivity : 0 < remF s ^ 2)]
  have hq1 : x ^ 2 / N ≤ (remA s / M) ^ 2 := by
    calc x ^ 2 / N ≤ x ^ 2 := div_le_self (sq_nonneg x) hN1
      _ ≤ (remA s / M) ^ 2 := pow_le_pow_left₀ hx0 hxA 2
  have hq0 : 0 ≤ x ^ 2 / N := by positivity
  have hsum : (remA s / M) ^ 2 + remB s / (M:ℝ) ^ 2 = (remB s + remA s ^ 2) / (M:ℝ) ^ 2 := by
    rw [div_pow, ← add_div, add_comm]
  have habs : |x ^ 2 / N - (remA s / M - x)| ≤ (remB s + remA s ^ 2) / (M:ℝ) ^ 2 := by
    rw [abs_le]
    constructor <;> linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc |x ^ 2 / N - (remA s / M - x)| * (remF s ^ 2 * (M:ℝ) ^ 2)
      ≤ (remB s + remA s ^ 2) / (M:ℝ) ^ 2 * (remF s ^ 2 * (M:ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right habs (by positivity)
    _ = (remB s + remA s ^ 2) * remF s ^ 2 := by field_simp <;> ring

/-- The printed inversion estimate `|1/N - (1/F + A/(F²M))| ≤ (B + A²)/(F²M²)`. -/
theorem explicit_vacuum_remainder
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (c : ℝ) (hc : 1/12 < c) (M : ℕ) (hM : M ≠ 0) :
    let N := ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) /
      (c * (M:ℝ))) ∂μ.prod μ
    let s := (1/(12*c)) ^ 2
    |1 / N - (1 / remF s + remA s / (remF s ^ 2 * M))| ≤
      (remB s + remA s ^ 2) / (remF s ^ 2 * (M:ℝ) ^ 2) := by
  intro N s
  exact explicit_vacuum_remainder_aux U hU hind hlaw c hc M hM

end EulerianGrothendieck
