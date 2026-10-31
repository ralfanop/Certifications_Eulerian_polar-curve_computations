/-
# Dirichlet kernel, Lebesgue constants and the bounded sine sums (input to V001 Prop. 3.10)

`D N x = 1 + 2 ∑_{n=1}^N cos(n x)`.  Proved here:
* `sin(x/2) · D_N(x) = sin((N + ½) x)`;
* **Lebesgue constants** `L_N = ∫_{−π}^{π} |D_N| ≍ log N`, explicitly
  `(4/π) log(N + 1) ≤ L_N ≤ 2π (1 + log(2N + 1))`
  (the fact cited in the proof of Prop. 3.10 as [Grafakos, Exercise 3.1.5(b)]);
* `|∑_{n=a}^{m} sin(n x)| ≤ 1/sin(x/2)` and Abel summation;
* the sine sums of the proof of Prop. 3.10 are uniformly bounded:
  `|∑_{n=1}^N sin(n x)/n| ≤ 1 + π` for all `N` and all real `x`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.ToIntervalMod

open Real Finset intervalIntegral MeasureTheory Set

noncomputable section

namespace EulerianCert.Lebesgue

/-- The Dirichlet kernel `D_N(x) = 1 + 2 ∑_{n=1}^N cos(n x)`. -/
def D (N : ℕ) (x : ℝ) : ℝ := 1 + 2 * ∑ n ∈ range N, cos ((n + 1 : ℕ) * x)

lemma D_succ (N : ℕ) (x : ℝ) : D (N + 1) x = D N x + 2 * cos ((N + 1 : ℕ) * x) := by
  simp only [D, Finset.sum_range_succ]; ring

lemma continuous_D (N : ℕ) : Continuous (D N) := by
  unfold D; fun_prop

lemma D_neg (N : ℕ) (x : ℝ) : D N (-x) = D N x := by
  simp only [D, mul_neg, cos_neg]

lemma D_periodic (N : ℕ) : Function.Periodic (D N) (2 * π) := by
  intro x
  simp only [D]
  congr 2
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [mul_add, cos_add_nat_mul_two_pi]

lemma sin_mul_D (N : ℕ) (x : ℝ) : sin (x / 2) * D N x = sin ((N + 1 / 2) * x) := by
  induction N with
  | zero => simp [D]; ring_nf
  | succ N ih =>
    rw [D_succ, mul_add, ih]
    have gen : ∀ c b : ℝ, sin (c - b) + sin b * (2 * cos c) = sin (c + b) := by
      intro c b; rw [sin_sub, sin_add]; ring
    have := gen (((N + 1 : ℕ) : ℝ) * x) (x / 2)
    convert this using 2 <;> push_cast <;> ring

lemma abs_D_le (N : ℕ) (x : ℝ) : |D N x| ≤ 2 * N + 1 := by
  unfold D
  have h : |∑ n ∈ range N, cos ((n + 1 : ℕ) * x)| ≤ N := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ range N, |cos ((n + 1 : ℕ) * x)| ≤ ∑ _n ∈ range N, (1 : ℝ) :=
          Finset.sum_le_sum (fun n _ => abs_cos_le_one _)
      _ = N := by simp
  calc |1 + 2 * ∑ n ∈ range N, cos ((n + 1 : ℕ) * x)|
      ≤ |1| + |2 * ∑ n ∈ range N, cos ((n + 1 : ℕ) * x)| := abs_add_le _ _
    _ ≤ 2 * N + 1 := by rw [abs_mul, abs_one, abs_two]; linarith

lemma sin_half_pos {x : ℝ} (h0 : 0 < x) (hπ : x ≤ π) : 0 < sin (x / 2) :=
  sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])

/-- Jordan's inequality `sin(x/2) ≥ x/π` on `[0, π]`. -/
lemma sin_half_ge {x : ℝ} (h0 : 0 ≤ x) (hπ : x ≤ π) : x / π ≤ sin (x / 2) := by
  have := mul_le_sin (x := x / 2) (by linarith) (by linarith)
  calc x / π = 2 / π * (x / 2) := by field_simp
    _ ≤ _ := this

lemma abs_D_le_div {N : ℕ} {x : ℝ} (h0 : 0 < x) (hπ : x ≤ π) : |D N x| ≤ π / x := by
  have hs := sin_half_pos h0 hπ
  have hD : D N x = sin ((N + 1 / 2) * x) / sin (x / 2) := by
    rw [← sin_mul_D]; field_simp
  rw [hD, abs_div, abs_of_pos hs]
  calc |sin ((N + 1 / 2) * x)| / sin (x / 2) ≤ 1 / sin (x / 2) :=
        div_le_div_of_nonneg_right (abs_sin_le_one _) hs.le
    _ ≤ 1 / (x / π) := one_div_le_one_div_of_le (by positivity) (sin_half_ge h0.le hπ)
    _ = π / x := by field_simp

lemma abs_D_ge {N : ℕ} {x : ℝ} (h0 : 0 < x) (hπ : x ≤ π) :
    2 * |sin ((N + 1 / 2) * x)| / x ≤ |D N x| := by
  have hs := sin_half_pos h0 hπ
  have hD : D N x = sin ((N + 1 / 2) * x) / sin (x / 2) := by
    rw [← sin_mul_D]; field_simp
  rw [hD, abs_div, abs_of_pos hs]
  have hle : sin (x / 2) ≤ x / 2 := sin_le (by linarith)
  rw [div_le_div_iff₀ h0 hs]
  nlinarith [abs_nonneg (sin ((N + 1 / 2) * x))]

/-- The Lebesgue constant `L_N = ∫_{−π}^{π} |D_N|`. -/
def L (N : ℕ) : ℝ := ∫ x in (-π)..π, |D N x|

lemma integrable_absD (N : ℕ) (a b : ℝ) : IntervalIntegrable (fun x => |D N x|) volume a b :=
  ((continuous_D N).abs).intervalIntegrable a b

/-- `∫_0^π |sin(a x)|` over one arch. -/
lemma integral_abs_sin_arch {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ∫ x in (k * π / a)..((k + 1 : ℕ) * π / a), |sin (a * x)| = 2 / a := by
  have h1 : ∫ x in (k * π / a)..((k + 1 : ℕ) * π / a), |sin (a * x)| =
      a⁻¹ * ∫ u in (k * π)..((k + 1 : ℕ) * π), |sin u| := by
    rw [intervalIntegral.integral_comp_mul_left (fun u => |sin u|) ha.ne']
    congr 2 <;> field_simp
  have h2 : ∫ u in (k * π)..((k + 1 : ℕ) * π), |sin u| = ∫ u in (0 : ℝ)..π, |sin u| := by
    have := intervalIntegral.integral_comp_add_right (fun u => |sin u|) (k * π) (a := 0) (b := π)
    simp only [zero_add] at this
    rw [show ((k + 1 : ℕ) : ℝ) * π = π + k * π by push_cast; ring, ← this]
    refine (intervalIntegral.integral_congr (fun u _ => ?_)).symm
    rw [sin_add_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have h3 : ∫ u in (0 : ℝ)..π, |sin u| = 2 := by
    rw [intervalIntegral.integral_congr (g := sin) (fun u hu => by
      rw [uIcc_of_le pi_pos.le] at hu
      exact abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hu.1 hu.2))]
    rw [integral_sin]; simp; norm_num
  rw [h1, h2, h3]; field_simp

/-- Lower bound for the Lebesgue constants. -/
theorem L_lower (N : ℕ) : 4 / π * log (N + 1) ≤ L N := by
  set a : ℝ := N + 1 / 2 with ha_def
  have ha : 0 < a := by positivity
  set p : ℕ → ℝ := fun k => k * π / a with hp
  -- pointwise bound on the k-th arch
  have hpt : ∀ k : ℕ, k < N → ∀ x ∈ Icc (p k) (p (k + 1)),
      2 * a / ((k + 1 : ℕ) * π) * |sin (a * x)| ≤ |D N x| := by
    intro k hk x hx
    have hx0 : 0 ≤ x := le_trans (by positivity) hx.1
    have hxπ : x ≤ π := by
      refine hx.2.trans ?_
      simp only [hp]
      rw [div_le_iff₀ ha]
      have : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
      nlinarith [pi_pos]
    rcases hx0.eq_or_lt with h | h
    · subst h; simp
    · have := abs_D_ge (N := N) h hxπ
      rw [← ha_def, mul_comm a x] at this
      refine le_trans ?_ this
      rw [mul_comm (2 * a / _), mul_div_assoc', div_le_div_iff₀ (by positivity) h]
      have hxk : x * a ≤ (k + 1 : ℕ) * π := by
        have := hx.2; simp only [hp] at this; rwa [le_div_iff₀ ha] at this
      rw [show a * x = x * a by ring]
      nlinarith [mul_le_mul_of_nonneg_left hxk (by positivity : (0 : ℝ) ≤ 2 * |sin (x * a)|)]
  have hsum : ∑ k ∈ range N, ∫ x in p k..p (k + 1), |D N x| = ∫ x in p 0..p N, |D N x| :=
    intervalIntegral.sum_integral_adjacent_intervals (fun k _ => integrable_absD N _ _)
  have hp0 : p 0 = 0 := by simp [hp]
  have hpN : p N ≤ π := by
    simp only [hp]; rw [div_le_iff₀ ha]; nlinarith [pi_pos]
  have hpk : ∀ k, p k ≤ p (k + 1) := fun k => by
    simp only [hp]; apply div_le_div_of_nonneg_right _ ha.le; push_cast; nlinarith [pi_pos]
  have hstep : ∀ k ∈ range N, 4 / π * (1 / ((k : ℝ) + 1)) ≤ ∫ x in p k..p (k + 1), |D N x| := by
    intro k hk
    rw [Finset.mem_range] at hk
    calc 4 / π * (1 / ((k : ℝ) + 1)) = 2 * a / ((k + 1 : ℕ) * π) * (2 / a) := by
          push_cast; field_simp; ring
      _ = 2 * a / ((k + 1 : ℕ) * π) * ∫ x in p k..p (k + 1), |sin (a * x)| := by
          rw [integral_abs_sin_arch ha]
      _ = ∫ x in p k..p (k + 1), 2 * a / ((k + 1 : ℕ) * π) * |sin (a * x)| := by
          rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ x in p k..p (k + 1), |D N x| := by
          apply intervalIntegral.integral_mono_on (hpk k)
          · exact (by fun_prop : Continuous fun x : ℝ =>
              2 * a / ((k + 1 : ℕ) * π) * |sin (a * x)|).intervalIntegrable _ _
          · exact integrable_absD N _ _
          · exact hpt k hk
  have hharm : log (N + 1) ≤ ∑ k ∈ range N, 1 / ((k : ℝ) + 1) := by
    have := log_add_one_le_harmonic N
    push_cast at this
    simpa [harmonic, one_div] using this
  calc 4 / π * log (N + 1) ≤ 4 / π * ∑ k ∈ range N, 1 / ((k : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hharm (by positivity)
    _ = ∑ k ∈ range N, 4 / π * (1 / ((k : ℝ) + 1)) := by rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ range N, ∫ x in p k..p (k + 1), |D N x| := Finset.sum_le_sum hstep
    _ = ∫ x in (0 : ℝ)..p N, |D N x| := by rw [hsum, hp0]
    _ ≤ L N := by
      apply intervalIntegral.integral_mono_interval (by linarith [pi_pos]) (by
        simp only [hp]; positivity) hpN
      · exact Filter.Eventually.of_forall (fun x => abs_nonneg _)
      · exact integrable_absD N _ _

lemma half_le (N : ℕ) : ∫ x in (0 : ℝ)..π, |D N x| ≤ π * (1 + log (2 * N + 1)) := by
  set δ : ℝ := π / (2 * N + 1)
  have hδ : 0 < δ := by positivity
  have hδπ : δ ≤ π := div_le_self pi_pos.le (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := δ) (integrable_absD N _ _)
    (integrable_absD N _ _)]
  have h1 : ∫ x in (0 : ℝ)..δ, |D N x| ≤ π := by
    calc ∫ x in (0 : ℝ)..δ, |D N x| ≤ ∫ x in (0 : ℝ)..δ, (2 * N + 1 : ℝ) := by
          apply intervalIntegral.integral_mono_on hδ.le (integrable_absD N _ _)
            intervalIntegrable_const
          intro x _; exact abs_D_le N x
      _ = π := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; simp only [δ]; field_simp; ring
  have h2 : ∫ x in δ..π, |D N x| ≤ π * log (2 * N + 1) := by
    calc ∫ x in δ..π, |D N x| ≤ ∫ x in δ..π, π * x⁻¹ := by
          apply intervalIntegral.integral_mono_on hδπ (integrable_absD N _ _)
          · apply ContinuousOn.intervalIntegrable
            apply ContinuousOn.mul continuousOn_const
            apply ContinuousOn.inv₀ continuousOn_id
            intro x hx; rw [uIcc_of_le hδπ] at hx; exact (hδ.trans_le hx.1).ne'
          · intro x hx
            rw [← div_eq_mul_inv]
            exact abs_D_le_div (hδ.trans_le hx.1) hx.2
      _ = π * log (2 * N + 1) := by
          rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hδ pi_pos]
          congr 2; simp only [δ]; field_simp
  linarith

/-- Upper bound for the Lebesgue constants. -/
theorem L_upper (N : ℕ) : L N ≤ 2 * π * (1 + log (2 * N + 1)) := by
  have hsplit : L N = (∫ x in (-π)..0, |D N x|) + ∫ x in (0 : ℝ)..π, |D N x| :=
    (intervalIntegral.integral_add_adjacent_intervals (integrable_absD N _ _)
      (integrable_absD N _ _)).symm
  have hneg : ∫ x in (-π)..0, |D N x| = ∫ x in (0 : ℝ)..π, |D N x| := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := π) (fun x => |D N x|)
    simp only [D_neg, neg_zero] at this
    exact this.symm
  rw [hsplit, hneg]
  linarith [half_le N]

/-! ### Bounded sine sums -/

/-- Telescoping: `2 sin(x/2) ∑_{n=a}^{m−1} sin(n x) = cos((a − ½)x) − cos((m − ½)x)`. -/
lemma sin_sum_telescope (x : ℝ) (a : ℕ) {m : ℕ} (ham : a ≤ m) :
    2 * sin (x / 2) * ∑ n ∈ Ico a m, sin (n * x) =
      cos ((a - 1 / 2) * x) - cos ((m - 1 / 2) * x) := by
  induction m, ham using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm, mul_add, ih]
    have gen : ∀ c b : ℝ, cos (c - b) - cos (c + b) = 2 * sin b * sin c := by
      intro c b; rw [cos_sub, cos_add]; ring
    have := gen (m * x) (x / 2)
    have e1 : ((m : ℝ) - 1 / 2) * x = m * x - x / 2 := by ring
    have e2 : (((m + 1 : ℕ) : ℝ) - 1 / 2) * x = m * x + x / 2 := by push_cast; ring
    rw [e1, e2]; linarith

lemma abs_sin_sum_le {x : ℝ} (h0 : 0 < x) (hπ : x ≤ π) (a m : ℕ) :
    |∑ n ∈ Ico a m, sin (n * x)| ≤ π / x := by
  rcases le_or_gt a m with ham | ham
  · have hs := sin_half_pos h0 hπ
    have ht := sin_sum_telescope x a ham
    have hb : |∑ n ∈ Ico a m, sin (n * x)| ≤ 1 / sin (x / 2) := by
      rw [le_div_iff₀ hs]
      have : |2 * sin (x / 2) * ∑ n ∈ Ico a m, sin (n * x)| ≤ 2 := by
        rw [ht]
        calc |cos ((a - 1 / 2) * x) - cos ((m - 1 / 2) * x)|
            ≤ |cos ((a - 1 / 2) * x)| + |cos ((m - 1 / 2) * x)| := abs_sub _ _
          _ ≤ 2 := by linarith [abs_cos_le_one ((a - 1 / 2) * x), abs_cos_le_one ((m - 1 / 2) * x)]
      rw [abs_mul, abs_mul, abs_two, abs_of_pos hs] at this
      linarith
    calc |∑ n ∈ Ico a m, sin (n * x)| ≤ 1 / sin (x / 2) := hb
      _ ≤ 1 / (x / π) := one_div_le_one_div_of_le (by positivity) (sin_half_ge h0.le hπ)
      _ = π / x := by field_simp
  · rw [Finset.Ico_eq_empty_of_le ham.le]; simp; positivity

/-- Abel summation identity. -/
lemma abel_identity (c s : ℕ → ℝ) (a : ℕ) {b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Ico a b, c n * s n =
      ∑ n ∈ Ico a b, (c n - c (n + 1)) * (∑ j ∈ Ico a (n + 1), s j) +
        c b * ∑ j ∈ Ico a b, s j := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ico_succ_top hb, ih, Finset.sum_Ico_succ_top hb, Finset.sum_Ico_succ_top hb]
    ring

lemma telescope_Ico (c : ℕ → ℝ) (a : ℕ) {b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Ico a b, (c n - c (n + 1)) = c a - c b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih => rw [Finset.sum_Ico_succ_top hb, ih]; ring

/-- Abel's inequality for a non-increasing non-negative weight. -/
lemma abel_bound (c s : ℕ → ℝ) (a b : ℕ) (hc : ∀ n, a ≤ n → c (n + 1) ≤ c n)
    (hc0 : ∀ n, a ≤ n → 0 ≤ c n)
    (B : ℝ) (hB : ∀ m, |∑ j ∈ Ico a m, s j| ≤ B) :
    |∑ n ∈ Ico a b, c n * s n| ≤ B * c a := by
  rcases le_or_gt a b with hab | hab
  · rw [abel_identity c s a hab]
    calc |∑ n ∈ Ico a b, (c n - c (n + 1)) * (∑ j ∈ Ico a (n + 1), s j) +
          c b * ∑ j ∈ Ico a b, s j|
        ≤ ∑ n ∈ Ico a b, (c n - c (n + 1)) * B + c b * B := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n hn => ?_))
            have han := (Finset.mem_Ico.mp hn).1
            rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hc n han))]
            exact mul_le_mul_of_nonneg_left (hB _) (sub_nonneg.mpr (hc n han))
          · rw [abs_mul, abs_of_nonneg (hc0 b hab)]
            exact mul_le_mul_of_nonneg_left (hB _) (hc0 b hab)
      _ = B * c a := by rw [← Finset.sum_mul, telescope_Ico c a hab]; ring
  · rw [Finset.Ico_eq_empty_of_le hab.le, Finset.sum_empty, abs_zero]
    have := hB a
    simp only [Finset.Ico_self, Finset.sum_empty, abs_zero] at this
    exact mul_nonneg this (hc0 a le_rfl)

/-- The sine sum `σ_N(x) = ∑_{n=1}^N sin(n x)/n`. -/
def σ (N : ℕ) (x : ℝ) : ℝ := ∑ n ∈ Ico 1 (N + 1), sin (n * x) / n

lemma σ_pos_bound (N : ℕ) {x : ℝ} (h0 : 0 < x) (hπ : x ≤ π) : |σ N x| ≤ 1 + π := by
  set m : ℕ := ⌊1 / x⌋₊ with hm
  have hmx : (m : ℝ) * x ≤ 1 := by
    have := Nat.floor_le (a := 1 / x) (by positivity)
    rw [← hm] at this
    calc (m : ℝ) * x ≤ 1 / x * x := mul_le_mul_of_nonneg_right this h0.le
      _ = 1 := by field_simp
  have hmx' : 1 < ((m + 1 : ℕ) : ℝ) * x := by
    have := Nat.lt_floor_add_one (1 / x)
    rw [← hm] at this
    push_cast
    calc 1 = 1 / x * x := by field_simp
      _ < (m + 1) * x := mul_lt_mul_of_pos_right this h0
  set p : ℕ := min (m + 1) (N + 1)
  have hp1 : 1 ≤ p := le_min (by omega) (by omega)
  have hpN : p ≤ N + 1 := min_le_right _ _
  unfold σ
  rw [← Finset.sum_Ico_consecutive _ hp1 hpN]
  have hA : |∑ n ∈ Ico 1 p, sin (n * x) / n| ≤ 1 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ Ico 1 p, |sin (n * x) / n| ≤ ∑ _n ∈ Ico 1 p, x := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_Ico] at hn
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
          rw [abs_div, Nat.abs_cast, div_le_iff₀ hn0]
          calc |sin (n * x)| ≤ |n * x| := abs_sin_le_abs
            _ = x * n := by rw [abs_of_pos (by positivity)]; ring
      _ = (p - 1 : ℕ) * x := by simp
      _ ≤ m * x := by
          apply mul_le_mul_of_nonneg_right _ h0.le
          exact_mod_cast (show p - 1 ≤ m by omega)
      _ ≤ 1 := hmx
  have hB : |∑ n ∈ Ico p (N + 1), sin (n * x) / n| ≤ π := by
    rcases le_or_gt (m + 1) (N + 1) with hle | hgt
    · have hpm : p = m + 1 := min_eq_left hle
      have := abel_bound (fun n : ℕ => 1 / (n : ℝ)) (fun n => sin (n * x)) p (N + 1)
        (fun n hn => one_div_le_one_div_of_le (by exact_mod_cast (show 0 < n by omega))
          (by push_cast; linarith))
        (fun n _ => by positivity) (π / x) (abs_sin_sum_le h0 hπ p)
      calc |∑ n ∈ Ico p (N + 1), sin (n * x) / n|
          = |∑ n ∈ Ico p (N + 1), 1 / (n : ℝ) * sin (n * x)| := by
            congr 1; refine Finset.sum_congr rfl (fun n _ => ?_); ring
        _ ≤ π / x * (1 / (p : ℝ)) := this
        _ ≤ π := by
            rw [hpm]
            rw [div_mul_div_comm, mul_one, div_le_iff₀ (by positivity)]
            nlinarith [pi_pos]
    · have hpN' : p = N + 1 := min_eq_right hgt.le
      rw [hpN', Finset.Ico_self, Finset.sum_empty, abs_zero]; exact pi_pos.le
  calc |∑ n ∈ Ico 1 p, sin (n * x) / n + ∑ n ∈ Ico p (N + 1), sin (n * x) / n|
      ≤ |∑ n ∈ Ico 1 p, sin (n * x) / n| + |∑ n ∈ Ico p (N + 1), sin (n * x) / n| :=
        abs_add_le _ _
    _ ≤ 1 + π := add_le_add hA hB

lemma σ_neg (N : ℕ) (x : ℝ) : σ N (-x) = -σ N x := by
  simp only [σ, mul_neg, sin_neg, neg_div, Finset.sum_neg_distrib]

lemma σ_periodic (N : ℕ) : Function.Periodic (σ N) (2 * π) := by
  intro x
  simp only [σ]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [mul_add, sin_add_nat_mul_two_pi]

/-- **The sine sums are uniformly bounded**: `|∑_{n=1}^N sin(n x)/n| ≤ 1 + π`. -/
theorem σ_bound (N : ℕ) (x : ℝ) : |σ N x| ≤ 1 + π := by
  have hp : (0 : ℝ) < 2 * π := by positivity
  set y := toIocMod hp (-π) x
  have hy : y ∈ Ioc (-π) (-π + 2 * π) := toIocMod_mem_Ioc hp (-π) x
  have hxy : σ N x = σ N y := by
    show σ N x = σ N (toIocMod hp (-π) x)
    rw [← self_sub_toIocDiv_zsmul hp (-π) x, (σ_periodic N).sub_zsmul_eq]
  rw [hxy]
  rcases lt_trichotomy y 0 with h | h | h
  · rw [show y = -(-y) by ring, σ_neg, abs_neg]
    exact σ_pos_bound N (by linarith) (by linarith [hy.1])
  · rw [h]; simp [σ]; positivity
  · exact σ_pos_bound N h (by linarith [hy.2])

end EulerianCert.Lebesgue
