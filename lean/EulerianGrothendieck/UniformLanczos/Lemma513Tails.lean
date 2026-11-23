import Mathlib

/-! # Manuscript 12, Lemma 5.13 (localisation): the first tail bound

First paragraph of the proof of Lemma 5.13 (Subsection 5.8). For an orthonormal family
`p_k` with the symmetric three-term recurrence (ul-rate-rec),
`x p_k = a_{k+1} p_{k+1} + a_k p_{k-1}`, one has `x^q p_k = Σ_l (J^q e_k)_l p_l`, hence
`∫ x^{2q} p_k² dμ = ‖J^q e_k‖²`. If every bond within distance `q+1` of `k` is at most
`r₀/2`, then `‖J^q e_k‖ ≤ r₀^q`, and Markov's inequality gives
`∫_{|x| ≥ s} p_k² dμ ≤ (r₀/s)^{2q}` (`tail_bound`). With `q = ⌊δM⌋` this is
`≤ e^{-cM}` (`geometric_le_exp`).

The orthonormal polynomials of `g_M` and their recurrence with `a_k = √β_k^{[M]}/M`
are classical (published results cited); here they enter as the premises `horth`, `hint`,
`hrec`. The argument below is the one of the manuscript. -/

namespace UniformLanczos.Lemma513Tails

open MeasureTheory Finset

/-- One application of the Jacobi operator: `(J v)_l = a_{l+1} v_{l+1} + a_l v_{l-1}`. -/
noncomputable def jstep (a v : ℕ → ℝ) (l : ℕ) : ℝ :=
  a (l + 1) * v (l + 1) + (if l = 0 then 0 else a l * v (l - 1))

/-- `J^n e_k`. -/
noncomputable def jpow (a : ℕ → ℝ) (k : ℕ) : ℕ → ℕ → ℝ
  | 0 => fun l => if l = k then 1 else 0
  | n + 1 => jstep a (jpow a k n)

theorem jpow_eq_zero_above (a : ℕ → ℝ) (k : ℕ) :
    ∀ n l, k + n < l → jpow a k n l = 0 := by
  intro n
  induction n with
  | zero => intro l hl; simp only [jpow]; rw [if_neg (by omega)]
  | succ n ih =>
    intro l hl
    simp only [jpow, jstep]
    rw [ih (l + 1) (by omega), if_neg (by omega), ih (l - 1) (by omega)]
    ring

theorem jpow_eq_zero_below (a : ℕ → ℝ) (k : ℕ) :
    ∀ n l, l + n < k → jpow a k n l = 0 := by
  intro n
  induction n with
  | zero => intro l hl; simp only [jpow]; rw [if_neg (by omega)]
  | succ n ih =>
    intro l hl
    simp only [jpow, jstep]
    rw [ih (l + 1) (by omega)]
    by_cases h0 : l = 0
    · rw [if_pos h0]; ring
    · rw [if_neg h0, ih (l - 1) (by omega)]; ring

/-! ## The expansion `x^n p_k = Σ_l (J^n e_k)_l p_l` -/

theorem expand_step (p : ℕ → ℝ → ℝ) (a : ℕ → ℝ)
    (hrec : ∀ l x, x * p l x = a (l + 1) * p (l + 1) x + (if l = 0 then 0 else a l * p (l - 1) x))
    (v : ℕ → ℝ) (S : ℕ) (hv : ∀ l, S ≤ l → v l = 0) (x : ℝ) :
    x * ∑ l ∈ range (S + 1), v l * p l x = ∑ l ∈ range (S + 1), jstep a v l * p l x := by
  have hL : x * ∑ l ∈ range (S + 1), v l * p l x =
      ∑ l ∈ range (S + 1), v l * (a (l + 1) * p (l + 1) x) +
        ∑ l ∈ range (S + 1), v l * (if l = 0 then 0 else a l * p (l - 1) x) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show x * (v l * p l x) = v l * (x * p l x) by ring, hrec]; ring
  have hR : ∑ l ∈ range (S + 1), jstep a v l * p l x =
      ∑ l ∈ range (S + 1), a (l + 1) * v (l + 1) * p l x +
        ∑ l ∈ range (S + 1), (if l = 0 then 0 else a l * v (l - 1)) * p l x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [jstep]; ring
  -- first pieces: `Σ_{l ≤ S} v_l a_{l+1} p_{l+1} = Σ_{l ≤ S} [l ≠ 0] a_l v_{l-1} p_l`
  have h1 : ∑ l ∈ range (S + 1), v l * (a (l + 1) * p (l + 1) x) =
      ∑ l ∈ range (S + 1), (if l = 0 then 0 else a l * v (l - 1)) * p l x := by
    rw [Finset.sum_range_succ, hv S le_rfl, Finset.sum_range_succ']
    simp only [if_pos, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    simp only [zero_mul, add_zero]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  -- second pieces: `Σ_{l ≤ S} v_l [l ≠ 0] a_l p_{l-1} = Σ_{l ≤ S} a_{l+1} v_{l+1} p_l`
  have h2 : ∑ l ∈ range (S + 1), v l * (if l = 0 then 0 else a l * p (l - 1) x) =
      ∑ l ∈ range (S + 1), a (l + 1) * v (l + 1) * p l x := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ, hv (S + 1) (by omega)]
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, if_pos, mul_zero, zero_mul,
      add_zero]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hL, hR, h1, h2, add_comm]

theorem expand_pow (p : ℕ → ℝ → ℝ) (a : ℕ → ℝ)
    (hrec : ∀ l x, x * p l x = a (l + 1) * p (l + 1) x + (if l = 0 then 0 else a l * p (l - 1) x))
    (k : ℕ) : ∀ n T, k + n + 1 ≤ T → ∀ x : ℝ,
      x ^ n * p k x = ∑ l ∈ range T, jpow a k n l * p l x := by
  intro n
  induction n with
  | zero =>
    intro T hT x
    simp only [pow_zero, one_mul, jpow]
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _ hl; rw [if_neg hl, zero_mul]
    · intro hk; exact absurd (Finset.mem_range.mpr (by omega)) hk
  | succ n ih =>
    intro T hT x
    obtain ⟨S, rfl⟩ : ∃ S, T = S + 1 := ⟨T - 1, by omega⟩
    rw [pow_succ, mul_comm (x ^ n) x, mul_assoc, ih (S + 1) (by omega) x,
      expand_step p a hrec (jpow a k n) S
        (fun l hl => jpow_eq_zero_above a k n l (by omega)) x]
    rfl

/-! ## Orthonormal expansions -/

theorem integral_sq_expansion (μ : Measure ℝ) (p : ℕ → ℝ → ℝ)
    (horth : ∀ l m, ∫ x, p l x * p m x ∂μ = if l = m then 1 else 0)
    (hint : ∀ l m, Integrable (fun x => p l x * p m x) μ) (c : ℕ → ℝ) (T : ℕ) :
    ∫ x, (∑ l ∈ range T, c l * p l x) ^ 2 ∂μ = ∑ l ∈ range T, c l ^ 2 := by
  have hsq : ∀ x, (∑ l ∈ range T, c l * p l x) ^ 2 =
      ∑ l ∈ range T, ∑ m ∈ range T, (c l * c m) * (p l x * p m x) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  simp_rw [hsq]
  rw [integral_finset_sum _ (fun l _ => integrable_finset_sum _
    (fun m _ => (hint l m).const_mul _))]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [integral_finset_sum _ (fun m _ => (hint l m).const_mul _)]
  simp_rw [integral_const_mul, horth]
  rw [Finset.sum_eq_single l]
  · simp [sq]
  · intro m _ hm; rw [if_neg (Ne.symm hm), mul_zero]
  · intro h; exact absurd hl h

theorem integrable_sq_expansion (μ : Measure ℝ) (p : ℕ → ℝ → ℝ)
    (hint : ∀ l m, Integrable (fun x => p l x * p m x) μ) (c : ℕ → ℝ) (T : ℕ) :
    Integrable (fun x => (∑ l ∈ range T, c l * p l x) ^ 2) μ := by
  have hsq : (fun x => (∑ l ∈ range T, c l * p l x) ^ 2) =
      fun x => ∑ l ∈ range T, ∑ m ∈ range T, (c l * c m) * (p l x * p m x) := by
    funext x
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hsq]
  exact integrable_finset_sum _ fun l _ => integrable_finset_sum _ fun m _ =>
    (hint l m).const_mul _

/-! ## The shift bound `‖J^n e_k‖ ≤ r₀^n` -/

/-- If the bonds within distance `q+1` of `k` are at most `r₀/2`, then for `n ≤ q`,
`Σ_{l < B} (J^n e_k)_l² ≤ r₀^{2n}` with `B = k + q + 2`. -/
theorem jpow_norm_sq (a : ℕ → ℝ) (k q : ℕ) {r₀ : ℝ}
    (hbond : ∀ m, k ≤ m + q + 1 → m ≤ k + q + 1 → |a m| ≤ r₀ / 2) :
    ∀ n, n ≤ q → ∑ l ∈ range (k + q + 2), jpow a k n l ^ 2 ≤ (r₀ ^ 2) ^ n := by
  intro n
  induction n with
  | zero =>
    intro _
    simp only [jpow, pow_zero]
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _ hl; simp [hl]
    · intro hk; exact absurd (Finset.mem_range.mpr (by omega)) hk
  | succ n ih =>
    intro hn
    set v := jpow a k n
    set B := k + q + 2
    have habove : ∀ l, k + n < l → v l = 0 := jpow_eq_zero_above a k n
    have hbelow : ∀ l, l + n < k → v l = 0 := jpow_eq_zero_below a k n
    have hr : ∀ m, v m ≠ 0 → |a m| ≤ r₀ / 2 ∧ |a (m + 1)| ≤ r₀ / 2 := by
      intro m hm
      have h1 : ¬ (k + n < m) := fun h => hm (habove m h)
      have h2 : ¬ (m + n < k) := fun h => hm (hbelow m h)
      exact ⟨hbond m (by omega) (by omega), hbond (m + 1) (by omega) (by omega)⟩
    -- pointwise: `(a_{l+1} v_{l+1})² ≤ (r₀²/4) v_{l+1}²` and the same for `a_l v_{l-1}`
    have hpt1 : ∀ m, (a m * v m) ^ 2 ≤ r₀ ^ 2 / 4 * v m ^ 2 := by
      intro m
      by_cases hm : v m = 0
      · rw [hm]; simp
      · have ha := (hr m hm).1
        rw [mul_pow]
        have : a m ^ 2 ≤ r₀ ^ 2 / 4 := by
          have h0 : 0 ≤ |a m| := abs_nonneg _
          rw [← sq_abs]; nlinarith
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have hpt2 : ∀ m, (a (m + 1) * v m) ^ 2 ≤ r₀ ^ 2 / 4 * v m ^ 2 := by
      intro m
      by_cases hm : v m = 0
      · rw [hm]; simp
      · have ha := (hr m hm).2
        rw [mul_pow]
        have : a (m + 1) ^ 2 ≤ r₀ ^ 2 / 4 := by
          have h0 : 0 ≤ |a (m + 1)| := abs_nonneg _
          rw [← sq_abs]; nlinarith
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have hterm : ∀ l, jstep a v l ^ 2 ≤
        r₀ ^ 2 / 2 * v (l + 1) ^ 2 + r₀ ^ 2 / 2 * (if l = 0 then 0 else v (l - 1) ^ 2) := by
      intro l
      simp only [jstep]
      by_cases h0 : l = 0
      · simp only [h0, if_pos, add_zero, zero_add]
        have := hpt1 1
        nlinarith [sq_nonneg (v 1)]
      · simp only [if_neg h0]
        have e1 := hpt1 (l + 1)
        have e2 : (a l * v (l - 1)) ^ 2 ≤ r₀ ^ 2 / 4 * v (l - 1) ^ 2 := by
          have := hpt2 (l - 1)
          rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)] at this
        nlinarith [sq_nonneg (a (l + 1) * v (l + 1) - a l * v (l - 1))]
    have hshift1 : ∑ l ∈ range B, v (l + 1) ^ 2 ≤ ∑ l ∈ range B, v l ^ 2 := by
      have h := Finset.sum_range_succ' (fun l => v l ^ 2) B
      rw [Finset.sum_range_succ, habove B (by omega)] at h
      have : 0 ≤ v 0 ^ 2 := sq_nonneg _
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
      linarith
    have hshift2 : ∑ l ∈ range B, (if l = 0 then 0 else v (l - 1) ^ 2) ≤
        ∑ l ∈ range B, v l ^ 2 := by
      have hB : B = (B - 1) + 1 := by omega
      rw [hB, Finset.sum_range_succ', Finset.sum_range_succ]
      simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, if_pos, add_zero]
      have : 0 ≤ v (B - 1) ^ 2 := sq_nonneg _
      linarith
    calc ∑ l ∈ range B, jpow a k (n + 1) l ^ 2
        = ∑ l ∈ range B, jstep a v l ^ 2 := rfl
      _ ≤ ∑ l ∈ range B, (r₀ ^ 2 / 2 * v (l + 1) ^ 2 +
            r₀ ^ 2 / 2 * (if l = 0 then 0 else v (l - 1) ^ 2)) :=
          Finset.sum_le_sum fun l _ => hterm l
      _ = r₀ ^ 2 / 2 * ∑ l ∈ range B, v (l + 1) ^ 2 +
            r₀ ^ 2 / 2 * ∑ l ∈ range B, (if l = 0 then 0 else v (l - 1) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ r₀ ^ 2 / 2 * ∑ l ∈ range B, v l ^ 2 + r₀ ^ 2 / 2 * ∑ l ∈ range B, v l ^ 2 := by
          gcongr
      _ = r₀ ^ 2 * ∑ l ∈ range B, v l ^ 2 := by ring
      _ ≤ r₀ ^ 2 * (r₀ ^ 2) ^ n := mul_le_mul_of_nonneg_left (ih (by omega)) (sq_nonneg _)
      _ = (r₀ ^ 2) ^ (n + 1) := by ring

/-! ## The tail bound -/

/-- **Lemma 5.13, first bound.** `∫_{|x| ≥ s} p_k² dμ ≤ (r₀/s)^{2q}` whenever every bond within
distance `q+1` of `k` is at most `r₀/2`. -/
theorem tail_bound (μ : Measure ℝ) (p : ℕ → ℝ → ℝ) (a : ℕ → ℝ)
    (horth : ∀ l m, ∫ x, p l x * p m x ∂μ = if l = m then 1 else 0)
    (hint : ∀ l m, Integrable (fun x => p l x * p m x) μ)
    (hrec : ∀ l x, x * p l x = a (l + 1) * p (l + 1) x + (if l = 0 then 0 else a l * p (l - 1) x))
    (k q : ℕ) {r₀ s : ℝ} (hs : 0 < s)
    (hbond : ∀ m, k ≤ m + q + 1 → m ≤ k + q + 1 → |a m| ≤ r₀ / 2) :
    ∫ x in {x : ℝ | s ≤ |x|}, p k x ^ 2 ∂μ ≤ (r₀ / s) ^ (2 * q) := by
  set B := k + q + 2
  set c := jpow a k q
  have hexp : ∀ x, x ^ q * p k x = ∑ l ∈ range B, c l * p l x :=
    expand_pow p a hrec k q B (by omega)
  have hmom : ∫ x, (x ^ q * p k x) ^ 2 ∂μ = ∑ l ∈ range B, c l ^ 2 := by
    simp_rw [hexp]; exact integral_sq_expansion μ p horth hint c B
  have hmomint : Integrable (fun x => (x ^ q * p k x) ^ 2) μ := by
    simp_rw [hexp]; exact integrable_sq_expansion μ p hint c B
  have hnorm : ∑ l ∈ range B, c l ^ 2 ≤ (r₀ ^ 2) ^ q := jpow_norm_sq a k q hbond q le_rfl
  have hs2q : 0 < s ^ (2 * q) := pow_pos hs _
  have hmeas : MeasurableSet {x : ℝ | s ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hpk : Integrable (fun x => p k x ^ 2) μ := by
    simpa [sq] using hint k k
  have hpt : ∀ x ∈ {x : ℝ | s ≤ |x|}, p k x ^ 2 ≤ (x ^ q * p k x) ^ 2 / s ^ (2 * q) := by
    intro x hx
    have hx' : s ≤ |x| := hx
    have h3 : s ^ 2 ≤ x ^ 2 := by rw [← sq_abs x]; exact pow_le_pow_left₀ hs.le hx' 2
    have hxq : s ^ (2 * q) ≤ (x ^ q) ^ 2 := by
      calc s ^ (2 * q) = (s ^ 2) ^ q := pow_mul s 2 q
        _ ≤ (x ^ 2) ^ q := pow_le_pow_left₀ (sq_nonneg s) h3 q
        _ = (x ^ q) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [le_div_iff₀ hs2q, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hxq (sq_nonneg (p k x))]
  calc ∫ x in {x : ℝ | s ≤ |x|}, p k x ^ 2 ∂μ
      ≤ ∫ x in {x : ℝ | s ≤ |x|}, (x ^ q * p k x) ^ 2 / s ^ (2 * q) ∂μ :=
        setIntegral_mono_on hpk.integrableOn (hmomint.div_const _).integrableOn hmeas hpt
    _ ≤ ∫ x, (x ^ q * p k x) ^ 2 / s ^ (2 * q) ∂μ :=
        setIntegral_le_integral (hmomint.div_const _)
          (Filter.Eventually.of_forall fun x => by positivity)
    _ = (∑ l ∈ range B, c l ^ 2) / s ^ (2 * q) := by rw [integral_div, hmom]
    _ ≤ (r₀ ^ 2) ^ q / s ^ (2 * q) := div_le_div_of_nonneg_right hnorm hs2q.le
    _ = (r₀ / s) ^ (2 * q) := by rw [div_pow, pow_mul, pow_mul]

/-- With `q = ⌊δM⌋` and `ρ = r₀/s ∈ (0,1)`: `ρ^{2q} ≤ e^{-cM}` for `δM ≥ 2`,
with `c = -δ log ρ > 0`. -/
theorem geometric_le_exp {ρ δ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hδ : 0 < δ)
    (hM : 2 ≤ δ * M) :
    0 < -δ * Real.log ρ ∧ ρ ^ (2 * ⌊δ * M⌋₊) ≤ Real.exp (-(-δ * Real.log ρ) * M) := by
  have hlog : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  refine ⟨by nlinarith, ?_⟩
  have hfl : δ * M - 1 ≤ (⌊δ * M⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (δ * M); linarith
  rw [← Real.exp_log (pow_pos hρ0 _), Real.log_pow]
  apply Real.exp_le_exp.mpr
  push_cast
  have h1 : δ * M / 2 ≤ (⌊δ * M⌋₊ : ℝ) := by linarith
  nlinarith

end UniformLanczos.Lemma513Tails

#print axioms UniformLanczos.Lemma513Tails.jpow_eq_zero_above
#print axioms UniformLanczos.Lemma513Tails.jpow_eq_zero_below
#print axioms UniformLanczos.Lemma513Tails.expand_step
#print axioms UniformLanczos.Lemma513Tails.expand_pow
#print axioms UniformLanczos.Lemma513Tails.integral_sq_expansion
#print axioms UniformLanczos.Lemma513Tails.integrable_sq_expansion
#print axioms UniformLanczos.Lemma513Tails.jpow_norm_sq
#print axioms UniformLanczos.Lemma513Tails.tail_bound
#print axioms UniformLanczos.Lemma513Tails.geometric_le_exp
