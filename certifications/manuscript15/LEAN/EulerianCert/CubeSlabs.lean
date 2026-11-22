/-
# V001 Lemma 3.14, Eq. (79), first equality (Laplace): cube slabs and Eulerian numbers

For `n ≥ 1`, `1 ≤ k ≤ n`:
  `Vol_n {x ∈ [0,1]^n : k − 1 ≤ x₁ + ⋯ + xₙ ≤ k} = E(n, k−1)/n!`,
with `E` the Eulerian triangle of `Bracket` (defined by its recurrence).  Proof:
* the truncated powers `x₊^m` (`x₊^0 = 𝟙[x ≥ 0]`) and `∫₀¹ (c − t)₊^m dt = ((c)₊^{m+1} − (c−1)₊^{m+1})/(m+1)`;
* the **Irwin–Hall formula** `Vol_n {x ∈ [0,1]^n : ∑ x ≤ s} = (1/n!) ∑_j (−1)^j C(n,j) (s − j)₊^n`, by
  induction on `n` (Fubini through `MeasurableEquiv.piFinSuccAbove`);
* a Pascal shift turns the slab into `U_n(k)/n!`, `U_m(x) = ∑_j (−1)^j C(m+1,j) (x − j)₊^m`;
* `U_{m+1}(x) = x U_m(x) + (m + 2 − x) U_m(x − 1)` (Cox–de Boor), `U_m = 0` on `[m+1, ∞)`, so
  `U_n(k+1)` satisfies the Eulerian recurrence and initial values: `E(n,k) = U_n(k+1)`.
-/
import EulerianCert.Bracket
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Real Finset MeasureTheory Set Filter Topology

noncomputable section

namespace EulerianCert.CubeSlabs

/-! ### Truncated powers -/

/-- `x₊^m`, with `x₊^0 = 𝟙[x ≥ 0]`. -/
def tp (m : ℕ) (x : ℝ) : ℝ := if 0 ≤ x then x ^ m else 0

lemma tp_succ (m : ℕ) (x : ℝ) : tp (m + 1) x = x * tp m x := by
  unfold tp; split_ifs <;> ring

lemma tp_of_neg {m : ℕ} {x : ℝ} (hx : x < 0) : tp m x = 0 := by
  unfold tp; rw [if_neg (not_le.mpr hx)]

lemma tp_of_nonneg {m : ℕ} {x : ℝ} (hx : 0 ≤ x) : tp m x = x ^ m := by
  unfold tp; rw [if_pos hx]

lemma tp_nonneg (m : ℕ) (x : ℝ) : 0 ≤ tp m x := by
  unfold tp; split_ifs with h
  · exact pow_nonneg h m
  · exact le_rfl

lemma tp_zero_eq {m : ℕ} (hm : 1 ≤ m) : tp m 0 = 0 := by
  rw [tp_of_nonneg le_rfl, zero_pow (by omega)]

lemma tp_mono (m : ℕ) : Monotone (tp m) := by
  intro x y hxy
  by_cases hx : 0 ≤ x
  · rw [tp_of_nonneg hx, tp_of_nonneg (hx.trans hxy)]
    exact pow_le_pow_left₀ hx hxy m
  · rw [tp_of_neg (not_le.mp hx)]; exact tp_nonneg m y

lemma measurable_tp (m : ℕ) : Measurable (tp m) :=
  Measurable.ite measurableSet_Ici (measurable_id.pow_const m) measurable_const

lemma tp_eq_max {m : ℕ} (hm : 1 ≤ m) (x : ℝ) : tp m x = (max x 0) ^ m := by
  by_cases hx : 0 ≤ x
  · rw [tp_of_nonneg hx, max_eq_left hx]
  · rw [tp_of_neg (not_le.mp hx), max_eq_right (not_le.mp hx).le, zero_pow (by omega)]

lemma continuous_tp {m : ℕ} (hm : 1 ≤ m) : Continuous (tp m) := by
  rw [show tp m = fun x => (max x 0) ^ m from funext (tp_eq_max hm)]
  fun_prop

lemma hasDerivAt_tp (m : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (tp (m + 1)) ((m + 1) * tp m x) x := by
  rcases lt_or_gt_of_ne hx with h | h
  · have heq : tp (m + 1) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with y hy
      exact tp_of_neg hy
    rw [tp_of_neg h, mul_zero]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
  · have heq : tp (m + 1) =ᶠ[𝓝 x] fun y => y ^ (m + 1) := by
      filter_upwards [Ioi_mem_nhds h] with y hy
      exact tp_of_nonneg hy.le
    rw [tp_of_nonneg h.le]
    have := hasDerivAt_pow (m + 1) x
    refine HasDerivAt.congr_of_eventuallyEq ?_ heq
    convert this using 1; push_cast; ring

/-- `∫₀¹ (c − t)₊^m dt = (c₊^{m+1} − (c−1)₊^{m+1})/(m+1)`. -/
lemma integral_tp (m : ℕ) (c : ℝ) :
    ∫ t in (0 : ℝ)..1, tp m (c - t) = (tp (m + 1) c - tp (m + 1) (c - 1)) / (m + 1) := by
  have hm : (0 : ℝ) < m + 1 := by positivity
  have hF := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t => -tp (m + 1) (c - t) / (m + 1)) (fun t => tp m (c - t)) zero_le_one
    (s := {c}) (countable_singleton c)
    (((continuous_tp (by omega)).comp (continuous_const.sub continuous_id)).neg.div_const
      _).continuousOn
    (fun t ht => by
      have hne : c - t ≠ 0 := sub_ne_zero.mpr (fun h => ht.2 (by rw [h]; rfl))
      have := ((hasDerivAt_tp m hne).comp t ((hasDerivAt_id t).const_sub c)).neg.div_const (m + 1)
      exact this.congr_deriv (by field_simp))
    ((tp_mono m).comp_antitone (fun a b h => by linarith)).intervalIntegrable
  rw [hF]
  simp only [sub_zero]
  field_simp
  ring

/-! ### A Pascal shift -/

lemma pascal_shift (n : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ range (n + 1), (-1 : ℝ) ^ j * (n.choose j) * (f j - f (j + 1)) =
      ∑ j ∈ range (n + 2), (-1 : ℝ) ^ j * ((n + 1).choose j) * f j := by
  have hB : ∑ j ∈ range (n + 2), (-1 : ℝ) ^ j * (n.choose j) * f j =
      ∑ j ∈ range (n + 1), (-1 : ℝ) ^ j * (n.choose j) * f j := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self]; simp
  have hB' : ∑ j ∈ range (n + 2), (-1 : ℝ) ^ j * (n.choose j) * f j =
      ∑ j ∈ range (n + 1), (-1 : ℝ) ^ (j + 1) * (n.choose (j + 1)) * f (j + 1) + f 0 := by
    rw [Finset.sum_range_succ']; simp
  rw [Finset.sum_range_succ' (fun j => (-1 : ℝ) ^ j * (((n + 1).choose j : ℕ) : ℝ) * f j)]
  have hsplit : ∀ j ∈ range (n + 1), (-1 : ℝ) ^ (j + 1) * (((n + 1).choose (j + 1) : ℕ) : ℝ) *
      f (j + 1) = -((-1 : ℝ) ^ j * (n.choose j) * f (j + 1)) +
        (-1 : ℝ) ^ (j + 1) * (n.choose (j + 1)) * f (j + 1) := by
    intro j _; rw [Nat.choose_succ_succ']; push_cast; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have h1 : ∑ j ∈ range (n + 1), (-1 : ℝ) ^ j * (n.choose j) * (f j - f (j + 1)) =
      ∑ j ∈ range (n + 1), (-1 : ℝ) ^ j * (n.choose j) * f j -
        ∑ j ∈ range (n + 1), (-1 : ℝ) ^ j * (n.choose j) * f (j + 1) := by
    rw [← Finset.sum_sub_distrib]; congr 1; funext j; ring
  rw [h1]
  simp only [Nat.choose_zero_right, pow_zero, Nat.cast_one, one_mul]
  linarith [hB, hB']

/-! ### The Irwin–Hall formula -/

/-- `Vol_n {x ∈ [0,1]^n : ∑ x ≤ s}` in closed form. -/
def IH (n : ℕ) (s : ℝ) : ℝ :=
  (1 / (n.factorial : ℝ)) * ∑ j ∈ range (n + 1), (-1 : ℝ) ^ j * (n.choose j) * tp n (s - j)

/-- The set `{x ∈ [0,1]^n : ∑ x ≤ s}`. -/
def S (n : ℕ) (s : ℝ) : Set (Fin n → ℝ) := {x | (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧ ∑ i, x i ≤ s}

lemma measurableSet_S (n : ℕ) (s : ℝ) : MeasurableSet (S n s) := by
  have h1 : MeasurableSet {x : Fin n → ℝ | ∀ i, x i ∈ Icc (0 : ℝ) 1} := by
    rw [show {x : Fin n → ℝ | ∀ i, x i ∈ Icc (0 : ℝ) 1} = ⋂ i, (fun x => x i) ⁻¹' Icc 0 1 by
      ext x; simp]
    exact MeasurableSet.iInter (fun i => measurableSet_Icc.preimage (measurable_pi_apply i))
  have h2 : MeasurableSet {x : Fin n → ℝ | ∑ i, x i ≤ s} :=
    measurableSet_le (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)) measurable_const
  exact h1.inter h2

lemma S_subset_cube (n : ℕ) (s : ℝ) : S n s ⊆ Set.pi univ (fun _ => Icc (0 : ℝ) 1) :=
  fun x hx i _ => hx.1 i

lemma volume_S_le (n : ℕ) (s : ℝ) : volume (S n s) ≤ 1 := by
  calc volume (S n s) ≤ volume (Set.pi univ (fun _ : Fin n => Icc (0 : ℝ) 1)) :=
        measure_mono (S_subset_cube n s)
    _ = 1 := by rw [volume_pi_pi]; simp

lemma IH_succ (n : ℕ) (s : ℝ) : ∫ t in (0 : ℝ)..1, IH n (s - t) = IH (n + 1) s := by
  unfold IH
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finset_sum]
  · have : ∀ j ∈ range (n + 1), ∫ t in (0 : ℝ)..1, (-1 : ℝ) ^ j * (n.choose j) * tp n (s - t - j)
        = (-1 : ℝ) ^ j * (n.choose j) * ((tp (n + 1) (s - j) - tp (n + 1) (s - (j + 1 : ℕ))) /
          (n + 1)) := by
      intro j _
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [show (fun t => tp n (s - t - j)) = fun t => tp n ((s - j) - t) by funext t; ring_nf,
        integral_tp]
      congr 3; push_cast; ring
    rw [Finset.sum_congr rfl this]
    have hp := pascal_shift n (fun j => tp (n + 1) (s - j))
    rw [show ∑ j ∈ range (n + 1), (-1 : ℝ) ^ j * (n.choose j) *
        ((tp (n + 1) (s - j) - tp (n + 1) (s - (j + 1 : ℕ))) / (n + 1)) =
        (∑ j ∈ range (n + 1), (-1 : ℝ) ^ j * (n.choose j) *
          (tp (n + 1) (s - j) - tp (n + 1) (s - (j + 1 : ℕ)))) / (n + 1) by
      rw [Finset.sum_div]; congr 1; funext j; ring, hp, Nat.factorial_succ]
    push_cast
    field_simp
  · intro j _
    exact (((tp_mono n).comp_antitone (fun a b h => by linarith)).intervalIntegrable).const_mul _

lemma IH_nonneg (n : ℕ) (s : ℝ) : 0 ≤ IH n s := by
  induction n generalizing s with
  | zero => unfold IH; simp only [zero_add, Finset.sum_range_one]; simp [tp_nonneg]
  | succ n ih =>
    rw [← IH_succ]
    exact intervalIntegral.integral_nonneg zero_le_one (fun t _ => ih _)

/-- **The Irwin–Hall formula**. -/
theorem volume_S (n : ℕ) (s : ℝ) : volume (S n s) = ENNReal.ofReal (IH n s) := by
  induction n generalizing s with
  | zero =>
    unfold IH S
    simp only [Finset.univ_eq_empty, Finset.sum_empty, IsEmpty.forall_iff, true_and,
      Nat.factorial_zero, Nat.cast_one, div_one, zero_add, Finset.sum_range_one, pow_zero,
      Nat.choose_self, one_mul, CharP.cast_eq_zero, sub_zero]
    by_cases hs : 0 ≤ s
    · rw [tp_of_nonneg hs, pow_zero, show {x : Fin 0 → ℝ | (0 : ℝ) ≤ s} = univ by
        ext x; simp [hs]]
      simp [volume_pi]
    · rw [tp_of_neg (not_le.mp hs), show {x : Fin 0 → ℝ | (0 : ℝ) ≤ s} = ∅ by
        ext x; simp [hs]]
      simp
  | succ n ih =>
    -- Fubini through the first coordinate
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hmp : MeasurePreserving e volume (volume.prod volume) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    set T : Set (ℝ × (Fin n → ℝ)) := {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ S n (s - p.1)}
    have hT : MeasurableSet T := by
      have h1 : MeasurableSet {p : ℝ × (Fin n → ℝ) | p.1 ∈ Icc (0 : ℝ) 1} :=
        measurableSet_Icc.preimage measurable_fst
      have h2 : MeasurableSet {p : ℝ × (Fin n → ℝ) | ∀ i, p.2 i ∈ Icc (0 : ℝ) 1} := by
        rw [show {p : ℝ × (Fin n → ℝ) | ∀ i, p.2 i ∈ Icc (0 : ℝ) 1} =
          ⋂ i, (fun p : ℝ × (Fin n → ℝ) => p.2 i) ⁻¹' Icc 0 1 by ext p; simp]
        exact MeasurableSet.iInter (fun i =>
          measurableSet_Icc.preimage ((measurable_pi_apply i).comp measurable_snd))
      have h3 : MeasurableSet {p : ℝ × (Fin n → ℝ) | ∑ i, p.2 i ≤ s - p.1} :=
        measurableSet_le (Finset.measurable_sum _ (fun i _ =>
          (measurable_pi_apply i).comp measurable_snd)) (measurable_const.sub measurable_fst)
      rw [show T = {p : ℝ × (Fin n → ℝ) | p.1 ∈ Icc (0 : ℝ) 1} ∩
          ({p : ℝ × (Fin n → ℝ) | ∀ i, p.2 i ∈ Icc (0 : ℝ) 1} ∩
            {p : ℝ × (Fin n → ℝ) | ∑ i, p.2 i ≤ s - p.1}) by
        ext p; simp only [T, S, Set.mem_setOf_eq, Set.mem_inter_iff]]
      exact h1.inter (h2.inter h3)
    have hpre : S (n + 1) s = e ⁻¹' T := by
      ext x
      rw [Set.mem_preimage, show e x = (x 0, Fin.removeNth 0 x) from rfl]
      simp only [S, T, Set.mem_setOf_eq, Fin.removeNth_apply]
      rw [Fin.forall_iff_succAbove 0, Fin.sum_univ_succAbove _ 0]
      constructor
      · rintro ⟨⟨h0, hi⟩, hs⟩; exact ⟨h0, hi, by linarith⟩
      · rintro ⟨h0, hi, hs⟩; exact ⟨⟨h0, hi⟩, by linarith⟩
    rw [hpre, hmp.measure_preimage hT.nullMeasurableSet, Measure.prod_apply hT]
    have hslice : ∀ t : ℝ, volume (Prod.mk t ⁻¹' T) =
        (Icc (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal (IH n (s - t))) t := by
      intro t
      by_cases ht : t ∈ Icc (0 : ℝ) 1
      · rw [indicator_of_mem ht, ← ih (s - t)]
        congr 1; ext y
        simp only [T, Set.mem_preimage, Set.mem_setOf_eq]
        exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩
      · rw [indicator_of_notMem ht]
        rw [show Prod.mk t ⁻¹' T = ∅ by
          ext y
          simp only [T, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
            not_and]
          intro h; exact absurd h ht]
        simp
    simp_rw [hslice]
    rw [lintegral_indicator measurableSet_Icc]
    have hnn : ∀ t, 0 ≤ IH n (s - t) := fun t => IH_nonneg n _
    have hint : IntegrableOn (fun t => IH n (s - t)) (Icc (0 : ℝ) 1) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      have : IntervalIntegrable (fun t => IH n (s - t)) volume 0 1 := by
        have hs : ∀ j ∈ range (n + 1), IntervalIntegrable
            (fun t => (-1 : ℝ) ^ j * (n.choose j) * tp n (s - t - j)) volume 0 1 :=
          fun j _ => (((tp_mono n).comp_antitone (fun a b h => by linarith)).intervalIntegrable).const_mul _
        have := (IntervalIntegrable.sum (range (n + 1)) hs).const_mul (1 / (n.factorial : ℝ))
        refine this.congr (fun t _ => ?_)
        simp only [IH, Finset.sum_apply]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (fun t => hnn t)),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, IH_succ]

/-! ### Cox–de Boor and the Eulerian numbers -/

/-- `U_m(x) = ∑_{j=0}^{m+1} (−1)^j C(m+1,j) (x − j)₊^m` (`m!` times the cardinal B-spline). -/
def U (m : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (m + 2), (-1 : ℝ) ^ j * ((m + 1).choose j) * tp m (x - j)

/-- The slab difference of the Irwin–Hall formula: `IH_n(x) − IH_n(x − 1) = U_n(x)/n!`. -/
lemma IH_sub (n : ℕ) (x : ℝ) : IH n x - IH n (x - 1) = U n x / n.factorial := by
  unfold IH U
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have h : ∀ j ∈ range (n + 1), (-1 : ℝ) ^ j * (n.choose j) * tp n (x - j) -
      (-1 : ℝ) ^ j * (n.choose j) * tp n (x - 1 - j) =
      (-1 : ℝ) ^ j * (n.choose j) * (tp n (x - j) - tp n (x - ((j + 1 : ℕ) : ℝ))) := by
    intro j _; rw [show x - ((j + 1 : ℕ) : ℝ) = x - 1 - j by push_cast; ring]; ring
  rw [Finset.sum_congr rfl h, pascal_shift n (fun j => tp n (x - j))]
  ring

lemma choose_identity (m j : ℕ) (x : ℝ) :
    ((m + 2).choose (j + 1) : ℝ) * (x - (j + 1)) =
      x * ((m + 1).choose (j + 1)) + (x - (m + 2)) * ((m + 1).choose j) := by
  have h1 : ((m + 2).choose (j + 1) : ℝ) = (m + 1).choose j + (m + 1).choose (j + 1) := by
    rw [Nat.choose_succ_succ']; push_cast; ring
  have h2 : ((m + 2).choose (j + 1) : ℝ) * (j + 1) = (m + 2) * (m + 1).choose j := by
    have := Nat.add_one_mul_choose_eq (m + 1) j
    have h : ((m + 1 + 1 : ℕ) : ℝ) * ((m + 1).choose j : ℕ) =
        (((m + 1 + 1).choose (j + 1) : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h
    linarith
  linear_combination x * h1 - h2

/-- **Cox–de Boor**: `U_{m+1}(x) = x U_m(x) + (m + 2 − x) U_m(x − 1)`. -/
theorem U_succ (m : ℕ) (x : ℝ) : U (m + 1) x = x * U m x + (m + 2 - x) * U m (x - 1) := by
  have hA : U m x = ∑ j ∈ range (m + 2),
      (-1 : ℝ) ^ (j + 1) * ((m + 1).choose (j + 1)) * tp m (x - ((j + 1 : ℕ) : ℝ)) + tp m x := by
    unfold U
    rw [Finset.sum_range_succ' _ (m + 1), Finset.sum_range_succ _ (m + 1),
      Nat.choose_eq_zero_of_lt (show m + 1 < m + 1 + 1 by omega)]
    simp
  have hB : U m (x - 1) = ∑ j ∈ range (m + 2),
      (-1 : ℝ) ^ j * ((m + 1).choose j) * tp m (x - ((j + 1 : ℕ) : ℝ)) := by
    unfold U
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show x - ((j + 1 : ℕ) : ℝ) = x - 1 - j by push_cast; ring]
  rw [hA, hB]
  unfold U
  rw [show m + 1 + 2 = (m + 2) + 1 by ring, Finset.sum_range_succ']
  have hterm : ∀ j ∈ range (m + 2), (-1 : ℝ) ^ (j + 1) * ((m + 1 + 1).choose (j + 1) : ℕ) *
      tp (m + 1) (x - ((j + 1 : ℕ) : ℝ)) =
      x * ((-1 : ℝ) ^ (j + 1) * ((m + 1).choose (j + 1)) * tp m (x - ((j + 1 : ℕ) : ℝ))) +
      (m + 2 - x) * ((-1 : ℝ) ^ j * ((m + 1).choose j) * tp m (x - ((j + 1 : ℕ) : ℝ))) := by
    intro j _
    rw [tp_succ]
    have hc := choose_identity m j x
    push_cast at hc ⊢
    rw [show m + 1 + 1 = m + 2 by ring]
    linear_combination (-1 : ℝ) ^ (j + 1) * tp m (x - (j + 1)) * hc
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, CharP.cast_eq_zero,
    sub_zero, tp_succ]
  ring

lemma U_zero_eq (x : ℝ) : U 0 x = tp 0 x - tp 0 (x - 1) := by
  unfold U; simp [Finset.sum_range_succ]; ring

/-- `U_m` vanishes on `[m + 1, ∞)`. -/
lemma U_eq_zero_of_ge (m : ℕ) {x : ℝ} (hx : (m : ℝ) + 1 ≤ x) : U m x = 0 := by
  induction m generalizing x with
  | zero =>
    rw [U_zero_eq, tp_of_nonneg (by push_cast at hx; linarith),
      tp_of_nonneg (by push_cast at hx; linarith)]
    simp
  | succ m ih =>
    push_cast at hx
    rw [U_succ, ih (by linarith), ih (by linarith)]; ring

/-- `U_m(0) = 0` for `m ≥ 1`. -/
lemma U_at_zero {m : ℕ} (hm : 1 ≤ m) : U m 0 = 0 := by
  unfold U
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; simp [tp_zero_eq hm]
  · rw [tp_of_neg (by have : (0 : ℝ) < j := by exact_mod_cast h
                      linarith), mul_zero]

/-- **The Eulerian numbers in closed form**: `E(n,k) = U_n(k+1) =
∑_{j=0}^{k+1} (−1)^j C(n+1,j) (k+1−j)^n` for `n ≥ 1`. -/
theorem E_eq_U {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : (EulerianCert.Bracket.E n k : ℝ) = U n (k + 1) := by
  induction n, hn using Nat.le_induction generalizing k with
  | base =>
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      rw [EulerianCert.Bracket.E_one_zero]
      show ((1 : ℕ) : ℝ) = U (0 + 1) (((0 : ℕ) : ℝ) + 1)
      rw [U_succ, U_eq_zero_of_ge 0 (by simp), U_zero_eq]
      norm_num
      rw [tp_of_nonneg le_rfl, tp_of_neg (by norm_num)]
      norm_num
    · rw [EulerianCert.Bracket.E_eq_zero_of_le h, U_eq_zero_of_ge 1 (by
        have : (1 : ℝ) ≤ k := by exact_mod_cast h
        push_cast; linarith)]
      simp
  | succ n hn ih =>
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      rw [EulerianCert.Bracket.E_succ_zero hn, ih 0]
      push_cast
      rw [U_succ, show ((0 : ℝ) + 1 - 1) = 0 by ring, U_at_zero hn]
      ring
    · rcases le_or_gt k (n + 1) with hk | hk
      · rw [EulerianCert.Bracket.E_succ hn h]
        push_cast [Nat.cast_sub hk]
        have h2 := ih (k - 1)
        rw [show (((k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) by push_cast [Nat.cast_sub h]; ring] at h2
        rw [ih k, h2, U_succ, show (k : ℝ) + 1 - 1 = k by ring]
        ring
      · rw [EulerianCert.Bracket.E_eq_zero_of_le (by omega), U_eq_zero_of_ge (n + 1) (by
          have : ((n + 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
          push_cast at this ⊢; linarith)]
        simp

/-! ### The slab volume (Laplace) -/

/-- The slab `{x ∈ [0,1]^n : k − 1 ≤ ∑ x ≤ k}`. -/
def Slab (n k : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧ (k : ℝ) - 1 ≤ ∑ i, x i ∧ ∑ i, x i ≤ k}

/-- `{x ∈ [0,1]^n : ∑ x < c}`. -/
def L (n : ℕ) (c : ℝ) : Set (Fin n → ℝ) := {x | (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧ ∑ i, x i < c}

lemma continuous_IH {n : ℕ} (hn : 1 ≤ n) : Continuous (IH n) := by
  unfold IH
  have := continuous_tp hn
  fun_prop

lemma volume_L {n : ℕ} (hn : 1 ≤ n) (c : ℝ) : volume (L n c) = ENNReal.ofReal (IH n c) := by
  set s : ℕ → Set (Fin n → ℝ) := fun m => S n (c - 1 / ((m : ℝ) + 1))
  have hmono : Monotone s := by
    intro a b hab x hx
    refine ⟨hx.1, hx.2.trans ?_⟩
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hU : L n c = ⋃ m, s m := by
    ext x
    simp only [L, s, S, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hc, hlt⟩
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      exact ⟨m, hc, by linarith⟩
    · rintro ⟨m, hc, hle⟩
      exact ⟨hc, lt_of_le_of_lt hle (by have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
                                        linarith)⟩
  have h1 : Tendsto (fun m => volume (s m)) atTop (𝓝 (volume (L n c))) := by
    rw [hU]; exact tendsto_measure_iUnion_atTop hmono
  have h2 : Tendsto (fun m => volume (s m)) atTop (𝓝 (ENNReal.ofReal (IH n c))) := by
    simp only [s, volume_S]
    apply (ENNReal.continuous_ofReal.tendsto _).comp
    apply ((continuous_IH hn).tendsto c).comp
    have : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds (x := c)).sub this
  exact tendsto_nhds_unique h1 h2

/-- **Lemma 3.14, Eq. (79), first equality (Laplace)**:
`Vol_n {x ∈ [0,1]^n : k − 1 ≤ ∑ x ≤ k} = E(n, k−1)/n!` for `n ≥ 1`, `k ≥ 1`. -/
theorem volume_slab {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    volume (Slab n k) =
      ENNReal.ofReal ((EulerianCert.Bracket.E n (k - 1) : ℝ) / n.factorial) := by
  have hdiff : Slab n k = S n k \ L n ((k : ℝ) - 1) := by
    ext x
    simp only [Slab, S, L, Set.mem_diff, Set.mem_setOf_eq, not_and, not_lt]
    constructor
    · rintro ⟨hc, h1, h2⟩; exact ⟨⟨hc, h2⟩, fun _ => h1⟩
    · rintro ⟨⟨hc, h2⟩, h1⟩; exact ⟨hc, h1 hc, h2⟩
  have hsub : L n ((k : ℝ) - 1) ⊆ S n k := fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  have hLm : MeasurableSet (L n ((k : ℝ) - 1)) := by
    have h1 : MeasurableSet {x : Fin n → ℝ | ∀ i, x i ∈ Icc (0 : ℝ) 1} := by
      rw [show {x : Fin n → ℝ | ∀ i, x i ∈ Icc (0 : ℝ) 1} = ⋂ i, (fun x => x i) ⁻¹' Icc 0 1 by
        ext x; simp]
      exact MeasurableSet.iInter (fun i => measurableSet_Icc.preimage (measurable_pi_apply i))
    exact h1.inter (measurableSet_lt (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
      measurable_const)
  have hfin : volume (L n ((k : ℝ) - 1)) ≠ ⊤ := by
    rw [volume_L hn]; exact ENNReal.ofReal_ne_top
  rw [hdiff, measure_diff hsub hLm.nullMeasurableSet hfin, volume_S, volume_L hn,
    ← ENNReal.ofReal_sub _ (IH_nonneg n _), IH_sub, E_eq_U hn,
    show (((k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) by push_cast [Nat.cast_sub hk]; ring]

end EulerianCert.CubeSlabs
