import Mathlib
import Manuscript16.MaxwellGibbsTailObstruction20261125

/-!
# M16 v16.5 §14.5, Theorem 14.5, equation (W1): exact `W₁` and an explicit optimal coupling

Source lock: `Manoscritto_16_5_Magnetic_Evanescent_Spectral_Transport_20261116(1).zip`,
SHA-256 `4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e`
(analytic audits `audits/manuscript16/v16_5_section14_5_finite_w1_bounds_20261117.md`, PR #342,
and `audits/M16_v165_Section14_GibbsScalarMean_20261117.md`, PR #343, whose open obligations
— first moments, stochastic dominance, identification of the optimal `W₁` with the difference
of the means — are discharged here).

For `0 < q < 1`, with the laws of `Manuscript16.MaxwellGibbsTail20261125`
(`pₙ = (1-q) qⁿ`, `rₙ = 4(n+1)(n+3) qⁿ / C(q)`, `C(q) = 4(3-q)/(1-q)³`, `Eₙ = 2n + 1`):

* exact energy means `∑ Eₙ pₙ = 2q/(1-q) + 1` and `∑ Eₙ rₙ = 2q(3/(1-q) - 1/(3-q)) + 1`;
* every coupling `μ` of `p` and `r` on `ℕ × ℕ` has transport cost
  `∫ |E_x - E_y| dμ ≥ 2Δ(q)`, `Δ(q) = q(5-q)/((1-q)(3-q)) > 0`;
* the explicit coupling `ν(m, n) = (1-q)³ qⁿ (2(n-m)+3)/(3-q)` for `m ≤ n` (zero otherwise)
  has marginals `p` and `r`, is supported on `{m ≤ n}`, and has cost exactly `2Δ(q)`;
* hence `W₁(p_E, r_E) = 2Δ(q) = 4q/(1-q) - 2q/(3-q)` (infimum attained), which contains the
  two-sided bounds of the analytic audit #342; `W₁` is finite while `W∞ = +∞` (#600);
* stochastic dominance of the upper tails: `q^N ≤ ∑_{n ≥ N} rₙ` for every `N`.

`W₁` is the infimum, over probability measures on `ℕ × ℕ` with the two marginals, of the
lower Lebesgue integral of `|E_x - E_y|`. No statement on electromagnetic energy flux or
physical spatial transport is made.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Manuscript16.MaxwellGibbsW1_20261125

open Manuscript16.V165 Manuscript16.MaxwellGibbsTail20261125

variable {q : ℝ}

/-! ## Exact means on the energy axis -/

/-- `∑ n³ qⁿ = q(1 + 4q + q²)/(1-q)⁴`. -/
theorem hasSum_cube_mul_geometric (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 3 * q ^ n) (q * (1 + 4 * q + q ^ 2) / (1 - q) ^ 4) := by
  have hn : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have h := hasSum_pow_mul_geometric_of_norm_lt_one 3 hn
  have hd : 1 - q ≠ 0 := by linarith
  have e0 : Nat.stirlingSecond 3 0 = 0 := by decide
  have e1 : Nat.stirlingSecond 3 1 = 1 := by decide
  have e2 : Nat.stirlingSecond 3 2 = 3 := by decide
  have e3 : Nat.stirlingSecond 3 3 = 1 := by decide
  convert h using 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, Nat.factorial]
  push_cast
  field_simp
  ring

/-- Exact magnetic energy mean: `∑ Eₙ pₙ = 2q/(1-q) + 1`. -/
theorem magnetic_energy_mean_hasSum (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun n => energy n * magneticLaw q n) (2 * q / (1 - q) + 1) := by
  have hn : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have h0 := hasSum_geometric_of_norm_lt_one hn
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have hd : 1 - q ≠ 0 := by linarith
  have h := (h1.mul_left (2 * (1 - q))).add (h0.mul_left (1 - q))
  convert h using 1
  · funext n
    simp only [energy, magneticLaw]
    ring
  · field_simp

/-- Exact Maxwell energy mean: `∑ Eₙ rₙ = 2q(3/(1-q) - 1/(3-q)) + 1`, i.e. `2 q C'(q)/C(q) + 1`. -/
theorem maxwell_energy_mean_hasSum (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun n => energy n * maxwellLaw q n) (2 * q * (3 / (1 - q) - 1 / (3 - q)) + 1) := by
  have hn : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have h0 := hasSum_geometric_of_norm_lt_one hn
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have h2 := hasSum_sq_mul_geometric_of_norm_lt_one hn
  have h3 := hasSum_cube_mul_geometric hq0 hq1
  have hd : 1 - q ≠ 0 := by linarith
  have h3q : 3 - q ≠ 0 := by linarith
  have hC := (maxwellNorm_pos hq0 hq1).ne'
  have h := ((((h3.mul_left 2).add (h2.mul_left 9)).add (h1.mul_left 10)).add
    (h0.mul_left 3)).mul_left (4 / maxwellNorm q)
  convert h using 1
  · funext n
    simp only [energy, maxwellLaw, resonanceWeight]
    field_simp
    ring
  · simp only [maxwellNorm]
    field_simp
    ring

/-- The mean gap `Δ(q) = q(5-q)/((1-q)(3-q))` on the index axis. -/
def meanGap (q : ℝ) : ℝ := q * (5 - q) / ((1 - q) * (3 - q))

theorem meanGap_pos (hq0 : 0 < q) (hq1 : q < 1) : 0 < meanGap q := by
  unfold meanGap
  have h1 : 0 < 1 - q := by linarith
  have h3 : 0 < 3 - q := by linarith
  have h5 : 0 < 5 - q := by linarith
  positivity

/-- The difference of the energy means is `2Δ(q)`. -/
theorem energy_mean_gap (hq0 : 0 < q) (hq1 : q < 1) :
    (2 * q * (3 / (1 - q) - 1 / (3 - q)) + 1) - (2 * q / (1 - q) + 1) = 2 * meanGap q := by
  have hd : 1 - q ≠ 0 := by linarith
  have h3q : 3 - q ≠ 0 := by linarith
  unfold meanGap
  field_simp
  ring

/-- Printed form: `2Δ(q) = 4q/(1-q) - 2q/(3-q)`. -/
theorem two_meanGap_eq (hq0 : 0 < q) (hq1 : q < 1) :
    2 * meanGap q = 4 * q / (1 - q) - 2 * q / (3 - q) := by
  have hd : 1 - q ≠ 0 := by linarith
  have h3q : 3 - q ≠ 0 := by linarith
  unfold meanGap
  field_simp
  ring

/-! ## Integrals of marginal observables under an arbitrary coupling -/

theorem ofReal_tsum_eq {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {a : ℝ} (h : HasSum f a) :
    ∑' n, ENNReal.ofReal (f n) = ENNReal.ofReal a := by
  rw [← ENNReal.ofReal_tsum_of_nonneg hf h.summable, h.tsum_eq]

/-- Lower integral of an observable of the first coordinate under any coupling. -/
theorem lintegral_fst_of_coupling {μ : Measure (ℕ × ℕ)} {p r : ℕ → ℝ} (hμ : IsCoupling μ p r)
    (hp : ∀ n, 0 ≤ p n) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) {a : ℝ}
    (ha : HasSum (fun n => f n * p n) a) :
    ∫⁻ x, ENNReal.ofReal (f x.1) ∂μ = ENNReal.ofReal a := by
  have hm := lintegral_map (μ := μ) (f := fun n : ℕ => ENNReal.ofReal (f n))
    (measurable_of_countable _) measurable_fst
  rw [← hm, lintegral_countable']
  have hsing : ∀ n, (μ.map Prod.fst) {n} = ENNReal.ofReal (p n) := by
    intro n
    rw [Measure.map_apply measurable_fst (measurableSet_singleton n)]
    exact hμ.2.1 n
  simp_rw [hsing, ← ENNReal.ofReal_mul (hf _)]
  exact ofReal_tsum_eq (fun n => mul_nonneg (hf n) (hp n)) ha

/-- Lower integral of an observable of the second coordinate under any coupling. -/
theorem lintegral_snd_of_coupling {μ : Measure (ℕ × ℕ)} {p r : ℕ → ℝ} (hμ : IsCoupling μ p r)
    (hr : ∀ n, 0 ≤ r n) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) {a : ℝ}
    (ha : HasSum (fun n => f n * r n) a) :
    ∫⁻ x, ENNReal.ofReal (f x.2) ∂μ = ENNReal.ofReal a := by
  have hm := lintegral_map (μ := μ) (f := fun n : ℕ => ENNReal.ofReal (f n))
    (measurable_of_countable _) measurable_snd
  rw [← hm, lintegral_countable']
  have hsing : ∀ n, (μ.map Prod.snd) {n} = ENNReal.ofReal (r n) := by
    intro n
    rw [Measure.map_apply measurable_snd (measurableSet_singleton n)]
    exact hμ.2.2 n
  simp_rw [hsing, ← ENNReal.ofReal_mul (hf _)]
  exact ofReal_tsum_eq (fun n => mul_nonneg (hf n) (hr n)) ha

theorem energy_nonneg (n : ℕ) : 0 ≤ energy n := by
  unfold energy
  positivity

/-! ## Lower bound for every coupling -/

/-- **Kantorovich lower bound.** Every coupling of `p` and `r` has energy transport cost at
least `2Δ(q)`. -/
theorem coupling_cost_ge (hq0 : 0 < q) (hq1 : q < 1) {μ : Measure (ℕ × ℕ)}
    (hμ : IsCoupling μ (magneticLaw q) (maxwellLaw q)) :
    ENNReal.ofReal (2 * meanGap q) ≤ ∫⁻ x, ENNReal.ofReal |energy x.1 - energy x.2| ∂μ := by
  have hX := lintegral_fst_of_coupling hμ (magneticLaw_nonneg hq0 hq1) energy energy_nonneg
    (magnetic_energy_mean_hasSum hq0 hq1)
  have hY := lintegral_snd_of_coupling hμ (maxwellLaw_nonneg hq0 hq1) energy energy_nonneg
    (maxwell_energy_mean_hasSum hq0 hq1)
  have hpt : ∀ x : ℕ × ℕ, ENNReal.ofReal (energy x.2) ≤
      ENNReal.ofReal (energy x.1) + ENNReal.ofReal |energy x.1 - energy x.2| := by
    intro x
    rw [← ENNReal.ofReal_add (energy_nonneg _) (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have := neg_abs_le (energy x.1 - energy x.2)
    linarith
  have hint : ∫⁻ x, ENNReal.ofReal (energy x.2) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal (energy x.1) ∂μ + ∫⁻ x, ENNReal.ofReal |energy x.1 - energy x.2| ∂μ := by
    rw [← lintegral_add_left (measurable_of_countable _)]
    exact lintegral_mono hpt
  rw [hX, hY] at hint
  have hpos : 0 ≤ 2 * q / (1 - q) + 1 := by
    have : 0 < 1 - q := by linarith
    positivity
  rw [← energy_mean_gap hq0 hq1, ENNReal.ofReal_sub _ hpos]
  exact tsub_le_iff_left.2 hint

/-! ## The explicit optimal coupling -/

/-- Mass of the optimal coupling: `ν(m, n) = (1-q)³ qⁿ (2(n-m)+3)/(3-q)` for `m ≤ n`. -/
def optMass (q : ℝ) (m n : ℕ) : ℝ :=
  if m ≤ n then (1 - q) ^ 3 * q ^ n * (2 * ((n : ℝ) - m) + 3) / (3 - q) else 0

theorem optMass_nonneg (hq0 : 0 < q) (hq1 : q < 1) (m n : ℕ) : 0 ≤ optMass q m n := by
  unfold optMass
  split_ifs with h
  · have h1 : 0 < 1 - q := by linarith
    have h3 : 0 < 3 - q := by linarith
    have hmn : (m : ℝ) ≤ n := by exact_mod_cast h
    have : 0 ≤ 2 * ((n : ℝ) - m) + 3 := by linarith
    positivity
  · exact le_rfl

/-- First marginal of `ν`: `∑ₙ ν(m, n) = pₘ`. -/
theorem optMass_fst_hasSum (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) :
    HasSum (fun n => optMass q m n) (magneticLaw q m) := by
  have hn : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have h0 := hasSum_geometric_of_norm_lt_one hn
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have hd : 1 - q ≠ 0 := by linarith
  have h3q : 3 - q ≠ 0 := by linarith
  apply (upper_tail_hasSum_iff (fun n => (1 - q) ^ 3 * q ^ n * (2 * ((n : ℝ) - m) + 3) / (3 - q))
    m (magneticLaw q m)).2
  have h := ((h1.mul_left 2).add (h0.mul_left 3)).mul_left ((1 - q) ^ 3 * q ^ m / (3 - q))
  convert h using 1
  · funext k
    push_cast
    rw [pow_add]
    field_simp
    ring
  · simp only [magneticLaw]
    field_simp
    ring

theorem sum_range_natCast (K : ℕ) : ∑ m ∈ range K, (m : ℝ) = (K : ℝ) * ((K : ℝ) - 1) / 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem sum_range_weight (n : ℕ) :
    ∑ m ∈ range (n + 1), (2 * ((n : ℝ) - m) + 3) = ((n : ℝ) + 1) * ((n : ℝ) + 3) := by
  have h : ∀ m : ℕ, 2 * ((n : ℝ) - m) + 3 = (2 * (n : ℝ) + 3) - 2 * (m : ℝ) := by
    intro m
    ring
  simp_rw [h]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum,
    sum_range_natCast, nsmul_eq_mul]
  push_cast
  ring

/-- Second marginal of `ν`: `∑ₘ ν(m, n) = rₙ` (a finite sum over `m ≤ n`). -/
theorem optMass_snd_hasSum (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    HasSum (fun m => optMass q m n) (maxwellLaw q n) := by
  have hd : 1 - q ≠ 0 := by linarith
  have h3q : 3 - q ≠ 0 := by linarith
  have hC := (maxwellNorm_pos hq0 hq1).ne'
  have hz : ∀ m ∉ range (n + 1), optMass q m n = 0 := by
    intro m hm
    rw [Finset.mem_range, not_lt] at hm
    simp [optMass, show ¬ m ≤ n by omega]
  have hs : ∑ m ∈ range (n + 1), optMass q m n =
      ∑ m ∈ range (n + 1), (1 - q) ^ 3 * q ^ n / (3 - q) * (2 * ((n : ℝ) - m) + 3) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    simp only [optMass, show m ≤ n by omega, ite_true]
    ring
  have hsum : maxwellLaw q n = ∑ m ∈ range (n + 1), optMass q m n := by
    rw [hs, ← Finset.mul_sum, sum_range_weight]
    simp only [maxwellLaw, resonanceWeight, maxwellNorm]
    have h4 : 4 * (3 - q) ≠ 0 := by positivity
    rw [div_div_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff h4 h3q]
    ring
  rw [hsum]
  exact hasSum_sum_of_ne_finset_zero hz

/-- The optimal coupling as a probability mass function on `ℕ × ℕ`. -/
def optPMF (hq0 : 0 < q) (hq1 : q < 1) : PMF (ℕ × ℕ) :=
  ⟨fun x => ENNReal.ofReal (optMass q x.1 x.2), by
    have hs := ENNReal.summable.hasSum (f := fun x : ℕ × ℕ => ENNReal.ofReal (optMass q x.1 x.2))
    convert hs using 1
    rw [ENNReal.tsum_prod']
    simp_rw [ofReal_tsum_eq (optMass_nonneg hq0 hq1 _) (optMass_fst_hasSum hq0 hq1 _)]
    rw [ofReal_tsum_eq (magneticLaw_nonneg hq0 hq1) (magneticLaw_hasSum hq0 hq1),
      ENNReal.ofReal_one]⟩

/-- The optimal coupling as a measure on `ℕ × ℕ`. -/
def optCoupling (hq0 : 0 < q) (hq1 : q < 1) : Measure (ℕ × ℕ) := (optPMF hq0 hq1).toMeasure

theorem optPMF_apply (hq0 : 0 < q) (hq1 : q < 1) (x : ℕ × ℕ) :
    optPMF hq0 hq1 x = ENNReal.ofReal (optMass q x.1 x.2) := rfl

/-- `ν` is a coupling of `p` and `r`. -/
theorem optCoupling_isCoupling (hq0 : 0 < q) (hq1 : q < 1) :
    IsCoupling (optCoupling hq0 hq1) (magneticLaw q) (maxwellLaw q) := by
  refine ⟨by unfold optCoupling; infer_instance, fun m => ?_, fun n => ?_⟩
  · rw [optCoupling, PMF.toMeasure_apply _ (measurable_fst (measurableSet_singleton m)),
      ENNReal.tsum_prod']
    have hout : ∀ a : ℕ, a ≠ m →
        ∑' b : ℕ, (Prod.fst ⁻¹' {m}).indicator (optPMF hq0 hq1) (a, b) = 0 := by
      intro a ha
      simp [ha]
    rw [tsum_eq_single m hout]
    have hin : ∀ b : ℕ, (Prod.fst ⁻¹' {m}).indicator (optPMF hq0 hq1) (m, b) =
        ENNReal.ofReal (optMass q m b) := by
      intro b
      simp [optPMF_apply]
    simp_rw [hin]
    exact ofReal_tsum_eq (optMass_nonneg hq0 hq1 m) (optMass_fst_hasSum hq0 hq1 m)
  · rw [optCoupling, PMF.toMeasure_apply _ (measurable_snd (measurableSet_singleton n)),
      ENNReal.tsum_prod']
    have hin : ∀ a : ℕ, ∑' b : ℕ, (Prod.snd ⁻¹' {n}).indicator (optPMF hq0 hq1) (a, b) =
        ENNReal.ofReal (optMass q a n) := by
      intro a
      rw [tsum_eq_single n]
      · simp [optPMF_apply]
      · intro b hb
        simp [hb]
    simp_rw [hin]
    exact ofReal_tsum_eq (fun m => optMass_nonneg hq0 hq1 m n) (optMass_snd_hasSum hq0 hq1 n)

/-- `ν` is monotone: almost surely `x.1 ≤ x.2`. -/
theorem optCoupling_ae_le (hq0 : 0 < q) (hq1 : q < 1) :
    ∀ᵐ x ∂(optCoupling hq0 hq1), x.1 ≤ x.2 := by
  rw [ae_iff, optCoupling, PMF.toMeasure_apply_eq_zero_iff _ (MeasurableSet.of_discrete)]
  rw [Set.disjoint_left]
  intro x hx hlt
  rw [PMF.mem_support_iff, optPMF_apply] at hx
  have hlt' : ¬ x.1 ≤ x.2 := hlt
  apply hx
  simp [optMass, hlt']

/-- **Optimality.** The cost of `ν` is exactly `2Δ(q)`. -/
theorem optCoupling_cost (hq0 : 0 < q) (hq1 : q < 1) :
    ∫⁻ x, ENNReal.ofReal |energy x.1 - energy x.2| ∂(optCoupling hq0 hq1) =
      ENNReal.ofReal (2 * meanGap q) := by
  have hμ := optCoupling_isCoupling hq0 hq1
  have hX := lintegral_fst_of_coupling hμ (magneticLaw_nonneg hq0 hq1) energy energy_nonneg
    (magnetic_energy_mean_hasSum hq0 hq1)
  have hY := lintegral_snd_of_coupling hμ (maxwellLaw_nonneg hq0 hq1) energy energy_nonneg
    (maxwell_energy_mean_hasSum hq0 hq1)
  have hae : (fun x : ℕ × ℕ => ENNReal.ofReal (energy x.2)) =ᵐ[optCoupling hq0 hq1]
      fun x => ENNReal.ofReal (energy x.1) + ENNReal.ofReal |energy x.1 - energy x.2| := by
    filter_upwards [optCoupling_ae_le hq0 hq1] with x hx
    rw [← ENNReal.ofReal_add (energy_nonneg _) (abs_nonneg _)]
    congr 1
    have hle : energy x.1 ≤ energy x.2 := by
      unfold energy
      have : (x.1 : ℝ) ≤ x.2 := by exact_mod_cast hx
      linarith
    rw [abs_of_nonpos (by linarith)]
    ring
  have hint := lintegral_congr_ae hae
  rw [lintegral_add_left (measurable_of_countable _), hX, hY] at hint
  have hfin : ENNReal.ofReal (2 * q / (1 - q) + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpos : 0 ≤ 2 * q / (1 - q) + 1 := by
    have : 0 < 1 - q := by linarith
    positivity
  rw [← energy_mean_gap hq0 hq1, ENNReal.ofReal_sub _ hpos, hint,
    ENNReal.add_sub_cancel_left hfin]

/-! ## `W₁` on the energy axis -/

/-- `W₁` on the energy axis `Eₙ = 2n + 1`: infimum over couplings on `ℕ × ℕ` of the lower
integral of `|E_x - E_y|`. -/
def wOneEnergy (p r : ℕ → ℝ) : ℝ≥0∞ :=
  ⨅ (μ : Measure (ℕ × ℕ)) (_ : IsCoupling μ p r),
    ∫⁻ x, ENNReal.ofReal |energy x.1 - energy x.2| ∂μ

/-- **Theorem 14.5, equation (W1).** `W₁(p_E, r_E) = 2Δ(q)`, attained by `ν`. -/
theorem wOneEnergy_eq (hq0 : 0 < q) (hq1 : q < 1) :
    wOneEnergy (magneticLaw q) (maxwellLaw q) = ENNReal.ofReal (2 * meanGap q) := by
  apply le_antisymm
  · exact (iInf₂_le (optCoupling hq0 hq1) (optCoupling_isCoupling hq0 hq1)).trans
      (optCoupling_cost hq0 hq1).le
  · exact le_iInf₂ fun μ hμ => coupling_cost_ge hq0 hq1 hμ

/-- Printed form: `W₁(p_E, r_E) = 4q/(1-q) - 2q/(3-q)`. -/
theorem wOneEnergy_eq_closed (hq0 : 0 < q) (hq1 : q < 1) :
    wOneEnergy (magneticLaw q) (maxwellLaw q) =
      ENNReal.ofReal (4 * q / (1 - q) - 2 * q / (3 - q)) := by
  rw [wOneEnergy_eq hq0 hq1, two_meanGap_eq hq0 hq1]

/-- The two-sided bounds of the analytic audit #342, as a consequence of the exact value. -/
theorem wOneEnergy_bounds (hq0 : 0 < q) (hq1 : q < 1) :
    2 * q * (5 - q) / ((1 - q) * (3 - q)) ≤
        (wOneEnergy (magneticLaw q) (maxwellLaw q)).toReal ∧
      (wOneEnergy (magneticLaw q) (maxwellLaw q)).toReal ≤
        2 * q * (4 / (1 - q) - 1 / (3 - q)) := by
  have hg := meanGap_pos hq0 hq1
  rw [wOneEnergy_eq hq0 hq1, ENNReal.toReal_ofReal (by linarith)]
  have hd : 0 < 1 - q := by linarith
  have h3 : 0 < 3 - q := by linarith
  constructor
  · unfold meanGap
    apply le_of_eq
    ring
  · have key : 2 * q * (4 / (1 - q) - 1 / (3 - q)) - 2 * meanGap q = 4 * q / (1 - q) := by
      unfold meanGap
      field_simp
      ring
    have : 0 ≤ 4 * q / (1 - q) := by positivity
    linarith

/-- `W₁` is finite while `W∞ = +∞` (#600): no contradiction, finite mean transport does not
bound the essential displacement. -/
theorem wOne_finite_wInf_infinite (hq0 : 0 < q) (hq1 : q < 1) :
    wOneEnergy (magneticLaw q) (maxwellLaw q) < ⊤ ∧
      wInfEnergy (magneticLaw q) (maxwellLaw q) = ⊤ := by
  refine ⟨?_, wInfEnergy_eq_top hq0 hq1⟩
  rw [wOneEnergy_eq hq0 hq1]
  exact ENNReal.ofReal_lt_top

/-! ## Stochastic dominance of the upper tails -/

/-- **Stochastic dominance.** `∑_{n ≥ N} pₙ = q^N ≤ ∑_{n ≥ N} rₙ` for every `N`. -/
theorem tail_dominance (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    q ^ N ≤ maxwellTailClosed q N := by
  have hd : 0 < 1 - q := by linarith
  have h3 : 0 < 3 - q := by linarith
  have hqN : 0 < q ^ N := pow_pos hq0 N
  have key : maxwellTailClosed q N - q ^ N =
      q ^ N * ((N : ℝ) * ((N : ℝ) + 4) * (1 - q) ^ 2 + 2 * (N : ℝ) * q * (1 - q)) / (3 - q) := by
    simp only [maxwellTailClosed, maxwellNorm]
    field_simp
    ring
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have : 0 ≤ q ^ N * ((N : ℝ) * ((N : ℝ) + 4) * (1 - q) ^ 2 + 2 * (N : ℝ) * q * (1 - q)) /
      (3 - q) := by positivity
  linarith

end Manuscript16.MaxwellGibbsW1_20261125

#print axioms Manuscript16.MaxwellGibbsW1_20261125.hasSum_cube_mul_geometric
#print axioms Manuscript16.MaxwellGibbsW1_20261125.magnetic_energy_mean_hasSum
#print axioms Manuscript16.MaxwellGibbsW1_20261125.maxwell_energy_mean_hasSum
#print axioms Manuscript16.MaxwellGibbsW1_20261125.meanGap_pos
#print axioms Manuscript16.MaxwellGibbsW1_20261125.energy_mean_gap
#print axioms Manuscript16.MaxwellGibbsW1_20261125.two_meanGap_eq
#print axioms Manuscript16.MaxwellGibbsW1_20261125.ofReal_tsum_eq
#print axioms Manuscript16.MaxwellGibbsW1_20261125.lintegral_fst_of_coupling
#print axioms Manuscript16.MaxwellGibbsW1_20261125.lintegral_snd_of_coupling
#print axioms Manuscript16.MaxwellGibbsW1_20261125.energy_nonneg
#print axioms Manuscript16.MaxwellGibbsW1_20261125.coupling_cost_ge
#print axioms Manuscript16.MaxwellGibbsW1_20261125.optMass_nonneg
#print axioms Manuscript16.MaxwellGibbsW1_20261125.optMass_fst_hasSum
#print axioms Manuscript16.MaxwellGibbsW1_20261125.sum_range_natCast
#print axioms Manuscript16.MaxwellGibbsW1_20261125.sum_range_weight
#print axioms Manuscript16.MaxwellGibbsW1_20261125.optMass_snd_hasSum
#print axioms Manuscript16.MaxwellGibbsW1_20261125.optPMF_apply
#print axioms Manuscript16.MaxwellGibbsW1_20261125.optCoupling_isCoupling
#print axioms Manuscript16.MaxwellGibbsW1_20261125.optCoupling_ae_le
#print axioms Manuscript16.MaxwellGibbsW1_20261125.optCoupling_cost
#print axioms Manuscript16.MaxwellGibbsW1_20261125.wOneEnergy_eq
#print axioms Manuscript16.MaxwellGibbsW1_20261125.wOneEnergy_eq_closed
#print axioms Manuscript16.MaxwellGibbsW1_20261125.wOneEnergy_bounds
#print axioms Manuscript16.MaxwellGibbsW1_20261125.wOne_finite_wInf_infinite
#print axioms Manuscript16.MaxwellGibbsW1_20261125.tail_dominance
