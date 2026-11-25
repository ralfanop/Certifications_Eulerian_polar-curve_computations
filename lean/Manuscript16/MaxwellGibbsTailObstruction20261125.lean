import Mathlib
import Manuscript16.V165ResonanceInfinite

/-!
# M16 v16.5 §14.5, Theorem 14.5: exact Maxwell–Gibbs upper tail and the `W∞` obstruction

Source lock: `Manoscritto_16_5_Magnetic_Evanescent_Spectral_Transport_20261116(1).zip`,
SHA-256 `4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e`
(analytic audit `audits/manuscript16/v16_5_section14_5_exact_tail_audit_20261117.md`, whose
Lean obligations (i)–(vi) are discharged here).

For `0 < q < 1`, `w_n = 4(n+1)(n+3)` (`Manuscript16.V165.resonanceWeight`) and
`C(q) = 4(3-q)/(1-q)^3`:

* the magnetic index law `p_n = (1-q) q^n` and the Maxwell index law `r_n = w_n q^n / C(q)`
  are probability laws on `ℕ` (`magneticLaw_hasSum`, `maxwellLaw_hasSum`);
* exact upper tails: `∑_{n ≥ N} p_n = q^N` and
  `∑_{n ≥ N} r_n = 4 q^N / C(q) · ((N+1)(N+3)/(1-q) + (2N+4) q/(1-q)^2 + q(1+q)/(1-q)^3)`,
  both as series and as probabilities of the events `{X ≥ N}`, `{Y ≥ N}`;
* the ratio of the two tails is bounded below by `4(N+1)(N+3)/(C(q)(1-q))` and tends to `+∞`;
* on any measure space, two `ℕ`-valued random variables with laws `p` and `r` never satisfy
  `|X - Y| ≤ D` almost everywhere, for any real `D`, neither on the index axis nor on the energy
  axis `E_n = 2n + 1`; equivalently the essential supremum of the displacement is `+∞`;
* hence `W∞(p, r) = +∞`, the infimum over all couplings on `ℕ × ℕ` of the essential supremum of
  the displacement, on both axes; the set of couplings is nonempty (independent coupling).

No statement on electromagnetic energy flux or physical spatial transport is made.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Manuscript16.MaxwellGibbsTail20261125

open Manuscript16.V165

/-- `C(q) = ∑ₙ wₙ qⁿ = 4(3-q)/(1-q)³`. -/
def maxwellNorm (q : ℝ) : ℝ := 4 * (3 - q) / (1 - q) ^ 3

/-- Magnetic index law `pₙ = (1-q) qⁿ`. -/
def magneticLaw (q : ℝ) (n : ℕ) : ℝ := (1 - q) * q ^ n

/-- Maxwell index law `rₙ = wₙ qⁿ / C(q)`. -/
def maxwellLaw (q : ℝ) (n : ℕ) : ℝ := resonanceWeight n * q ^ n / maxwellNorm q

/-- Energy axis `Eₙ = 2n + 1`. -/
def energy (n : ℕ) : ℝ := 2 * (n : ℝ) + 1

/-- Closed form of the Maxwell upper tail `∑_{n ≥ N} rₙ`. -/
def maxwellTailClosed (q : ℝ) (N : ℕ) : ℝ :=
  4 * q ^ N / maxwellNorm q *
    (((N : ℝ) + 1) * ((N : ℝ) + 3) / (1 - q) + (2 * (N : ℝ) + 4) * q / (1 - q) ^ 2 +
      q * (1 + q) / (1 - q) ^ 3)

variable {q : ℝ}

theorem maxwellNorm_pos (hq0 : 0 < q) (hq1 : q < 1) : 0 < maxwellNorm q := by
  unfold maxwellNorm
  have h1 : 0 < 1 - q := by linarith
  have h3 : 0 < 3 - q := by linarith
  positivity

theorem resonanceWeight_pos (n : ℕ) : 0 < resonanceWeight n := by
  unfold resonanceWeight
  positivity

theorem magneticLaw_nonneg (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) : 0 ≤ magneticLaw q n := by
  unfold magneticLaw
  have h1 : 0 < 1 - q := by linarith
  positivity

theorem maxwellLaw_nonneg (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) : 0 ≤ maxwellLaw q n := by
  unfold maxwellLaw
  have := maxwellNorm_pos hq0 hq1
  have := resonanceWeight_pos n
  positivity

/-- The magnetic index law is a probability law. -/
theorem magneticLaw_hasSum (hq0 : 0 < q) (hq1 : q < 1) : HasSum (magneticLaw q) 1 := by
  have h := (hasSum_geometric_of_lt_one hq0.le hq1).mul_left (1 - q)
  have hd : 1 - q ≠ 0 := by linarith
  rw [mul_inv_cancel₀ hd] at h
  exact h

/-- The Maxwell index law is a probability law (normalisation by `C(q)`). -/
theorem maxwellLaw_hasSum (hq0 : 0 < q) (hq1 : q < 1) : HasSum (maxwellLaw q) 1 := by
  have h := (resonance_hasSum q hq0 hq1).div_const (maxwellNorm q)
  rw [show 4 * (3 - q) / (1 - q) ^ 3 / maxwellNorm q = 1 from
    div_self (maxwellNorm_pos hq0 hq1).ne'] at h
  exact h

/-- Exact magnetic upper tail as a series: `∑_{k} p_{k+N} = q^N`. -/
theorem magnetic_tail_hasSum (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    HasSum (fun k : ℕ => magneticLaw q (k + N)) (q ^ N) := by
  have h := (magneticLaw_hasSum hq0 hq1).mul_left (q ^ N)
  rw [mul_one] at h
  convert h using 1
  funext k
  simp only [magneticLaw, pow_add]
  ring

/-- Exact Maxwell upper tail as a series, from the three geometric moment identities. -/
theorem maxwell_tail_hasSum (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    HasSum (fun k : ℕ => maxwellLaw q (k + N)) (maxwellTailClosed q N) := by
  have hn : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have h0 := hasSum_geometric_of_norm_lt_one hn
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have h2 := hasSum_sq_mul_geometric_of_norm_lt_one hn
  have hC := (maxwellNorm_pos hq0 hq1).ne'
  have hd : 1 - q ≠ 0 := by linarith
  have h := ((h0.mul_left (((N : ℝ) + 1) * ((N : ℝ) + 3))).add
    ((h1.mul_left (2 * (N : ℝ) + 4)).add h2)).mul_left (4 * q ^ N / maxwellNorm q)
  convert h using 1
  · funext k
    simp only [maxwellLaw, resonanceWeight, pow_add]
    push_cast
    field_simp
    ring
  · simp only [maxwellTailClosed]
    field_simp
    ring

/-- Upper-tail series written with the indicator of `{n ≥ K}`. -/
theorem upper_tail_hasSum_iff (p : ℕ → ℝ) (K : ℕ) (a : ℝ) :
    HasSum (fun n => if K ≤ n then p n else 0) a ↔ HasSum (fun k => p (k + K)) a := by
  have h2 : ∑ i ∈ Finset.range K, (if K ≤ i then p i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    simp [not_le.mpr hi]
  rw [← hasSum_nat_add_iff' K, h2, sub_zero]
  simp

/-- Law of a measurable `ℕ`-valued map, evaluated on any set through its point masses. -/
theorem measure_preimage_eq_ofReal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℕ) (hX : Measurable X) (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hlaw : ∀ n, P (X ⁻¹' {n}) = ENNReal.ofReal (p n)) (s : Set ℕ) [DecidablePred (· ∈ s)]
    {a : ℝ} (ha : HasSum (fun n => if n ∈ s then p n else 0) a) :
    P (X ⁻¹' s) = ENNReal.ofReal a := by
  let f : ℕ → Set Ω := fun n => if n ∈ s then X ⁻¹' {n} else ∅
  have hU : X ⁻¹' s = ⋃ n, f n := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, f]
    constructor
    · intro h
      exact ⟨X ω, by simp [h]⟩
    · rintro ⟨n, hn⟩
      by_cases h : n ∈ s
      · simp only [h, ite_true, Set.mem_preimage, Set.mem_singleton_iff] at hn
        rw [hn]
        exact h
      · simp [h] at hn
  have hsub : ∀ n, f n ⊆ X ⁻¹' {n} := by
    intro n
    simp only [f]
    split_ifs
    · exact subset_rfl
    · exact Set.empty_subset _
  have hdisj : Pairwise (Function.onFun Disjoint f) := by
    intro i j hij
    exact ((Set.disjoint_singleton.2 hij).preimage X).mono (hsub i) (hsub j)
  have hmeas : ∀ n, MeasurableSet (f n) := by
    intro n
    simp only [f]
    split_ifs
    · exact hX (measurableSet_singleton n)
    · exact MeasurableSet.empty
  have hval : ∀ n, P (f n) = ENNReal.ofReal (if n ∈ s then p n else 0) := by
    intro n
    simp only [f]
    split_ifs
    · exact hlaw n
    · simp
  have hnn : ∀ n, 0 ≤ (if n ∈ s then p n else 0) := by
    intro n
    split_ifs
    · exact hp n
    · exact le_rfl
  rw [hU, measure_iUnion hdisj hmeas, tsum_congr hval,
    ← ENNReal.ofReal_tsum_of_nonneg hnn ha.summable, ha.tsum_eq]

/-- Magnetic upper tail as an event: `P(X ≥ N) = q^N`. -/
theorem magnetic_tail_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hq0 : 0 < q) (hq1 : q < 1) (X : Ω → ℕ) (hX : Measurable X)
    (hlaw : ∀ n, P (X ⁻¹' {n}) = ENNReal.ofReal (magneticLaw q n)) (N : ℕ) :
    P (X ⁻¹' {n | N ≤ n}) = ENNReal.ofReal (q ^ N) :=
  measure_preimage_eq_ofReal P X hX _ (magneticLaw_nonneg hq0 hq1) hlaw _
    ((upper_tail_hasSum_iff _ N _).2 (magnetic_tail_hasSum hq0 hq1 N))

/-- Maxwell upper tail as an event: `P(Y ≥ N) = maxwellTailClosed q N`. -/
theorem maxwell_tail_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hq0 : 0 < q) (hq1 : q < 1) (Y : Ω → ℕ) (hY : Measurable Y)
    (hlaw : ∀ n, P (Y ⁻¹' {n}) = ENNReal.ofReal (maxwellLaw q n)) (N : ℕ) :
    P (Y ⁻¹' {n | N ≤ n}) = ENNReal.ofReal (maxwellTailClosed q N) :=
  measure_preimage_eq_ofReal P Y hY _ (maxwellLaw_nonneg hq0 hq1) hlaw _
    ((upper_tail_hasSum_iff _ N _).2 (maxwell_tail_hasSum hq0 hq1 N))

/-- Quadratic lower bound for the ratio of the Maxwell and magnetic upper tails. -/
theorem tail_ratio_lower (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    4 * (((N : ℝ) + 1) * ((N : ℝ) + 3)) / (maxwellNorm q * (1 - q)) ≤
      maxwellTailClosed q N / q ^ N := by
  have hC := maxwellNorm_pos hq0 hq1
  have h1 : 0 < 1 - q := by linarith
  have hqN : 0 < q ^ N := pow_pos hq0 N
  have key : maxwellTailClosed q N / q ^ N =
      4 * (((N : ℝ) + 1) * ((N : ℝ) + 3)) / (maxwellNorm q * (1 - q)) +
        4 / maxwellNorm q * ((2 * (N : ℝ) + 4) * q / (1 - q) ^ 2 + q * (1 + q) / (1 - q) ^ 3) := by
    simp only [maxwellTailClosed]
    field_simp
    ring
  rw [key]
  have : 0 ≤ 4 / maxwellNorm q *
      ((2 * (N : ℝ) + 4) * q / (1 - q) ^ 2 + q * (1 + q) / (1 - q) ^ 3) := by positivity
  linarith

/-- The ratio of the Maxwell to the magnetic upper tail diverges. -/
theorem tail_ratio_tendsto (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun N : ℕ => maxwellTailClosed q N / q ^ N) atTop atTop := by
  have hC := maxwellNorm_pos hq0 hq1
  have h1 : 0 < 1 - q := by linarith
  have hc : 0 < 4 / (maxwellNorm q * (1 - q)) := by positivity
  refine tendsto_atTop_mono (fun N => ?_)
    (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  refine le_trans ?_ (tail_ratio_lower hq0 hq1 N)
  rw [div_mul_eq_mul_div]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hden : 0 < maxwellNorm q * (1 - q) := by positivity
  rw [div_le_div_iff_of_pos_right hden]
  nlinarith

/-- **Theorem 14.5, obstruction.** On any measure space, two `ℕ`-valued maps with the magnetic
and the Maxwell index laws never have almost-everywhere bounded displacement. -/
theorem no_bounded_displacement {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hq0 : 0 < q) (hq1 : q < 1) (X Y : Ω → ℕ) (hX : Measurable X)
    (hXlaw : ∀ n, P (X ⁻¹' {n}) = ENNReal.ofReal (magneticLaw q n))
    (hYlaw : ∀ n, P (Y ⁻¹' {n}) = ENNReal.ofReal (maxwellLaw q n)) (D : ℝ) :
    ¬ (∀ᵐ ω ∂P, |(X ω : ℝ) - (Y ω : ℝ)| ≤ D) := by
  intro hD
  have hC := maxwellNorm_pos hq0 hq1
  set M : ℕ := ⌈D⌉₊ with hMdef
  have hDM : D ≤ (M : ℝ) := Nat.le_ceil D
  have hqM : 0 < q ^ M := pow_pos hq0 M
  set T : ℕ := ⌈maxwellNorm q / (4 * q ^ M)⌉₊ with hTdef
  have hT : maxwellNorm q ≤ 4 * q ^ M * (T : ℝ) := by
    have h := Nat.le_ceil (maxwellNorm q / (4 * q ^ M))
    rw [← hTdef, div_le_iff₀ (by positivity)] at h
    linarith
  set N : ℕ := M + T with hNdef
  -- almost surely, `Y = N` forces `X ≥ T`
  have hsub : (Y ⁻¹' {N} : Set Ω) ≤ᵐ[P] (X ⁻¹' {n | T ≤ n} : Set Ω) := by
    filter_upwards [hD] with ω hω
    intro hYω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hYω
    show T ≤ X ω
    have h1 : (Y ω : ℝ) - X ω ≤ D := by
      have := neg_abs_le ((X ω : ℝ) - Y ω)
      linarith
    have h2 : (Y ω : ℝ) = (M : ℝ) + T := by rw [hYω, hNdef]; push_cast; ring
    have h3 : (T : ℝ) ≤ X ω := by linarith
    exact_mod_cast h3
  have hle := measure_mono_ae hsub
  rw [hYlaw, magnetic_tail_prob P hq0 hq1 X hX hXlaw T,
    ENNReal.ofReal_le_ofReal_iff (pow_nonneg hq0.le T)] at hle
  -- `r_N ≤ q^T` with `N = M + T` gives `w_N q^M ≤ C(q)`
  have hqT : 0 < q ^ T := pow_pos hq0 T
  have hw : resonanceWeight N * q ^ M ≤ maxwellNorm q := by
    have hle' : resonanceWeight N * q ^ M * q ^ T / maxwellNorm q ≤ q ^ T := by
      have : maxwellLaw q N = resonanceWeight N * q ^ M * q ^ T / maxwellNorm q := by
        simp only [maxwellLaw, hNdef, pow_add]
        ring
      rw [← this]
      exact hle
    rw [div_le_iff₀ hC] at hle'
    nlinarith
  have hwN : 4 * ((T : ℝ) + 1) ≤ resonanceWeight N := by
    simp only [resonanceWeight, hNdef]
    push_cast
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hwN hqM.le]

/-- The same obstruction on the energy axis `Eₙ = 2n + 1`. -/
theorem no_bounded_energy_displacement {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hq0 : 0 < q) (hq1 : q < 1) (X Y : Ω → ℕ) (hX : Measurable X)
    (hXlaw : ∀ n, P (X ⁻¹' {n}) = ENNReal.ofReal (magneticLaw q n))
    (hYlaw : ∀ n, P (Y ⁻¹' {n}) = ENNReal.ofReal (maxwellLaw q n)) (D : ℝ) :
    ¬ (∀ᵐ ω ∂P, |energy (X ω) - energy (Y ω)| ≤ D) := by
  intro h
  apply no_bounded_displacement P hq0 hq1 X Y hX hXlaw hYlaw (D / 2)
  filter_upwards [h] with ω hω
  have he : energy (X ω) - energy (Y ω) = 2 * ((X ω : ℝ) - Y ω) := by
    unfold energy
    ring
  rw [he, abs_mul, abs_two] at hω
  linarith

/-- The essential supremum of the index displacement is `+∞` for every such pair. -/
theorem essSup_displacement_eq_top {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hq0 : 0 < q) (hq1 : q < 1) (X Y : Ω → ℕ) (hX : Measurable X)
    (hXlaw : ∀ n, P (X ⁻¹' {n}) = ENNReal.ofReal (magneticLaw q n))
    (hYlaw : ∀ n, P (Y ⁻¹' {n}) = ENNReal.ofReal (maxwellLaw q n)) :
    essSup (fun ω => ENNReal.ofReal |(X ω : ℝ) - (Y ω : ℝ)|) P = ⊤ := by
  by_contra hne
  apply no_bounded_displacement P hq0 hq1 X Y hX hXlaw hYlaw
    (essSup (fun ω => ENNReal.ofReal |(X ω : ℝ) - (Y ω : ℝ)|) P).toReal
  filter_upwards [ENNReal.ae_le_essSup (fun ω => ENNReal.ofReal |(X ω : ℝ) - (Y ω : ℝ)|)]
    with ω hω
  exact (ENNReal.ofReal_le_iff_le_toReal hne).1 hω

/-- The essential supremum of the energy displacement is `+∞` for every such pair. -/
theorem essSup_energy_displacement_eq_top {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hq0 : 0 < q) (hq1 : q < 1) (X Y : Ω → ℕ) (hX : Measurable X)
    (hXlaw : ∀ n, P (X ⁻¹' {n}) = ENNReal.ofReal (magneticLaw q n))
    (hYlaw : ∀ n, P (Y ⁻¹' {n}) = ENNReal.ofReal (maxwellLaw q n)) :
    essSup (fun ω => ENNReal.ofReal |energy (X ω) - energy (Y ω)|) P = ⊤ := by
  by_contra hne
  apply no_bounded_energy_displacement P hq0 hq1 X Y hX hXlaw hYlaw
    (essSup (fun ω => ENNReal.ofReal |energy (X ω) - energy (Y ω)|) P).toReal
  filter_upwards [ENNReal.ae_le_essSup (fun ω => ENNReal.ofReal |energy (X ω) - energy (Y ω)|)]
    with ω hω
  exact (ENNReal.ofReal_le_iff_le_toReal hne).1 hω

/-- Couplings of two laws on `ℕ`: probability measures on `ℕ × ℕ` with the given marginals. -/
def IsCoupling (μ : Measure (ℕ × ℕ)) (p r : ℕ → ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ n, μ (Prod.fst ⁻¹' {n}) = ENNReal.ofReal (p n)) ∧
    ∀ n, μ (Prod.snd ⁻¹' {n}) = ENNReal.ofReal (r n)

/-- `W∞` on the index axis: infimum over couplings of the essential supremum of `|x - y|`. -/
def wInfIndex (p r : ℕ → ℝ) : ℝ≥0∞ :=
  ⨅ (μ : Measure (ℕ × ℕ)) (_ : IsCoupling μ p r),
    essSup (fun x : ℕ × ℕ => ENNReal.ofReal |(x.1 : ℝ) - (x.2 : ℝ)|) μ

/-- `W∞` on the energy axis `Eₙ = 2n + 1`. -/
def wInfEnergy (p r : ℕ → ℝ) : ℝ≥0∞ :=
  ⨅ (μ : Measure (ℕ × ℕ)) (_ : IsCoupling μ p r),
    essSup (fun x : ℕ × ℕ => ENNReal.ofReal |energy x.1 - energy x.2|) μ

/-- **Theorem 14.5.** `W∞(p, r) = +∞` on the index axis. -/
theorem wInfIndex_eq_top (hq0 : 0 < q) (hq1 : q < 1) :
    wInfIndex (magneticLaw q) (maxwellLaw q) = ⊤ := by
  unfold wInfIndex
  refine iInf₂_eq_top.2 (fun μ hμ => ?_)
  exact essSup_displacement_eq_top μ hq0 hq1 Prod.fst Prod.snd measurable_fst hμ.2.1 hμ.2.2

/-- **Theorem 14.5.** `W∞ = +∞` on the energy axis `Eₙ = 2n + 1` as well. -/
theorem wInfEnergy_eq_top (hq0 : 0 < q) (hq1 : q < 1) :
    wInfEnergy (magneticLaw q) (maxwellLaw q) = ⊤ := by
  unfold wInfEnergy
  refine iInf₂_eq_top.2 (fun μ hμ => ?_)
  exact essSup_energy_displacement_eq_top μ hq0 hq1 Prod.fst Prod.snd measurable_fst
    hμ.2.1 hμ.2.2

/-- A probability law on `ℕ` given by a nonnegative real series of sum one, as a `PMF`. -/
def pmfOfReal (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n) (h : HasSum p 1) : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal (p n), by
    have hs := ENNReal.summable.hasSum (f := fun n => ENNReal.ofReal (p n))
    rwa [← ENNReal.ofReal_tsum_of_nonneg hp h.summable, h.tsum_eq, ENNReal.ofReal_one] at hs⟩

theorem pmfOfReal_toMeasure_singleton (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n) (h : HasSum p 1)
    (n : ℕ) : (pmfOfReal p hp h).toMeasure {n} = ENNReal.ofReal (p n) := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n)]
  rfl

/-- The set of couplings is not empty: the independent coupling. -/
theorem exists_coupling (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ μ : Measure (ℕ × ℕ), IsCoupling μ (magneticLaw q) (maxwellLaw q) := by
  let μp := (pmfOfReal _ (magneticLaw_nonneg hq0 hq1) (magneticLaw_hasSum hq0 hq1)).toMeasure
  let μr := (pmfOfReal _ (maxwellLaw_nonneg hq0 hq1) (maxwellLaw_hasSum hq0 hq1)).toMeasure
  refine ⟨μp.prod μr, inferInstance, fun n => ?_, fun n => ?_⟩
  · rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]
    exact pmfOfReal_toMeasure_singleton _ _ _ n
  · rw [← Set.univ_prod, Measure.prod_prod, measure_univ, one_mul]
    exact pmfOfReal_toMeasure_singleton _ _ _ n

end Manuscript16.MaxwellGibbsTail20261125

#print axioms Manuscript16.MaxwellGibbsTail20261125.maxwellNorm_pos
#print axioms Manuscript16.MaxwellGibbsTail20261125.resonanceWeight_pos
#print axioms Manuscript16.MaxwellGibbsTail20261125.magneticLaw_nonneg
#print axioms Manuscript16.MaxwellGibbsTail20261125.maxwellLaw_nonneg
#print axioms Manuscript16.MaxwellGibbsTail20261125.magneticLaw_hasSum
#print axioms Manuscript16.MaxwellGibbsTail20261125.maxwellLaw_hasSum
#print axioms Manuscript16.MaxwellGibbsTail20261125.magnetic_tail_hasSum
#print axioms Manuscript16.MaxwellGibbsTail20261125.maxwell_tail_hasSum
#print axioms Manuscript16.MaxwellGibbsTail20261125.upper_tail_hasSum_iff
#print axioms Manuscript16.MaxwellGibbsTail20261125.measure_preimage_eq_ofReal
#print axioms Manuscript16.MaxwellGibbsTail20261125.magnetic_tail_prob
#print axioms Manuscript16.MaxwellGibbsTail20261125.maxwell_tail_prob
#print axioms Manuscript16.MaxwellGibbsTail20261125.tail_ratio_lower
#print axioms Manuscript16.MaxwellGibbsTail20261125.tail_ratio_tendsto
#print axioms Manuscript16.MaxwellGibbsTail20261125.no_bounded_displacement
#print axioms Manuscript16.MaxwellGibbsTail20261125.no_bounded_energy_displacement
#print axioms Manuscript16.MaxwellGibbsTail20261125.essSup_displacement_eq_top
#print axioms Manuscript16.MaxwellGibbsTail20261125.essSup_energy_displacement_eq_top
#print axioms Manuscript16.MaxwellGibbsTail20261125.wInfIndex_eq_top
#print axioms Manuscript16.MaxwellGibbsTail20261125.wInfEnergy_eq_top
#print axioms Manuscript16.MaxwellGibbsTail20261125.pmfOfReal_toMeasure_singleton
#print axioms Manuscript16.MaxwellGibbsTail20261125.exists_coupling
