import EulerianGrothendieck.RawScaleAsymptotics
import EulerianGrothendieck.CentralBinomialSeries
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.Polynomial

/-! # Task B: the critical and subcritical branch `0 < c ≤ 1/12`

For the actual probability integrals `N_M(c) = E exp(S_M T_M/(c M))` we prove
`N_M(c) → +∞` and `1/N_M(c) → 0` when `0 < c ≤ 1/12` (Theorem 9.6, branch `t = 1/(12c) ≥ 1`,
including the critical value `t = 1`).

The proof does not use `tsum` of a non-summable series.  For every real `t` and every `M ≥ 1`
we prove the `HasSum` identity of the bounded exponential kernel
(`uniform_exponential_integral_hasSum`); finite partial sums of nonnegative terms are then
lower bounds.  For fixed `k`, `R_{M,k} → 1`; the limiting partial sums
`∑_{k<K} binom(2k,k) t^{2k}/4^k` are unbounded, by `binom(2k,k)/4^k ≥ 1/(2(k+1))` and the
divergence of the harmonic series.  We choose `K` first, then `M`. -/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Finset Filter
namespace EulerianGrothendieck

/-- `HasSum` form of the exact series, valid for every real `t` and every `M ≥ 1`. -/
theorem uniform_exponential_integral_hasSum
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (M : ℕ) (hM : M ≠ 0) (t : ℝ) :
    HasSum (fun k => binomialWeight t k * (uniformMomentRatio M k) ^ 2)
      (∫ xy, Real.exp (t * (standardizedUniformSum U M xy.1 * standardizedUniformSum U M xy.2))
        ∂μ.prod μ) := by
  set Z := standardizedUniformSum U M with hZdef
  have hZ : Measurable Z := standardizedUniformSum_measurable U hU M
  set B := Real.sqrt (12/(M:ℝ)) * ((M:ℝ)/2) with hBdef
  have hB : 0 ≤ B := by positivity
  have hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ B := standardizedUniformSum_ae_bound U hU hlaw M
  have hZprod : Measurable (fun xy : Ω × Ω => Z xy.1 * Z xy.2) :=
    (hZ.comp measurable_fst).mul (hZ.comp measurable_snd)
  have hb : ∀ᵐ xy ∂μ.prod μ, |Z xy.1 * Z xy.2| ≤ B ^ 2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hbound,
      Measure.quasiMeasurePreserving_snd.ae hbound] with xy hx hy
    rw [abs_mul, pow_two]
    exact mul_le_mul hx hy (abs_nonneg _) hB
  have h := bounded_exp_integral_hasSum (fun xy : Ω × Ω => Z xy.1 * Z xy.2) hZprod (B ^ 2) t
    (sq_nonneg B) hb
  have he : ∀ n : ℕ, (∫ xy, (Z xy.1 * Z xy.2) ^ n ∂μ.prod μ) = (∫ ω, Z ω ^ n ∂μ) ^ 2 := by
    intro n
    simp_rw [mul_pow]
    rw [integral_prod_mul (fun ω => Z ω ^ n) (fun ω => Z ω ^ n), pow_two]
  simp_rw [he] at h
  have hodd := standardizedUniformSum_odd_moment U hU hind hlaw M
  have hz : ∀ n ∉ Set.range (fun k : ℕ => 2 * k),
      (t ^ n / (n.factorial : ℝ)) * (∫ ω, Z ω ^ n ∂μ) ^ 2 = 0 := by
    intro n hn
    rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
    · exact absurd ⟨k, hk.symm⟩ hn
    · rw [hk, hodd k]; simp
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b hab; simp only at hab; omega
  have h2 := (hinj.hasSum_iff hz).2 h
  convert h2 using 1
  funext k
  simp only [Function.comp]
  rw [binomialWeight_moment_identity t _ k]
  rw [show (∫ ω, Z ω ^ (2*k) ∂μ) / (((2*k).factorial : ℝ) / (2^k * (k.factorial : ℝ))) =
      uniformMomentRatio M k from actual_uniform_sum_moment_ratio U hU hind hlaw M k hM]

/-- The same identity at the raw scale `α = c M`, for every `c ≠ 0`. -/
theorem raw_uniform_kernel_hasSum
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw) (c : ℝ) (hc : c ≠ 0)
    (M : ℕ) (hM : M ≠ 0) :
    HasSum (fun k => binomialWeight (1/(12*c)) k * (uniformMomentRatio M k) ^ 2)
      (∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) * (∑ i ∈ range M, U i xy.2) / (c * (M:ℝ)))
        ∂μ.prod μ) := by
  have h := uniform_exponential_integral_hasSum U hU hind hlaw M hM (1/(12*c))
  convert h using 1
  apply integral_congr_ae
  filter_upwards with xy
  rw [standardizedUniformSum, standardizedUniformSum, standardized_exponent_identity c _ _ hc M hM]

theorem centralCoefficient_ge (k : ℕ) : 1 / (2 * ((k:ℝ) + 1)) ≤ centralCoefficient k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hrec := centralCoefficient_recurrence k
    have hk : (0:ℝ) < k + 1 := by positivity
    have hc : centralCoefficient (k+1) = ((k + 1/2) * centralCoefficient k) / (k + 1) := by
      rw [eq_div_iff hk.ne']; linarith
    rw [hc]
    have h2 : (1:ℝ) / (2 * (((k+1:ℕ):ℝ) + 1)) ≤
        ((k + 1/2) * (1 / (2 * ((k:ℝ) + 1)))) / (k + 1) := by
      push_cast
      rw [mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    refine h2.trans ?_
    apply div_le_div_of_nonneg_right _ hk.le
    exact mul_le_mul_of_nonneg_left ih (by positivity)

/-- The partial sums of `binom(2k,k)/4^k` are unbounded. -/
theorem centralCoefficient_partial_unbounded :
    Tendsto (fun n => ∑ k ∈ range n, centralCoefficient k) atTop atTop := by
  have hh := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have h2 : Tendsto (fun n => (1/2:ℝ) * ∑ k ∈ range n, (1 / ((k:ℝ) + 1))) atTop atTop :=
    hh.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono (fun n => ?_) h2
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have := centralCoefficient_ge k
  calc (1/2:ℝ) * (1 / ((k:ℝ) + 1)) = 1 / (2 * ((k:ℝ) + 1)) := one_div_mul_one_div _ _
    _ ≤ centralCoefficient k := this

theorem binomialWeight_ge_central (t : ℝ) (ht : 1 ≤ t) (k : ℕ) :
    centralCoefficient k ≤ binomialWeight t k := by
  unfold binomialWeight centralCoefficient
  rw [Nat.centralBinom_eq_two_mul_choose]
  have h1 : (1:ℝ) ≤ t ^ (2*k) := one_le_pow₀ ht
  have h0 : (0:ℝ) ≤ ((2*k).choose k : ℝ) / 4^k := by positivity
  exact le_mul_of_one_le_right h0 h1

theorem uniformMomentRatio_tendsto_one (k : ℕ) :
    Tendsto (fun M : ℕ => uniformMomentRatio M k) atTop (nhds 1) := by
  have hp : Tendsto (fun M : ℕ => (uniformRatioPolynomial k).eval (1/(M:ℝ))) atTop
      (nhds ((uniformRatioPolynomial k).eval 0)) := by
    have h0 : Tendsto (fun M : ℕ => 1/(M:ℝ)) atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
    exact ((uniformRatioPolynomial k).continuous.tendsto 0).comp h0
  rw [uniformRatio_eval_zero] at hp
  refine hp.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with M hM
  exact (uniformMomentRatio_exact_polynomial M k hM).symm

/-- Divergence of the exact series at fixed `t ≥ 1`, by finite partial sums. -/
theorem uniform_norm_lower_bound_divergence (N : ℕ → ℝ) (t : ℝ) (ht : 1 ≤ t)
    (hN : ∀ M : ℕ, M ≠ 0 → HasSum (fun k => binomialWeight t k * (uniformMomentRatio M k) ^ 2)
      (N M)) :
    Tendsto N atTop atTop := by
  rw [tendsto_atTop]
  intro L
  obtain ⟨K, hK⟩ := (tendsto_atTop.mp centralCoefficient_partial_unbounded (L + 1)).exists
  have hlim : Tendsto (fun M : ℕ => ∑ k ∈ range K, binomialWeight t k * (uniformMomentRatio M k) ^ 2)
      atTop (nhds (∑ k ∈ range K, binomialWeight t k * 1 ^ 2)) := by
    apply tendsto_finset_sum
    intro k _
    exact ((uniformMomentRatio_tendsto_one k).pow 2).const_mul _
  have hG : L + 1 ≤ ∑ k ∈ range K, binomialWeight t k * 1 ^ 2 := by
    simp only [one_pow, mul_one]
    exact hK.trans (Finset.sum_le_sum (fun k _ => binomialWeight_ge_central t ht k))
  have hev := hlim.eventually (eventually_ge_nhds (show L < ∑ k ∈ range K,
    binomialWeight t k * 1 ^ 2 by linarith))
  filter_upwards [hev, eventually_ne_atTop 0] with M hM hM0
  have hle := sum_le_hasSum (range K) (fun k _ => mul_nonneg (binomialWeight_nonneg t k)
    (sq_nonneg _)) (hN M hM0)
  linarith

/-- **Theorem 9.6, branch `0 < c ≤ 1/12`**: `N_M(c) = E exp(S_M T_M/(cM)) → +∞`. -/
theorem critical_subcritical_norm_tendsto_atTop
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (c : ℝ) (hc0 : 0 < c) (hc : c ≤ 1/12) :
    Tendsto (fun M : ℕ => ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) *
      (∑ i ∈ range M, U i xy.2) / (c * (M:ℝ))) ∂μ.prod μ) atTop atTop := by
  apply uniform_norm_lower_bound_divergence _ (1/(12*c))
  · rw [le_div_iff₀ (by positivity)]; linarith
  · intro M hM
    exact raw_uniform_kernel_hasSum U hU hind hlaw c hc0.ne' M hM

/-- **Theorem 9.6, branch `0 < c ≤ 1/12`**: the vacuum probability `1/N_M(c) → 0`. -/
theorem critical_subcritical_vacuum_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (c : ℝ) (hc0 : 0 < c) (hc : c ≤ 1/12) :
    Tendsto (fun M : ℕ => 1 / ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) *
      (∑ i ∈ range M, U i xy.2) / (c * (M:ℝ))) ∂μ.prod μ) atTop (nhds 0) := by
  simp only [one_div]
  exact (critical_subcritical_norm_tendsto_atTop U hU hind hlaw c hc0 hc).inv_tendsto_atTop

end EulerianGrothendieck
