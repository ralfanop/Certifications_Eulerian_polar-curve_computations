import EulerianGrothendieck.FockVacuumProjection
import EulerianGrothendieck.CriticalSubcriticalVacuum
import EulerianGrothendieck.UniformParameterVacuum
import EulerianGrothendieck.CatalanLipschitzDirichlet

/-! # Assembly: the intrinsic Fock vacuum probability

With Task A the vacuum probability `p_{E,M}(α)` is defined inside `L²(μ_α)`
(`fockVacuumProbability`); these corollaries transfer Tasks B and I and Theorem 9.6 to it.

* `fock_vacuum_threshold_limit` (Theorem 9.6, both branches):
  `p_{E,M}(cM) → 0` for `0 < c ≤ 1/12` and `→ √(1 - 1/(144c²))` for `c > 1/12`;
* `fock_vacuum_uniform_parameters`: the reciprocal (vacuum) remainder is uniform in `c ≥ c0 > 1/12`. -/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Finset Filter Topology
namespace EulerianGrothendieck.Fock

theorem fockVacuumProbability_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    {c : ℝ} (hc : 0 < c) (M : ℕ) (hM : M ≠ 0) :
    fockVacuumProbability (c * M) M = 1 / ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) *
      (∑ i ∈ range M, U i xy.2) / (c * (M:ℝ))) ∂μ.prod μ := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  rw [fockVacuumProbability, (fock_vacuum_probability U hU hind hlaw M (mul_pos hc hMpos)).2.2]

/-- The limiting vacuum curve `p_∞(c)`. -/
def vacuumLimit (c : ℝ) : ℝ := if c ≤ 1/12 then 0 else Real.sqrt (1 - 1 / (144 * c ^ 2))

/-- **Theorem 9.6** for the intrinsic Fock vacuum probability, for every `c > 0`. -/
theorem fock_vacuum_threshold_limit {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (c : ℝ) (hc : 0 < c) :
    Tendsto (fun M : ℕ => fockVacuumProbability (c * M) M) atTop (𝓝 (vacuumLimit c)) := by
  have hev : ∀ᶠ M : ℕ in atTop, 1 / ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) *
      (∑ i ∈ range M, U i xy.2) / (c * (M:ℝ))) ∂μ.prod μ = fockVacuumProbability (c * M) M := by
    filter_upwards [eventually_ne_atTop 0] with M hM
    rw [fockVacuumProbability_eq U hU hind hlaw hc M hM]
  unfold vacuumLimit
  split_ifs with hcrit
  · exact (critical_subcritical_vacuum_tendsto_zero U hU hind hlaw c hc hcrit).congr' hev
  · push_neg at hcrit
    obtain ⟨K, hK, hrem⟩ := EulerianGrothendieck.raw_uniform_vacuum_all_orders U hU hind hlaw c hcrit 0
    have ht := normalized_scale_mem c hcrit
    have hcoef : uniformVacuumCoefficient (1/(12*c)) 0 = Real.sqrt (1 - 1 / (144 * c ^ 2)) := by
      rw [EulerianGrothendieck.Catalan.uniformVacuumCoefficient_zero _ ht.1 ht.2]
      congr 1
      rw [div_pow, one_pow, mul_pow]
      norm_num
    refine Tendsto.congr' hev ?_
    rw [← hcoef, Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M0, hM0⟩ := exists_nat_gt ((K + 1) / ε)
    refine ⟨M0 + 1, fun M hM => ?_⟩
    have hM' : M ≠ 0 := by omega
    have hMpos : (0:ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM'
    have hb := hrem M hM'
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, div_one, pow_one] at hb
    rw [Real.dist_eq]
    have hMgt : (K + 1) / ε < M := by
      have : (M0:ℝ) + 1 ≤ M := by exact_mod_cast hM
      linarith
    rw [div_lt_iff₀ hε] at hMgt
    calc _ ≤ K / M := hb
      _ < ε := by
        rw [div_lt_iff₀ hMpos]
        linarith

/-- **Task I for the Fock vacuum probability**: uniform in `c ≥ c0 > 1/12`. -/
theorem fock_vacuum_uniform_parameters {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (c0 : ℝ) (hc0 : 1/12 < c0) (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, c0 ≤ c → ∀ M : ℕ, M ≠ 0 →
      |fockVacuumProbability (c * M) M -
        ∑ r ∈ range (R+1), uniformVacuumCoefficient (1/(12*c)) r/(M:ℝ)^r| ≤ K/(M:ℝ)^(R+1) := by
  obtain ⟨K, hK, hrem⟩ := raw_uniform_vacuum_uniform_parameters U hU hind hlaw c0 hc0 R
  refine ⟨K, hK, fun c hc M hM => ?_⟩
  rw [fockVacuumProbability_eq U hU hind hlaw (by linarith) M hM]
  exact hrem c hc M hM

end EulerianGrothendieck.Fock
