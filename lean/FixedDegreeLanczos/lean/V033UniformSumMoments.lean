import V033UniformIntegrals
import Mathlib.Probability.Independence.Integration

/-! All moments of an arbitrary finite independent sum of centred uniforms.
The law assumption is the Lebesgue probability measure on a unit interval;
integrability and the moment recurrence are conclusions, not hypotheses. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace V033.UniformSum

def uniformLaw : Measure ℝ := volume.restrict (Ioc (-1/2:ℝ) (1/2))

def singleMoment (n : ℕ) : ℝ := ∫ x in (-1/2:ℝ)..(1/2), x^n

@[simp] theorem singleMoment_even (r : ℕ) :
    singleMoment (2*r) = 1 / ((4:ℝ)^r * (2*(r:ℝ)+1)) := uniform_even_integral r

@[simp] theorem singleMoment_odd (r : ℕ) : singleMoment (2*r+1) = 0 :=
  uniform_odd_integral r

@[simp] theorem singleMoment_zero : singleMoment 0 = 1 := by
  simpa using singleMoment_even 0
@[simp] theorem singleMoment_two : singleMoment 2 = 1/12 := by
  have h := singleMoment_even 1
  norm_num at h
  exact h
@[simp] theorem singleMoment_four : singleMoment 4 = 1/80 := by
  have h := singleMoment_even 2
  norm_num at h
  exact h

theorem uniformLaw_eq_closed : uniformLaw = volume.restrict (Icc (-1/2:ℝ) (1/2)) := by
  exact Measure.restrict_congr_set Ioc_ae_eq_Icc

def sumMoment : ℕ → ℕ → ℝ
  | 0, n => if n=0 then 1 else 0
  | M+1, n => ∑ k ∈ Finset.range (n+1),
      sumMoment M k * singleMoment (n-k) * (n.choose k : ℝ)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem uniform_all_moments {U : Ω → ℝ} (hU : Measurable U)
    (hlaw : μ.map U = uniformLaw) (n : ℕ) :
    Integrable (fun ω => U ω ^ n) μ ∧
      (∫ ω, U ω ^ n ∂μ) = singleMoment n := by
  have hc : Continuous (fun x : ℝ => x^n) := continuous_id.pow n
  have hi : Integrable (fun x : ℝ => x^n) uniformLaw :=
    hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have his : Integrable (fun x : ℝ => x^n) (μ.map U) := hlaw ▸ hi
  refine ⟨(integrable_map_measure hc.aestronglyMeasurable hU.aemeasurable).1 his, ?_⟩
  rw [← integral_map hU.aemeasurable hc.aestronglyMeasurable, hlaw]
  exact (intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ) ≤ 1/2)).symm

theorem independent_add_integrable_pow {X Y : Ω → ℝ}
    (hind : IndepFun X Y μ)
    (hX : ∀ n : ℕ, Integrable (fun ω => X ω ^ n) μ)
    (hY : ∀ n : ℕ, Integrable (fun ω => Y ω ^ n) μ) (n : ℕ) :
    Integrable (fun ω => (X ω + Y ω)^n) μ := by
  simp_rw [add_pow]
  apply integrable_finset_sum
  intro k hk
  exact ((hind.comp (measurable_id.pow_const k) (measurable_id.pow_const (n-k))).integrable_mul
    (hX k) (hY (n-k))).mul_const _

theorem independent_add_moment {X Y : Ω → ℝ}
    (hind : IndepFun X Y μ)
    (hX : ∀ n : ℕ, Integrable (fun ω => X ω ^ n) μ)
    (hY : ∀ n : ℕ, Integrable (fun ω => Y ω ^ n) μ) (n : ℕ) :
    (∫ ω, (X ω + Y ω)^n ∂μ) =
      ∑ k ∈ Finset.range (n+1),
      (∫ ω, X ω^k ∂μ) * (∫ ω, Y ω^(n-k) ∂μ) * (n.choose k:ℝ) := by
  simp_rw [add_pow]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_mul_const]
    congr 1
    simpa only [Function.comp_apply, id_eq] using
      (hind.comp (measurable_id.pow_const k) (measurable_id.pow_const (n-k))).integral_fun_mul_eq_mul_integral
        (hX k).aestronglyMeasurable (hY (n-k)).aestronglyMeasurable
  · intro k hk
    exact ((hind.comp (measurable_id.pow_const k) (measurable_id.pow_const (n-k))).integrable_mul
      (hX k) (hY (n-k))).mul_const _

/-- For every number of summands and every moment order, the actual probability
integral equals the recursively specified convolution moment. -/
theorem all_sum_moments [IsProbabilityMeasure μ] (U : ℕ → Ω → ℝ)
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = uniformLaw) (M n : ℕ) :
    Integrable (fun ω => (∑ i ∈ Finset.range M, U i ω)^n) μ ∧
    (∫ ω, (∑ i ∈ Finset.range M, U i ω)^n ∂μ) = sumMoment M n := by
  induction M generalizing n with
  | zero =>
    by_cases hn : n=0
    · simp [sumMoment, hn]
    · simp [sumMoment, hn, zero_pow hn]
  | succ M ih =>
    have hI : IndepFun (fun ω => ∑ i ∈ Finset.range M, U i ω) (U M) μ := by
      have he : (∑ i ∈ Finset.range M, U i) = (fun ω => ∑ i ∈ Finset.range M, U i ω) := by
        ext ω
        simp
      rw [← he]
      exact hind.indepFun_finset_sum_of_notMem hU (Finset.notMem_range_self (n := M))
    have hM := fun k => (ih k).1
    have h1 := fun k => (uniform_all_moments (hU M) (hlaw M) k).1
    simp only [Finset.sum_range_succ]
    refine ⟨independent_add_integrable_pow hI hM h1 n, ?_⟩
    rw [independent_add_moment hI hM h1, sumMoment]
    apply Finset.sum_congr rfl
    intro k hk
    rw [(ih k).2, (uniform_all_moments (hU M) (hlaw M) (n-k)).2]

#print axioms uniform_all_moments
#print axioms independent_add_moment
#print axioms all_sum_moments
end V033.UniformSum
