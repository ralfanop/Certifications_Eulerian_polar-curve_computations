import V033DeterminantAsymptotic
import V033ProbabilityFunctional
import V033RecurrenceGram

noncomputable section
namespace V033.UniformSum
open Polynomial Matrix MeasureTheory ProbabilityTheory Finset

theorem raw_hankel_nonzero (M j : ℕ) (hM : M ≠ 0)
    (hd : (recurrenceDenominator j).eval (1/(M:ℝ)) ≠ 0) :
    (Gram.hankel (rawFunctional M) (j+1)).det ≠ 0 := by
  intro hz
  apply hd
  rw [recurrenceDenominator, eval_pow, hankel_scaling M _ hM, hz, mul_zero, zero_pow (by decide)]

theorem determinant_ratio_scaling (M j : ℕ) (hM : M ≠ 0)
    (hd : (recurrenceDenominator j).eval (1/(M:ℝ)) ≠ 0) :
    ((M:ℝ)/12) * ((recurrenceNumerator j).eval (1/(M:ℝ)) /
      (recurrenceDenominator j).eval (1/(M:ℝ))) =
    (Gram.hankel (rawFunctional M) (j+2)).det * (Gram.hankel (rawFunctional M) j).det /
      (Gram.hankel (rawFunctional M) (j+1)).det^2 := by
  have hm : (0:ℝ)<M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hmn := ne_of_gt hm
  have ha : Real.sqrt (12/(M:ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have he := scalingProduct_ne_zero _ ha j
  have hr := raw_hankel_nonzero M j hM hd
  have hp : Real.sqrt (12/(M:ℝ))^j ≠ 0 := pow_ne_zero _ ha
  have hs : Real.sqrt (12/(M:ℝ))^2 = 12/(M:ℝ) := Real.sq_sqrt (by positivity)
  have heq : (recurrenceNumerator j).eval (1/(M:ℝ)) /
      (recurrenceDenominator j).eval (1/(M:ℝ)) =
      Real.sqrt (12/(M:ℝ))^2 *
      ((Gram.hankel (rawFunctional M) (j+2)).det * (Gram.hankel (rawFunctional M) j).det /
      (Gram.hankel (rawFunctional M) (j+1)).det^2) := by
    rw [recurrenceNumerator, recurrenceDenominator, eval_mul, eval_pow]
    simp only [hankel_scaling M _ hM]
    rw [scalingProduct_succ, scalingProduct_succ, pow_succ]
    field_simp
    <;> ring
  rw [heq, hs]
  field_simp

/-- The complete all-degree two-term estimate for the monic recurrence family
of the uniform-sum moment functional. C and N may depend on j, but not on M. -/
theorem two_term_lanczos_asymptotic
    (P : ℕ → ℕ → ℝ[X]) (β : ℕ → ℕ → ℝ)
    (h : ∀ M : ℕ, 0 < M → Gram.IsLanczosFamily (rawFunctional M) (P M) (β M))
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 0 < N ∧ ∀ M : ℕ, N ≤ M →
      |β M (j+1) - ((j+1:ℝ)*M/12-(j+1:ℝ)*j/20)| ≤ C/(M:ℝ) := by
  obtain ⟨C,hC,N,hNpos,hN⟩ := original_scale_determinant_remainder j
  refine ⟨C,hC,N,hNpos,?_⟩
  intro M hM
  obtain ⟨hd,hb⟩ := hN M hM
  have hm : 0<M := lt_of_lt_of_le hNpos hM
  have hm0 := Nat.ne_of_gt hm
  rw [determinant_ratio_scaling M j hm0 hd,
    ← (h M hm).coefficient_as_determinants j (raw_hankel_nonzero M j hm0 hd)] at hb
  exact hb

/-- The same theorem expressed directly with probability integrals of the
actual independent uniform random variables. No assumed moment expansion,
Gaussian limit, bounded remainder, or coefficient formula is required. -/
theorem uniform_probability_two_term
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = uniformLaw)
    (P : ℕ → ℕ → ℝ[X]) (β : ℕ → ℕ → ℝ)
    (hdeg : ∀ M n, 0<M → (P M n).natDegree=n)
    (hmon : ∀ M n, 0<M → (P M n).Monic)
    (hortho : ∀ M n m, 0<M → n≠m →
      (∫ ω, (P M n).eval (∑ i ∈ range M, U i ω) *
        (P M m).eval (∑ i ∈ range M, U i ω) ∂μ) = 0)
    (hzero : ∀ M, 0<M → P M 0=1) (hone : ∀ M, 0<M → P M 1=X)
    (hrec : ∀ M n, 0<M → P M (n+2)=X*P M (n+1)-C (β M (n+1))*P M n)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 0 < N ∧ ∀ M : ℕ, N ≤ M →
      |β M (j+1) - ((j+1:ℝ)*M/12-(j+1:ℝ)*j/20)| ≤ C/(M:ℝ) := by
  apply two_term_lanczos_asymptotic P β
  intro M hM
  refine ⟨fun n => hdeg M n hM, fun n => hmon M n hM, ?_, hzero M hM, hone M hM,
    fun n => hrec M n hM⟩
  intro n m hnm
  rw [← (rawFunctional_actual U hU hind hlaw M (P M n*P M m)).2]
  simpa only [eval_mul] using hortho M n m hM hnm

#print axioms two_term_lanczos_asymptotic
#print axioms uniform_probability_two_term

/-- The canonical Hankel ratio, independently of any choice of polynomial family. -/
def canonicalCoefficient (M j : ℕ) : ℝ :=
  (Gram.hankel (rawFunctional M) (j+2)).det * (Gram.hankel (rawFunctional M) j).det /
    (Gram.hankel (rawFunctional M) (j+1)).det^2

theorem canonical_two_term (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 0 < N ∧ ∀ M : ℕ, N ≤ M →
      (Gram.hankel (rawFunctional M) (j+1)).det ≠ 0 ∧
      |canonicalCoefficient M j - ((j+1:ℝ)*M/12-(j+1:ℝ)*j/20)| ≤ C/(M:ℝ) := by
  obtain ⟨C,hC,N,hNpos,hN⟩ := original_scale_determinant_remainder j
  refine ⟨C,hC,N,hNpos,?_⟩
  intro M hM
  obtain ⟨hd,hb⟩ := hN M hM
  have hm0 : M ≠ 0 := by omega
  refine ⟨raw_hankel_nonzero M j hm0 hd, ?_⟩
  rw [determinant_ratio_scaling M j hm0 hd] at hb
  exact hb

def integralHankel {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : ℕ → Ω → ℝ) (M n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ ω, (∑ k ∈ range M, U k ω)^(i.val+j.val) ∂μ

theorem integral_hankel_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = uniformLaw) (M n : ℕ) :
    integralHankel μ U M n = Gram.hankel (rawFunctional M) n := by
  ext i j
  change (∫ ω, (∑ k ∈ range M, U k ω)^(i.val+j.val) ∂μ) = _
  rw [(all_sum_moments U hU hind hlaw M (i.val+j.val)).2]
  exact (rawFunctional_X_pow M (i.val+j.val)).symm

/-- An unconditional statement about the actual probability moments: the
Hankel quotient exists eventually and satisfies the asserted two-term bound.
Its identification with every monic Lanczos family is proved above. -/
theorem uniform_integral_hankel_two_term
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = uniformLaw) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 0 < N ∧ ∀ M : ℕ, N ≤ M →
      (integralHankel μ U M (j+1)).det ≠ 0 ∧
      |(integralHankel μ U M (j+2)).det*(integralHankel μ U M j).det /
          (integralHankel μ U M (j+1)).det^2 -
        ((j+1:ℝ)*M/12-(j+1:ℝ)*j/20)| ≤ C/(M:ℝ) := by
  simpa only [integral_hankel_eq U hU hind hlaw, canonicalCoefficient] using canonical_two_term j

#print axioms canonical_two_term
#print axioms uniform_integral_hankel_two_term
end V033.UniformSum
