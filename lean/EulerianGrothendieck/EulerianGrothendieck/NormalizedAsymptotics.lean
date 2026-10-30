import EulerianGrothendieck.RawScaleAsymptotics

noncomputable section
open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory
namespace EulerianGrothendieck

def normalizedVacuumCoefficient (t : ℝ) (r : ℕ) : ℝ :=
  uniformVacuumCoefficient t r / Real.sqrt (1-t^2)

theorem normalizedVacuumCoefficient_zero (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    normalizedVacuumCoefficient t 0 = 1 := by
  have hs : 0 < Real.sqrt (1-t^2) := Real.sqrt_pos.2 (by nlinarith)
  rw [normalizedVacuumCoefficient, uniformVacuumCoefficient_zero_closed t ht0 ht1, div_self (ne_of_gt hs)]

/-- The normalized statement of the arbitrary-order theorem, with a positive
constant independent of M and with the threshold M=1. -/
theorem normalized_uniform_vacuum_all_orders
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
    (c : ℝ) (hc : 1/12 < c) (R : ℕ) :
    let t := 1/(12*c)
    ∃ K : ℝ, 0 < K ∧ ∀ M : ℕ, 1 ≤ M →
      |(1/(∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1)*(∑ i ∈ range M, U i xy.2)/(c*(M:ℝ))) ∂μ.prod μ)) /
        Real.sqrt (1-t^2) - 1 -
        ∑ r ∈ range R, normalizedVacuumCoefficient t (r+1)/(M:ℝ)^(r+1)| ≤ K/(M:ℝ)^(R+1) := by
  dsimp only
  have ht := normalized_scale_mem c hc
  have hs : 0 < Real.sqrt (1-(1/(12*c))^2) := Real.sqrt_pos.2 (by nlinarith [ht.1, ht.2])
  obtain ⟨K, hK, hrem⟩ := raw_uniform_vacuum_all_orders U hU hind hlaw c hc R
  refine ⟨K/Real.sqrt (1-(1/(12*c))^2)+1, by positivity, ?_⟩
  intro M hM
  have h := div_le_div_of_nonneg_right (hrem M (by omega)) hs.le
  rw [← abs_of_pos hs, ← abs_div] at h
  have he : (∑ r ∈ range (R+1), uniformVacuumCoefficient (1/(12*c)) r/(M:ℝ)^r) /
      Real.sqrt (1-(1/(12*c))^2) =
      1 + ∑ r ∈ range R, normalizedVacuumCoefficient (1/(12*c)) (r+1)/(M:ℝ)^(r+1) := by
    rw [Finset.sum_range_succ', add_div]
    simp only [pow_zero, div_one, uniformVacuumCoefficient_zero_closed _ ht.1 ht.2,
      div_self (ne_of_gt hs)]
    rw [Finset.sum_div]
    have hh : (∑ r ∈ range R, uniformVacuumCoefficient (1/(12*c)) (r+1)/(M:ℝ)^(r+1) /
        Real.sqrt (1-(1/(12*c))^2)) =
        ∑ r ∈ range R, normalizedVacuumCoefficient (1/(12*c)) (r+1)/(M:ℝ)^(r+1) := by
      apply Finset.sum_congr rfl
      intros
      simp only [normalizedVacuumCoefficient, div_right_comm]
    rw [hh, add_comm]
  rw [sub_div, he, sub_add_eq_sub_sub, abs_of_pos hs] at h
  calc
    _ ≤ (K/(M:ℝ)^(R+1))/Real.sqrt (1-(1/(12*c))^2) := h
    _ = (K/Real.sqrt (1-(1/(12*c))^2))/(M:ℝ)^(R+1) := div_right_comm _ _ _
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)

end EulerianGrothendieck
