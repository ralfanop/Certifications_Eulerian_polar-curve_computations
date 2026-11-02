import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearFiniteDual

/-!
# V007 — real finite nuclear-sum duality

Finite-sum extension of the coefficient-one rank-one estimate, for
arbitrary real signed coefficients and left/right vectors. No claim
about infinite series is made until the corresponding kernel audit.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Every finite nuclear sum obeys the sharp finite Fourier-trace
duality inequality, with constant one independently of N and s. -/
theorem realHilbertFiniteTrace_rankOne_finset_sum_abs_le
    (b : HilbertBasis ℕ ℝ H) (N : ℕ) (s : Finset ℕ)
    (u v : ℕ → H) (β : ℕ → ℝ) :
    |∑ n ∈ Finset.range N,
      inner ℝ (b n)
        ((∑ k ∈ s, β k • rankOne ℝ (u k) (v k)) (b n))| ≤
      ∑ k ∈ s, ‖β k‖ * ‖u k‖ * ‖v k‖ := by
  have hpoint (n : ℕ) :
      inner ℝ (b n)
        ((∑ k ∈ s, β k • rankOne ℝ (u k) (v k)) (b n)) =
      ∑ k ∈ s, β k * inner ℝ (b n) (rankOne ℝ (u k) (v k) (b n)) := by
    simp only [Finset.sum_apply, ContinuousLinearMap.smul_apply,
      inner_sum, real_inner_smul_right]
  have heq :
      (∑ n ∈ Finset.range N,
        inner ℝ (b n)
          ((∑ k ∈ s, β k • rankOne ℝ (u k) (v k)) (b n))) =
      ∑ k ∈ s, β k *
        (∑ n ∈ Finset.range N,
          inner ℝ (b n) (rankOne ℝ (u k) (v k) (b n))) := by
    calc
      _ = ∑ n ∈ Finset.range N, ∑ k ∈ s,
          β k * inner ℝ (b n) (rankOne ℝ (u k) (v k) (b n)) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact hpoint n
      _ = ∑ k ∈ s, ∑ n ∈ Finset.range N,
          β k * inner ℝ (b n) (rankOne ℝ (u k) (v k) (b n)) := by
            rw [Finset.sum_comm]
      _ = ∑ k ∈ s, β k *
          (∑ n ∈ Finset.range N,
            inner ℝ (b n) (rankOne ℝ (u k) (v k) (b n))) := by
            simp only [Finset.mul_sum]
  rw [heq]
  calc
    |∑ k ∈ s, β k *
      (∑ n ∈ Finset.range N,
        inner ℝ (b n) (rankOne ℝ (u k) (v k) (b n)))| ≤
      ∑ k ∈ s, |β k *
        (∑ n ∈ Finset.range N,
          inner ℝ (b n) (rankOne ℝ (u k) (v k) (b n)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ s, ‖β k‖ * ‖u k‖ * ‖v k‖ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, ← Real.norm_eq_abs]
      calc
        ‖β k‖ *
          |∑ n ∈ Finset.range N,
            inner ℝ (b n) (rankOne ℝ (u k) (v k) (b n))| ≤
          ‖β k‖ * (‖u k‖ * ‖v k‖) :=
            mul_le_mul_of_nonneg_left
              (realHilbertFiniteTrace_rankOne_abs_le b N (u k) (v k))
              (norm_nonneg _)
        _ = ‖β k‖ * ‖u k‖ * ‖v k‖ := by ring

#print axioms GegenbauerFock.Ultraspherical.realHilbertFiniteTrace_rankOne_finset_sum_abs_le

end GegenbauerFock.Ultraspherical
