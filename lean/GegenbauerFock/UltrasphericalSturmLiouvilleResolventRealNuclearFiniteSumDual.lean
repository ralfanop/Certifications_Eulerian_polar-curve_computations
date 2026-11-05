import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearDualLower

/-!
# V007 — finite real nuclear-sum trace duality, sharp constant 1

Rather than expand inner products of operator-valued finite sums by
simplification, use the already certified continuous real-linear
finite Fourier trace functional. This retains the exact coefficient
one for arbitrary signed coefficients, and arbitrary left/right
real Hilbert vectors.

The generic infinite nuclear cost bound is separately kernel-certified
in `UltrasphericalSturmLiouvilleResolventRealNuclearDualLower`.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Sharp coefficient-one finite trace inequality for arbitrary finite
real signed rank-one sums. -/
theorem realHilbertFiniteTrace_rankOne_finset_sum_abs_le
    (b : HilbertBasis ℕ ℝ H) (N : ℕ) (s : Finset ℕ)
    (u v : ℕ → H) (β : ℕ → ℝ) :
    |∑ n ∈ Finset.range N,
      inner ℝ (b n)
        ((∑ k ∈ s, β k • rankOne ℝ (u k) (v k)) (b n))| ≤
      ∑ k ∈ s, ‖β k‖ * ‖u k‖ * ‖v k‖ := by
  let Φ : (H →L[ℝ] H) →L[ℝ] ℝ := realHilbertFiniteTraceCLM b N
  have hterm (k : ℕ) :
      ‖Φ (β k • rankOne ℝ (u k) (v k))‖ ≤
        ‖β k‖ * ‖u k‖ * ‖v k‖ := by
    have htrace :
        |Φ (rankOne ℝ (u k) (v k))| ≤ ‖u k‖ * ‖v k‖ := by
      rw [realHilbertFiniteTraceCLM_apply]
      exact realHilbertFiniteTrace_rankOne_abs_le b N (u k) (v k)
    have hscal :
        Φ (β k • rankOne ℝ (u k) (v k)) =
          β k • Φ (rankOne ℝ (u k) (v k)) := by
      exact map_smul Φ (β k) _
    rw [hscal, norm_smul, Real.norm_eq_abs]
    calc
      ‖β k‖ * |Φ (rankOne ℝ (u k) (v k))| ≤
          ‖β k‖ * (‖u k‖ * ‖v k‖) :=
        mul_le_mul_of_nonneg_left htrace (norm_nonneg _)
      _ = ‖β k‖ * ‖u k‖ * ‖v k‖ := by ring
  calc
    |∑ n ∈ Finset.range N,
      inner ℝ (b n)
        ((∑ k ∈ s, β k • rankOne ℝ (u k) (v k)) (b n))| =
        ‖Φ (∑ k ∈ s, β k • rankOne ℝ (u k) (v k))‖ := by
      rw [realHilbertFiniteTraceCLM_apply]
      exact (Real.norm_eq_abs _).symm
    _ = ‖∑ k ∈ s, Φ (β k • rankOne ℝ (u k) (v k))‖ := by
      rw [map_sum]
    _ ≤ ∑ k ∈ s, ‖Φ (β k • rankOne ℝ (u k) (v k))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ s, ‖β k‖ * ‖u k‖ * ‖v k‖ := by
      apply Finset.sum_le_sum
      intro k hk
      exact hterm k

#print axioms GegenbauerFock.Ultraspherical.realHilbertFiniteTrace_rankOne_finset_sum_abs_le

end GegenbauerFock.Ultraspherical
