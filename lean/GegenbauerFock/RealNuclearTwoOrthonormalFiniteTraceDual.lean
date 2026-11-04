import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearFiniteDual

/-!
# V007 — real two-orthonormal-family finite singular trace duality

The source and target families are independently orthonormal in one
real Hilbert space, but NEITHER is required to be complete. Their
closed spans may differ, and no global unitary phase is assumed.

This fills the coefficient-one finite duality step required for
compact operators whose kernel and cokernel have different dimensions.
The key contraction sends the source Fourier coefficients of a vector
into a finite orthonormal TARGET family; its norm is bounded using
Bessel on the SOURCE family and orthogonality on the TARGET family.

The generic nuclear sum and infinite-series extensions are separate
proof obligations; this source proves the sharp rank-one estimate.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The mixed finite Fourier transform between arbitrary independent
real orthonormal families is contractive. No complete basis, common
span, or unitary extension is required. -/
theorem realTwoOrthonormalFiniteTransfer_norm_le
    (b c : ℕ → H) (hb : Orthonormal ℝ b)
    (hc : Orthonormal ℝ c) (N : ℕ) (v : H) :
    ‖∑ n ∈ Finset.range N, (inner ℝ (b n) v) • c n‖ ≤ ‖v‖ := by
  let q : H := ∑ n ∈ Finset.range N, (inner ℝ (b n) v) • c n
  have hqnorm : ‖q‖ ^ 2 =
      ∑ n ∈ Finset.range N, (inner ℝ (b n) v) ^ 2 := by
    have hh := hc.inner_sum
      (fun n => inner ℝ (b n) v)
      (fun n => inner ℝ (b n) v) (Finset.range N)
    change inner ℝ q q =
      ∑ n ∈ Finset.range N,
        (inner ℝ (b n) v) * (inner ℝ (b n) v) at hh
    rw [real_inner_self_eq_norm_sq] at hh
    simpa [pow_two] using hh
  have hbessel :
      ∑ n ∈ Finset.range N, (inner ℝ (b n) v) ^ 2 ≤ ‖v‖ ^ 2 := by
    have h := hb.sum_inner_products_le
      (s := Finset.range N) v
    convert h using 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [Real.norm_eq_abs, sq_abs]
  have hqpos : 0 ≤ ‖q‖ := norm_nonneg _
  have hvpos : 0 ≤ ‖v‖ := norm_nonneg _
  change ‖q‖ ≤ ‖v‖
  nlinarith

/-- Exact mixed finite trace evaluation of one real rank-one
operator, with possibly incomplete and incompatible source/target
orthonormal families. -/
theorem realTwoOrthonormalFiniteTrace_rankOne_eq
    (b c : ℕ → H) (N : ℕ) (u v : H) :
    (∑ n ∈ Finset.range N,
       inner ℝ (c n) (rankOne ℝ u v (b n))) =
      inner ℝ
        (∑ n ∈ Finset.range N,
          (inner ℝ (b n) v) • c n) u := by
  calc
    (∑ n ∈ Finset.range N,
       inner ℝ (c n) (rankOne ℝ u v (b n))) =
      ∑ n ∈ Finset.range N,
        inner ℝ ((inner ℝ (b n) v) • c n) u := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [InnerProductSpace.rankOne_apply,
        real_inner_smul_right, real_inner_smul_left]
      rw [real_inner_comm v (b n)]
      ring
    _ = inner ℝ
          (∑ n ∈ Finset.range N,
            (inner ℝ (b n) v) • c n) u := by
      rw [sum_inner]

/-- Sharp constant-one mixed trace dual for arbitrary orthonormal
source/target families and a real rank-one Hilbert operator. -/
theorem realTwoOrthonormalFiniteTrace_rankOne_abs_le
    (b c : ℕ → H) (hb : Orthonormal ℝ b)
    (hc : Orthonormal ℝ c) (N : ℕ) (u v : H) :
    |∑ n ∈ Finset.range N,
      inner ℝ (c n) (rankOne ℝ u v (b n))| ≤
      ‖u‖ * ‖v‖ := by
  rw [realTwoOrthonormalFiniteTrace_rankOne_eq b c N u v]
  have hCS :
      |inner ℝ
        (∑ n ∈ Finset.range N,
          (inner ℝ (b n) v) • c n) u| ≤
        ‖∑ n ∈ Finset.range N,
          (inner ℝ (b n) v) • c n‖ * ‖u‖ := by
    simpa only [Real.norm_eq_abs] using
      norm_inner_le_norm (𝕜 := ℝ)
        (∑ n ∈ Finset.range N,
          (inner ℝ (b n) v) • c n) u
  calc
    _ ≤ ‖∑ n ∈ Finset.range N,
            (inner ℝ (b n) v) • c n‖ * ‖u‖ := hCS
    _ ≤ ‖v‖ * ‖u‖ := by
      gcongr
      exact realTwoOrthonormalFiniteTransfer_norm_le b c hb hc N v
    _ = ‖u‖ * ‖v‖ := mul_comm _ _

#print axioms GegenbauerFock.Ultraspherical.realTwoOrthonormalFiniteTransfer_norm_le
#print axioms GegenbauerFock.Ultraspherical.realTwoOrthonormalFiniteTrace_rankOne_eq
#print axioms GegenbauerFock.Ultraspherical.realTwoOrthonormalFiniteTrace_rankOne_abs_le

end GegenbauerFock.Ultraspherical
