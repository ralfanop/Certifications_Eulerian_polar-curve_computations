import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearNorm
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# V007 — finite spectral-trace duality against real rank-one operators

This module proves the sharp finite-trace dual estimate for a REAL
Hilbert space, using its actual orthonormal basis. Unlike the coarse
estimate bounded by N times the operator norm, the coefficient here is
one for each rank-one nuclear term.

Subsequent work must extend this estimate to absolutely summable
rank-one series and pass N to infinity to prove optimality of the
specific positive Gegenbauer expansion.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The first N Hilbert-basis Fourier modes define a contractive
finite orthogonal projection, written as an explicit finite sum. -/
theorem realHilbertFiniteFourierProjection_norm_le
    (b : HilbertBasis ℕ ℝ H) (N : ℕ) (v : H) :
    ‖∑ n ∈ Finset.range N, (inner ℝ (b n) v) • b n‖ ≤ ‖v‖ := by
  let q : H := ∑ n ∈ Finset.range N, (inner ℝ (b n) v) • b n
  have hqnorm : ‖q‖ ^ 2 =
      ∑ n ∈ Finset.range N, (inner ℝ (b n) v) ^ 2 := by
    have hh := b.orthonormal.inner_sum
      (fun n => inner ℝ (b n) v)
      (fun n => inner ℝ (b n) v) (Finset.range N)
    change inner ℝ q q =
      ∑ n ∈ Finset.range N,
        (inner ℝ (b n) v) * (inner ℝ (b n) v) at hh
    rw [real_inner_self_eq_norm_sq] at hh
    simpa [pow_two] using hh
  have hbessel : ∑ n ∈ Finset.range N,
      (inner ℝ (b n) v) ^ 2 ≤ ‖v‖ ^ 2 := by
    have h := b.orthonormal.sum_inner_products_le
      (s := Finset.range N) v
    convert h using 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [Real.norm_eq_abs, sq_abs]
  have hqnonneg : 0 ≤ ‖q‖ := norm_nonneg _
  have hvnonneg : 0 ≤ ‖v‖ := norm_nonneg _
  change ‖q‖ ≤ ‖v‖
  nlinarith

/-- The finite diagonal trace of the real-Hilbert rank-one operator
equals the scalar pairing with the finite Fourier projection. -/
theorem realHilbertFiniteTrace_rankOne_eq
    (b : HilbertBasis ℕ ℝ H) (N : ℕ) (u v : H) :
    (∑ n ∈ Finset.range N,
      inner ℝ (b n) (rankOne ℝ u v (b n))) =
    inner ℝ
      (∑ n ∈ Finset.range N, (inner ℝ (b n) v) • b n) u := by
  calc
    (∑ n ∈ Finset.range N,
      inner ℝ (b n) (rankOne ℝ u v (b n))) =
        ∑ n ∈ Finset.range N,
          inner ℝ u ((inner ℝ (b n) v) • b n) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [InnerProductSpace.rankOne_apply,
        real_inner_smul_right]
      rw [real_inner_comm v (b n), real_inner_comm u (b n)]
    _ = inner ℝ u
        (∑ n ∈ Finset.range N, (inner ℝ (b n) v) • b n) := by
      rw [inner_sum]
    _ = inner ℝ
        (∑ n ∈ Finset.range N, (inner ℝ (b n) v) • b n) u :=
      real_inner_comm _ _

/-- The coefficient-one nuclear duality estimate, valid for ANY
real Hilbert vectors u,v, and ANY finite initial segment of a
complete orthonormal basis. -/
theorem realHilbertFiniteTrace_rankOne_abs_le
    (b : HilbertBasis ℕ ℝ H) (N : ℕ) (u v : H) :
    |∑ n ∈ Finset.range N,
      inner ℝ (b n) (rankOne ℝ u v (b n))| ≤
      ‖u‖ * ‖v‖ := by
  rw [realHilbertFiniteTrace_rankOne_eq b N u v]
  have hCS :
      |inner ℝ
        (∑ n ∈ Finset.range N, (inner ℝ (b n) v) • b n) u| ≤
      ‖∑ n ∈ Finset.range N, (inner ℝ (b n) v) • b n‖ * ‖u‖ := by
    simpa only [Real.norm_eq_abs] using
      norm_inner_le_norm (𝕜 := ℝ)
        (∑ n ∈ Finset.range N, (inner ℝ (b n) v) • b n) u
  calc
    _ ≤ ‖∑ n ∈ Finset.range N, (inner ℝ (b n) v) • b n‖ * ‖u‖ := hCS
    _ ≤ ‖v‖ * ‖u‖ := by
      gcongr
      exact realHilbertFiniteFourierProjection_norm_le b N v
    _ = ‖u‖ * ‖v‖ := mul_comm _ _

#print axioms GegenbauerFock.Ultraspherical.realHilbertFiniteFourierProjection_norm_le
#print axioms GegenbauerFock.Ultraspherical.realHilbertFiniteTrace_rankOne_eq
#print axioms GegenbauerFock.Ultraspherical.realHilbertFiniteTrace_rankOne_abs_le

end GegenbauerFock.Ultraspherical
