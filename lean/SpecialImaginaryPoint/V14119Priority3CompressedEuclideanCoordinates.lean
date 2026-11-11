import Mathlib

/-!
# Priority 3: complex Hilbert compression into Euclidean coordinate vectors

Finite coefficient vectors associated to any orthonormal family in a
complex Hilbert space are genuine finite-dimensional Euclidean vectors.
Bessel's inequality shows their norms are <= the original Hilbert norms.
Their complex Gram products are EXACT truncated Parseval pairings.

These two identities allow the previously certified sharp mixed-Gram
determinant bounds to be applied to every finite Hilbert compression,
uniformly in the compression dimension. They do not by themselves
establish the universal Fredholm determinant on S₁(H).
-/

noncomputable section

namespace Manuscript14Priority3.CompressedEuclideanCoordinates

open InnerProductSpace
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The first N coefficients of x in an arbitrary indexed family,
as a vector with the genuine Euclidean (ℓ²) norm. -/
def coefficients (e : ℕ → E) (N : ℕ) (x : E) :
    EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun i : Fin N => inner ℂ (e i.val) x)

/-- Bessel: the squared Euclidean norm of the finite coefficient
vector is at most the squared Hilbert norm. -/
theorem coefficients_norm_sq_le (e : ℕ → E)
    (he : Orthonormal ℂ e) (N : ℕ) (x : E) :
    ‖coefficients e N x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  have h := he.sum_inner_products_le (s := Finset.range N) x
  simpa only [coefficients, PiLp.toLp_apply,
    Finset.sum_fin_eq_sum_range] using h

/-- The coordinate map is contractive, with exact constant one. -/
theorem coefficients_norm_le (e : ℕ → E)
    (he : Orthonormal ℂ e) (N : ℕ) (x : E) :
    ‖coefficients e N x‖ ≤ ‖x‖ := by
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (coefficients_norm_sq_le e he N x)

/-- The mixed Gram inner product of two coefficient vectors is
exactly the corresponding truncated Hilbert-basis Parseval pairing. -/
theorem coefficients_inner_eq_truncated (e : ℕ → E)
    (N : ℕ) (u v : E) :
    inner ℂ (coefficients e N v) (coefficients e N u) =
      ∑ k : Fin N,
        inner ℂ v (e k.val) * inner ℂ (e k.val) u := by
  rw [EuclideanSpace.inner_toLp_toLp]
  change (∑ k : Fin N,
      inner ℂ (e k.val) u * star (inner ℂ (e k.val) v)) = _
  apply Finset.sum_congr rfl
  intro k hk
  have hstar :
      star (inner ℂ (e k.val) v) = inner ℂ v (e k.val) := by
    simp [star_def, inner_conj_symm]
  rw [hstar]
  ring

#print axioms Manuscript14Priority3.CompressedEuclideanCoordinates.coefficients_norm_sq_le
#print axioms Manuscript14Priority3.CompressedEuclideanCoordinates.coefficients_norm_le
#print axioms Manuscript14Priority3.CompressedEuclideanCoordinates.coefficients_inner_eq_truncated

end Manuscript14Priority3.CompressedEuclideanCoordinates
