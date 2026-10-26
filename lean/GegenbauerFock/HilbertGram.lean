import Mathlib

/-!
# V007: rigorously verified Hilbert-space adjoint and Gram identities

These statements apply to any bounded complex-linear map between
Hilbert spaces. The special Gegenbauer–Fock map C : L²(νλ) → Fockα
has NOT yet been constructed, so they are not a certification of
its explicit evaluation adjoint or of its compactness.

Theorems here provide exact generic tools needed for the final
operator proof. No sorry, admits, opaque assumptions about C or
custom axioms are used.
-/

open scoped InnerProduct

namespace GegenbauerFock.HilbertGram

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
variable [CompleteSpace E] [CompleteSpace F]

/-- Genuine bounded Gram operator on the source Hilbert space. -/
noncomputable def gram (T : E →L[ℂ] F) : E →L[ℂ] E :=
  T.adjoint ∘L T

/-- Exact Gram pairing, with the complex inner product convention. -/
theorem gram_inner (T : E →L[ℂ] F) (x y : E) :
    inner ℂ (gram T x) y = inner ℂ (T x) (T y) := by
  unfold gram
  exact T.adjoint_inner_left y (T x)

/-- The general bounded Gram operator is self-adjoint. -/
theorem gram_adjoint (T : E →L[ℂ] F) :
    (gram T).adjoint = gram T := by
  unfold gram
  simp

/-- Positivity of the Gram quadratic form in the correct real part. -/
theorem gram_re_nonneg (T : E →L[ℂ] F) (x : E) :
    0 ≤ Complex.re (inner ℂ (gram T x) x) := by
  change 0 ≤ Complex.re (inner ℂ ((T.adjoint ∘L T) x) x)
  rw [← T.apply_norm_sq_eq_inner_adjoint_left x]
  positivity

/-- A compact bounded operator has a compact Gram operator. This
does NOT establish that the not-yet-constructed V007 C is compact. -/
theorem gram_compact (T : E →L[ℂ] F)
    (hT : IsCompactOperator T) :
    IsCompactOperator (gram T) := by
  change IsCompactOperator (fun x : E => T.adjoint (T x))
  exact hT.clm_comp T.adjoint

/-- The squared norm of the original bounded operator at x is
the quadratic form of its Gram operator. -/
theorem gram_norm_sq (T : E →L[ℂ] F) (x : E) :
    ‖T x‖ ^ 2 = Complex.re (inner ℂ (gram T x) x) := by
  simpa only [gram] using (T.apply_norm_sq_eq_inner_adjoint_left x)

#print axioms GegenbauerFock.HilbertGram.gram_inner
#print axioms GegenbauerFock.HilbertGram.gram_adjoint
#print axioms GegenbauerFock.HilbertGram.gram_re_nonneg
#print axioms GegenbauerFock.HilbertGram.gram_compact
#print axioms GegenbauerFock.HilbertGram.gram_norm_sq

end GegenbauerFock.HilbertGram
