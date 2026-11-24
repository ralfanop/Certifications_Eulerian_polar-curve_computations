import Mathlib

/-! M13 Corollary 4.12, independent of the kernel computations in #558.
Operator-level Gram factor on real Hilbert spaces. The spectral trace
is expressed by actual finite sums and an infinite series of diagonal
matrix elements. The summability hypothesis is explicit: it must later
be discharged for the concrete L² integral operator from #558.
Complex Hilbert space, kernel-to-operator realization, free resolvent
identification and ordinary Fredholm determinant remain open. -/

namespace Manuscript13.BirmanOperator20261124
open scoped RealInnerProductSpace
noncomputable section

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [CompleteSpace G]

def gram (B : H →L[ℝ] G) : H →L[ℝ] H := B.adjoint.comp B

theorem gram_apply (B : H →L[ℝ] G) (x : H) :
    gram B x = B.adjoint (B x) := rfl

theorem gram_inner (B : H →L[ℝ] G) (x y : H) :
    inner ℝ (gram B x) y = inner ℝ (B x) (B y) := by
  rw [gram_apply]
  first | exact B.adjoint_inner_left (B x) y | exact? 

theorem gram_quadratic (B : H →L[ℝ] G) (x : H) :
    inner ℝ (gram B x) x = ‖B x‖ ^ 2 := by
  rw [gram_inner]
  exact real_inner_self_eq_norm_sq _

theorem gram_nonneg (B : H →L[ℝ] G) (x : H) :
    0 ≤ inner ℝ (gram B x) x := by
  rw [gram_quadratic]
  positivity

theorem gram_symmetric (B : H →L[ℝ] G) (x y : H) :
    inner ℝ (gram B x) y = inner ℝ x (gram B y) := by
  calc
    inner ℝ (gram B x) y = inner ℝ (B x) (B y) := gram_inner B x y
    _ = inner ℝ (B y) (B x) := by
      first | exact real_inner_comm _ _ | exact (real_inner_comm _ _).symm
    _ = inner ℝ (gram B y) x := (gram_inner B y x).symm
    _ = inner ℝ x (gram B y) := by
      first | exact real_inner_comm _ _ | exact (real_inner_comm _ _).symm

theorem gram_kernel_iff (B : H →L[ℝ] G) (x : H) :
    gram B x = 0 ↔ B x = 0 := by
  constructor
  · intro h
    have hq : ‖B x‖ ^ 2 = 0 := by
      rw [← gram_quadratic B x, h]
      simp
    have hz : ‖B x‖ = 0 := by nlinarith [norm_nonneg (B x)]
    exact norm_eq_zero.mp hz
  · intro h
    rw [gram_apply, h, map_zero]

theorem gram_finite_diagonal {ι : Type*} (B : H →L[ℝ] G)
    (e : ι → H) (s : Finset ι) :
    (∑ i ∈ s, inner ℝ (gram B (e i)) (e i)) =
      ∑ i ∈ s, ‖B (e i)‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro i hi
  exact gram_quadratic B (e i)

theorem gram_diagonal_summable (B : H →L[ℝ] G) (e : ℕ → H)
    (h : Summable (fun i => ‖B (e i)‖ ^ 2)) :
    Summable (fun i => inner ℝ (gram B (e i)) (e i)) := by
  simpa only [gram_quadratic] using h

theorem gram_diagonal_tsum (B : H →L[ℝ] G) (e : ℕ → H) :
    (∑' i, inner ℝ (gram B (e i)) (e i)) =
      ∑' i, ‖B (e i)‖ ^ 2 := by
  simp_rw [gram_quadratic]

theorem gram_trace_specialization (B : H →L[ℝ] G) (e : ℕ → H)
    (a κ : ℝ) (h : (∑' i, ‖B (e i)‖ ^ 2) = Real.pi / (4*a*κ)) :
    (∑' i, inner ℝ (gram B (e i)) (e i)) = Real.pi / (4*a*κ) := by
  rw [gram_diagonal_tsum, h]

end
end Manuscript13.BirmanOperator20261124

#print axioms Manuscript13.BirmanOperator20261124.gram_apply
#print axioms Manuscript13.BirmanOperator20261124.gram_inner
#print axioms Manuscript13.BirmanOperator20261124.gram_quadratic
#print axioms Manuscript13.BirmanOperator20261124.gram_nonneg
#print axioms Manuscript13.BirmanOperator20261124.gram_symmetric
#print axioms Manuscript13.BirmanOperator20261124.gram_kernel_iff
#print axioms Manuscript13.BirmanOperator20261124.gram_finite_diagonal
#print axioms Manuscript13.BirmanOperator20261124.gram_diagonal_summable
#print axioms Manuscript13.BirmanOperator20261124.gram_diagonal_tsum
#print axioms Manuscript13.BirmanOperator20261124.gram_trace_specialization
