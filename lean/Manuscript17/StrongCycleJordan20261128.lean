import Mathlib
import Manuscript17.StrongCycleOriginal20261127
import Manuscript17.StrongCycleChebyshev20261128
import Manuscript17.ChebyshevCriticalSpectrum20261128

noncomputable section
namespace Manuscript17.StrongCycleJordan

open Matrix Polynomial Module.End
open Manuscript17.StrongCycleOriginal Manuscript17.StrongCycleChebyshev
open Manuscript17.ChebyshevCriticalSpectrum

def A (n : ℕ) (w : ℂ) := original n (alpha n) (radius n) w

def normalization (n : ℕ) : ℂ := 2^(n+1)

theorem normalization_ne_zero (n : ℕ) : normalization n ≠ 0 := by
  unfold normalization
  exact pow_ne_zero _ (by norm_num)

theorem pencil_eq (n : ℕ) (w z : ℂ) :
    Matrix.scalar (Fin (n+2)) z - A n w =
      Manuscript17.StrongCycle.pencil n (fun i => z-alpha n i) (radius n) w := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [A, original, Manuscript17.StrongCycle.pencil, Matrix.scalar]
  · simp [A, original, Manuscript17.StrongCycle.pencil, Matrix.scalar, h, Matrix.diagonal_apply]
    split_ifs <;> ring

theorem scaled_charpoly (n : ℕ) (w : ℂ) :
    C (normalization n) * (A n w).charpoly = fiber (n+2 : ℤ) w := by
  apply Polynomial.funext
  intro z
  rw [eval_mul, eval_C, Matrix.eval_charpoly, pencil_eq, concrete_determinant, fiber_eval]
  unfold normalization
  field_simp

theorem minimal_eq_characteristic (n : ℕ) (w : ℂ) :
    minpoly ℂ (A n w) = (A n w).charpoly :=
  original_minpoly_eq_charpoly n (alpha n) (radius n) w (radius_ne_zero n)

theorem charpoly_derivative_relation (n : ℕ) (w : ℂ) :
    C (normalization n) * derivative (A n w).charpoly =
      derivative (fiber (n+2 : ℤ) w) := by
  have h := congrArg derivative (scaled_charpoly n w)
  simpa [derivative_mul] using h

theorem charpoly_second_relation (n : ℕ) (w : ℂ) :
    C (normalization n) * derivative (derivative (A n w).charpoly) =
      derivative (derivative (fiber (n+2 : ℤ) w)) := by
  have h := congrArg derivative (charpoly_derivative_relation n w)
  simpa [derivative_mul] using h

theorem algebraic_multiplicity_le_two (n : ℕ) (w z : ℂ) :
    rootMultiplicity z (A n w).charpoly ≤ 2 := by
  by_contra! h
  have h1 := isRoot_iterate_derivative_of_lt_rootMultiplicity
    (show 1 < rootMultiplicity z (A n w).charpoly by omega)
  have h2 := isRoot_iterate_derivative_of_lt_rootMultiplicity h
  change (derivative (A n w).charpoly).eval z = 0 at h1
  change (derivative (derivative (A n w).charpoly)).eval z = 0 at h2
  have e1 := congrArg (fun p : ℂ[X] => p.eval z) (charpoly_derivative_relation n w)
  have e2 := congrArg (fun p : ℂ[X] => p.eval z) (charpoly_second_relation n w)
  simp only [eval_mul, eval_C, h1, h2, mul_zero] at e1 e2
  exact (fiber_no_triple_derivative_zero (n+2 : ℤ) (by omega) w z e1.symm) e2.symm

theorem algebraic_multiplicity_le_one (n : ℕ) (w z : ℂ)
    (h1 : w ≠ 1) (h2 : w ≠ -1) :
    rootMultiplicity z (A n w).charpoly ≤ 1 := by
  by_contra! h
  have hz := isRoot_iterate_derivative_of_lt_rootMultiplicity
    (show 0 < rootMultiplicity z (A n w).charpoly by omega)
  have hd := isRoot_iterate_derivative_of_lt_rootMultiplicity h
  change (A n w).charpoly.eval z = 0 at hz
  change (derivative (A n w).charpoly).eval z = 0 at hd
  have e0 := congrArg (fun p : ℂ[X] => p.eval z) (scaled_charpoly n w)
  have e1 := congrArg (fun p : ℂ[X] => p.eval z) (charpoly_derivative_relation n w)
  simp only [eval_mul, eval_C, hz, hd, mul_zero] at e0 e1
  exact (noncritical_fiber_derivative (n+2 : ℤ) (by omega) w z h1 h2 e0.symm) e1.symm

theorem generalized_dimension (n : ℕ) (w z : ℂ) :
    Module.finrank ℂ (Module.End.maxGenEigenspace (A n w).mulVecLin z) =
      rootMultiplicity z (A n w).charpoly := by
  rw [LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_mulVecLin]

theorem generalized_dimension_le_two (n : ℕ) (w z : ℂ) :
    Module.finrank ℂ (Module.End.maxGenEigenspace (A n w).mulVecLin z) ≤ 2 := by
  rw [generalized_dimension]
  exact algebraic_multiplicity_le_two n w z

theorem generalized_dimension_le_one (n : ℕ) (w z : ℂ)
    (h1 : w ≠ 1) (h2 : w ≠ -1) :
    Module.finrank ℂ (Module.End.maxGenEigenspace (A n w).mulVecLin z) ≤ 1 := by
  rw [generalized_dimension]
  exact algebraic_multiplicity_le_one n w z h1 h2

/- Classical Jordan normal form input: a nonempty list of positive block
sizes has sum equal to the algebraic multiplicity and maximum equal to the
minimal-polynomial multiplicity. Equality of these multiplicities forces
one block. The theorem below proves the finite combinatorial implication;
existence and similarity of a Jordan normal form are not asserted here. -/
theorem single_block_of_sum_eq_max (l : List ℕ) (hpos : ∀ k ∈ l, 0 < k)
    (h : ∃ k ∈ l, l.sum = k) : ∃ k, l = [k] := by
  obtain ⟨k,hk,hs⟩ := h
  induction l with
  | nil => simp at hk
  | cons a l ih =>
    have ha : 0 < a := hpos a (by simp)
    have hp : ∀ j ∈ l, 0 < j := fun j hj => hpos j (by simp [hj])
    simp only [List.mem_cons] at hk
    rcases hk with rfl | hk
    · have hz : l.sum = 0 := by simp at hs; omega
      cases l with
      | nil => exact ⟨k,rfl⟩
      | cons c l =>
        have hc := hp c (by simp)
        simp at hz
        omega
    · have hle : k ≤ l.sum := List.le_sum_of_mem hk
      simp at hs
      omega

#print axioms normalization_ne_zero
#print axioms pencil_eq
#print axioms scaled_charpoly
#print axioms minimal_eq_characteristic
#print axioms charpoly_derivative_relation
#print axioms charpoly_second_relation
#print axioms algebraic_multiplicity_le_two
#print axioms algebraic_multiplicity_le_one
#print axioms generalized_dimension
#print axioms generalized_dimension_le_two
#print axioms generalized_dimension_le_one
#print axioms single_block_of_sum_eq_max
end Manuscript17.StrongCycleJordan
