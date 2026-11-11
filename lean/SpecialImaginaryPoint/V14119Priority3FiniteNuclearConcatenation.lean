import SpecialImaginaryPoint.V14119Priority3FiniteIntrinsicFunctional
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Priority 3 — exact finite nuclear concatenation in genuine CFC-S₁

Two arbitrary finite CFC trace-class rank-one presentations can be
concatenated using `Fin.append`. The resulting genuine trace-class
operator is exactly the sum of the original two, and the nuclear cost
is exactly additive. Removing the second family (zero left vectors)
leaves the first operator unchanged. The operator difference is the
second genuine CFC trace-class operator and its trace norm is bounded
by the second family's nuclear mass.

These are the operatorial bridges needed to apply certified
multi-index Fredholm determinant inequalities to presentations
of different lengths. No claim of optimal trace-norm determinant
perturbation, infinite extension, or holomorphy is made here.
-/

noncomputable section
namespace Manuscript14Priority3.FiniteNuclearConcatenation

open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.NuclearRankOne
open Manuscript14Priority3.FiniteNuclearFredholm

/-- Concatenating arbitrary finite nuclear families gives exactly
the sum of their genuine CFC Schatten-S₁ operators. -/
theorem finiteNuclear_append_eq_add (m n : ℕ)
    (u v : Fin m → H) (a b : Fin n → H) :
    finiteNuclear (m + n) (Fin.append u a) (Fin.append v b) =
      finiteNuclear m u v + finiteNuclear n a b := by
  unfold finiteNuclear
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- The total finite nuclear mass is exactly additive under
concatenation, without dimension-dependent constants. -/
theorem nuclear_mass_append_eq_add (m n : ℕ)
    (u v : Fin m → H) (a b : Fin n → H) :
    (∑ i : Fin (m + n),
        ‖Fin.append u a i‖ * ‖Fin.append v b i‖) =
      (∑ i : Fin m, ‖u i‖ * ‖v i‖) +
        (∑ j : Fin n, ‖a j‖ * ‖b j‖) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- A nuclear rank-one Hilbert map with zero left vector is the
zero element of actual CFC-S₁, from the exact trace-norm identity. -/
theorem rankOneS1_zero_left (v : H) :
    rankOneS1 (0 : H) v = 0 := by
  apply norm_eq_zero.mp
  rw [rankOneS1_norm_eq]
  simp

/-- Concatenating a zeroed second left-vector family leaves the
genuine CFC trace-class operator of the first family unchanged. -/
theorem finiteNuclear_append_zero_right (m n : ℕ)
    (u v : Fin m → H) (b : Fin n → H) :
    finiteNuclear (m + n) (Fin.append u (fun _ => 0))
        (Fin.append v b) = finiteNuclear m u v := by
  rw [finiteNuclear_append_eq_add]
  have hz : finiteNuclear n (fun _ : Fin n => (0 : H)) b = 0 := by
    unfold finiteNuclear
    simp [rankOneS1_zero_left]
  rw [hz, add_zero]

/-- Replacing zero right-family nuclear terms by actual ones is
EXACTLY the right CFC-S₁ operator, independent of the family lengths. -/
theorem finiteNuclear_append_sub_zero_right (m n : ℕ)
    (u v : Fin m → H) (a b : Fin n → H) :
    finiteNuclear (m + n) (Fin.append u a) (Fin.append v b) -
      finiteNuclear (m + n) (Fin.append u (fun _ => 0))
        (Fin.append v b) = finiteNuclear n a b := by
  rw [finiteNuclear_append_eq_add, finiteNuclear_append_zero_right]
  abel

/-- Nuclear-cost control of the actual CFC-S₁ operator difference.
This mass is an upper bound for the norm, not the reverse. -/
theorem finiteNuclear_append_sub_norm_le_mass (m n : ℕ)
    (u v : Fin m → H) (a b : Fin n → H) :
    ‖finiteNuclear (m + n) (Fin.append u a) (Fin.append v b) -
      finiteNuclear (m + n) (Fin.append u (fun _ => 0))
        (Fin.append v b)‖ ≤
      ∑ j : Fin n, ‖a j‖ * ‖b j‖ := by
  rw [finiteNuclear_append_sub_zero_right]
  unfold finiteNuclear
  calc
    ‖∑ j : Fin n, rankOneS1 (a j) (b j)‖ ≤
        ∑ j : Fin n, ‖rankOneS1 (a j) (b j)‖ := norm_sum_le _ _
    _ = ∑ j : Fin n, ‖a j‖ * ‖b j‖ := by
      simp only [rankOneS1_norm_eq]

#print axioms Manuscript14Priority3.FiniteNuclearConcatenation.finiteNuclear_append_eq_add
#print axioms Manuscript14Priority3.FiniteNuclearConcatenation.nuclear_mass_append_eq_add
#print axioms Manuscript14Priority3.FiniteNuclearConcatenation.rankOneS1_zero_left
#print axioms Manuscript14Priority3.FiniteNuclearConcatenation.finiteNuclear_append_zero_right
#print axioms Manuscript14Priority3.FiniteNuclearConcatenation.finiteNuclear_append_sub_zero_right
#print axioms Manuscript14Priority3.FiniteNuclearConcatenation.finiteNuclear_append_sub_norm_le_mass

end Manuscript14Priority3.FiniteNuclearConcatenation
