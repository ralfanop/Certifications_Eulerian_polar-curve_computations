import Mathlib

/-!
# Priority 3 — finite nuclear families of unequal lengths: exact tail bookkeeping

For arbitrary vector families of lengths m and n, the tail indices in
Fin(m+n) are the image of Fin n under the canonical embedding
Fin.natAddEmb m. The corresponding index-mask removes precisely the
second concatenated family, not the first, and nuclear-cost sums over
the tail are exactly those over the second family.

These results concern finite-index bookkeeping only. They are needed
to instantiate the certified arbitrary-index Fredholm perturbation
bound for a base finite nuclear operator plus a separate finite
nuclear perturbation, without assuming equal representation lengths.
-/

noncomputable section

namespace Manuscript14Priority3.FinAppendTailIndex

/-- The trailing n positions of the concatenated family of length m+n. -/
def tailSet (m n : ℕ) : Finset (Fin (m + n)) :=
  (Finset.univ : Finset (Fin n)).map (Fin.natAddEmb m)

/-- Every index of the appended right family is in the tail set. -/
theorem natAdd_mem_tailSet (m n : ℕ) (j : Fin n) :
    Fin.natAdd m j ∈ tailSet m n := by
  change (Fin.natAddEmb m) j ∈
    (Finset.univ : Finset (Fin n)).map (Fin.natAddEmb m)
  exact Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩

/-- No index belonging to the first family is in the tail. -/
theorem castAdd_not_mem_tailSet (m n : ℕ) (i : Fin m) :
    Fin.castAdd n i ∉ tailSet m n := by
  intro hi
  obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
  have hv := congrArg Fin.val hji
  have hi_lt : i.val < m := i.isLt
  have heq : (Fin.natAddEmb m j).val = m + j.val := rfl
  have heq' : (Fin.castAdd n i).val = i.val := rfl
  rw [heq, heq'] at hv
  omega

/-- Zero out exactly those indices in the second appended family. -/
def zeroTail {E : Type*} [Zero E] (m n : ℕ) (u : Fin (m + n) → E) :
    Fin (m + n) → E :=
  fun i => if i ∈ tailSet m n then 0 else u i

/-- Zeroing the right-family tail of a concatenated presentation
is exactly concatenating the first family with the zero family. -/
theorem zeroTail_append {E : Type*} [Zero E] (m n : ℕ)
    (u : Fin m → E) (v : Fin n → E) :
    zeroTail m n (Fin.append u v) = Fin.append u (fun _ => 0) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp [zeroTail, castAdd_not_mem_tailSet]
  · simp [zeroTail, natAdd_mem_tailSet]

/-- Summation over all tail indices is exactly summation over the
second Fin n family, with no combinatorial correction. -/
theorem sum_tailSet (m n : ℕ) (f : Fin (m + n) → ℝ) :
    (∑ i ∈ tailSet m n, f i) =
      ∑ j : Fin n, f (Fin.natAdd m j) := by
  simp only [tailSet, Finset.sum_map, Fin.natAddEmb_apply]

/-- Exact identity for nuclear cost over the concatenated tail. -/
theorem nuclear_cost_tailSet {E : Type*} [SeminormedAddCommGroup E]
    (m n : ℕ) (u v : Fin m → E) (a b : Fin n → E) :
    (∑ i ∈ tailSet m n,
      ‖Fin.append u a i‖ * ‖Fin.append v b i‖) =
      ∑ j : Fin n, ‖a j‖ * ‖b j‖ := by
  rw [sum_tailSet]
  simp only [Fin.append_right]

#print axioms Manuscript14Priority3.FinAppendTailIndex.natAdd_mem_tailSet
#print axioms Manuscript14Priority3.FinAppendTailIndex.castAdd_not_mem_tailSet
#print axioms Manuscript14Priority3.FinAppendTailIndex.zeroTail_append
#print axioms Manuscript14Priority3.FinAppendTailIndex.sum_tailSet
#print axioms Manuscript14Priority3.FinAppendTailIndex.nuclear_cost_tailSet

end Manuscript14Priority3.FinAppendTailIndex
