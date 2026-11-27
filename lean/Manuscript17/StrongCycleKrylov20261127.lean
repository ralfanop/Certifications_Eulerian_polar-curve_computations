import Mathlib

noncomputable section
namespace Manuscript17.StrongCycleKrylov

open Matrix

/-! The reverse ordering of the manuscript strong cycle: diagonal a,
subdiagonal r, top-right corner r*w. Start at the first coordinate in
this ordering (the last coordinate in the original ordering). -/

def matrix (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ) :
    Matrix (Fin (n+2)) (Fin (n+2)) ℂ :=
  fun i j => if i = j then a i else
    if i.val = j.val+1 then r else
    if i.val = 0 ∧ j.val = n+1 then r*w else 0

theorem row_succ (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ)
    (v : Fin (n+2) → ℂ) (i : Fin (n+1)) :
    (matrix n a r w).mulVec v i.succ =
      a i.succ * v i.succ + r * v i.castSucc := by
  classical
  unfold Matrix.mulVec dotProduct
  calc
    _ = ∑ j : Fin (n+2),
        ((if j = i.succ then a i.succ * v j else 0) +
         (if j = i.castSucc then r * v j else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      have hh : i.succ ≠ i.castSucc := by
        intro e
        have hv := congrArg Fin.val e
        simp at hv
      by_cases h1 : j = i.succ
      · subst j
        simp [matrix, hh]
      by_cases h2 : j = i.castSucc
      · subst j
        simp [matrix, hh, Ne.symm hh]
      have hs : i.val ≠ j.val := by
        intro e
        apply h2
        apply Fin.ext
        exact e.symm
      simp [matrix, h1, Ne.symm h1, h2, hs, Ne.symm hs]
    _ = _ := by simp [Finset.sum_add_distrib]

def seed (n : ℕ) : Fin (n+2) → ℂ :=
  fun i => if i = 0 then 1 else 0

def iterate (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ) :
    ℕ → Fin (n+2) → ℂ
  | 0 => seed n
  | k+1 => (matrix n a r w).mulVec (iterate n a r w k)

theorem support (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ)
    (k : ℕ) (i : Fin (n+2)) (h : k < i.val) :
    iterate n a r w k i = 0 := by
  induction k generalizing i with
  | zero =>
    have hne : i ≠ 0 := by intro e; subst i; simp at h
    simp [iterate, seed, hne]
  | succ k ih =>
    cases i using Fin.cases with
    | zero => simp at h
    | succ i =>
      rw [iterate, row_succ]
      have h1 : k < i.succ.val := by omega
      have h2 : k < i.castSucc.val := by omega
      rw [ih i.succ h1, ih i.castSucc h2]
      ring

theorem pivot (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ)
    (k : ℕ) (i : Fin (n+2)) (h : i.val = k) :
    iterate n a r w k i = r^k := by
  induction k generalizing i with
  | zero =>
    have he : i = 0 := Fin.ext h
    subst i
    simp [iterate, seed]
  | succ k ih =>
    cases i using Fin.cases with
    | zero => simp at h
    | succ i =>
      rw [iterate, row_succ]
      have h1 : k < i.succ.val := by omega
      have h2 : i.castSucc.val = k := by omega
      rw [support n a r w k i.succ h1, ih i.castSucc h2, pow_succ]
      ring

def krylov (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ) :
    Matrix (Fin (n+2)) (Fin (n+2)) ℂ :=
  fun i j => iterate n a r w j.val i

theorem krylov_upper (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ) :
    (krylov n a r w).IsUpperTriangular := by
  intro i j h
  exact support n a r w j.val i h

theorem krylov_det (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ) :
    (krylov n a r w).det = ∏ j : Fin (n+2), r^j.val := by
  rw [Matrix.det_of_isUpperTriangular (krylov_upper n a r w)]
  apply Finset.prod_congr rfl
  intro j _
  exact pivot n a r w j.val j rfl

theorem krylov_det_ne_zero (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ) (hr : r ≠ 0) :
    (krylov n a r w).det ≠ 0 := by
  rw [krylov_det]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero j.val hr

/-- The actual Krylov columns are linearly independent, for all orders and w. -/
theorem krylov_linearIndependent (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ) (hr : r ≠ 0) :
    LinearIndependent ℂ (fun j : Fin (n+2) => iterate n a r w j.val) := by
  exact Matrix.linearIndependent_cols_of_det_ne_zero (krylov_det_ne_zero n a r w hr)

#print axioms row_succ
#print axioms support
#print axioms pivot
#print axioms krylov_upper
#print axioms krylov_det
#print axioms krylov_det_ne_zero
#print axioms krylov_linearIndependent

end Manuscript17.StrongCycleKrylov
