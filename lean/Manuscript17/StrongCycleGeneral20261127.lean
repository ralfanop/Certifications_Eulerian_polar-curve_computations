import Mathlib

noncomputable section
namespace Manuscript17.StrongCycle

open Matrix Polynomial

/-! General order n+2, with zero-based indices. The diagonal of lambda I-M
is d; the upper diagonal is -r, and the lower-left corner is -r*w. -/

def pencil (n : ℕ) (d : Fin (n+2) → ℂ) (r w : ℂ) :
    Matrix (Fin (n+2)) (Fin (n+2)) ℂ :=
  fun i j => if i = j then d i else
    if i.val+1 = j.val then -r else
    if i.val = n+1 ∧ j.val = 0 then -r*w else 0

theorem pencil_diag (n : ℕ) (d : Fin (n+2) → ℂ) (r w : ℂ) (i : Fin (n+2)) :
    pencil n d r w i i = d i := by simp [pencil]

theorem pencil_super (n : ℕ) (d : Fin (n+2) → ℂ) (r w : ℂ)
    (i j : Fin (n+2)) (h : i.val+1 = j.val) :
    pencil n d r w i j = -r := by
  have hij : i ≠ j := by intro e; subst j; omega
  simp [pencil, hij, h]

theorem pencil_corner (n : ℕ) (d : Fin (n+2) → ℂ) (r w : ℂ) :
    pencil n d r w (Fin.last (n+1)) 0 = -r*w := by
  simp [pencil, Fin.ext_iff]

theorem pencil_column_zero (n : ℕ) (d : Fin (n+2) → ℂ) (r w : ℂ)
    (i : Fin (n+2)) (h0 : i ≠ 0) (hl : i ≠ Fin.last (n+1)) :
    pencil n d r w i 0 = 0 := by
  have hi : i.val ≠ n+1 := by
    intro hi
    apply hl
    apply Fin.ext
    exact hi
  simp [pencil, h0, hi]

/-- Laplace expansion: the first minor is upper triangular. -/
theorem upper_minor (n : ℕ) (d : Fin (n+2) → ℂ) (r w : ℂ) :
    ((pencil n d r w).submatrix Fin.succ Fin.succ).det =
      ∏ i : Fin (n+1), d i.succ := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [Matrix.submatrix, pencil]
  · intro i j hij
    have hval : j.val < i.val := hij
    have hne : i.succ ≠ j.succ := by intro h; have := congrArg Fin.val h; simp at this; omega
    have hstep : i.succ.val+1 ≠ j.succ.val := by simp; omega
    simp [Matrix.submatrix, pencil, hne, hstep]

/-- The last-row first-column minor is lower triangular, all diagonal entries -r. -/
theorem lower_minor (n : ℕ) (d : Fin (n+2) → ℂ) (r w : ℂ) :
    ((pencil n d r w).submatrix Fin.castSucc Fin.succ).det =
      (-r)^(n+1) := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [Matrix.submatrix, pencil_super]
  · intro i j hij
    have hval : i.val < j.val := hij
    have hne : i.castSucc ≠ j.succ := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    have hstep : i.castSucc.val+1 ≠ j.succ.val := by simp; omega
    simp [Matrix.submatrix, pencil, hne, hstep]

/-- All orders n+2, without assuming r or w nonzero. -/
theorem determinant (n : ℕ) (d : Fin (n+2) → ℂ) (r w : ℂ) :
    (pencil n d r w).det = (∏ i, d i) - r^(n+2)*w := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Fin.prod_univ_succ]
  have hsum :
      (∑ i : Fin (n+1), (-1:ℂ)^i.succ.val * pencil n d r w i.succ 0 *
        ((pencil n d r w).submatrix i.succ.succAbove Fin.succ).det) =
      (-1:ℂ)^(n+1) * (-r*w) * (-r)^(n+1) := by
    rw [Finset.sum_eq_single (Fin.last n)]
    · rw [show (Fin.last n).succ = Fin.last (n+1) by apply Fin.ext; rfl]
      simp only [Fin.val_last]
      rw [pencil_corner]
      congr 1
      have he : (Fin.last (n+1)).succAbove = (Fin.castSucc : Fin (n+1) → Fin (n+2)) := by
        funext i
        simp
      rw [he, lower_minor]
    · intro i _ hi
      have h0 : i.succ ≠ (0 : Fin (n+2)) := by simp
      have hl : i.succ ≠ Fin.last (n+1) := by
        intro h
        apply hi
        apply Fin.ext
        have hv := congrArg Fin.val h
        simp at hv ⊢
        omega
      rw [pencil_column_zero n d r w i.succ h0 hl]
      simp
    · simp
  rw [hsum]
  simp only [Fin.val_zero, pow_zero, one_mul]
  rw [pencil_diag]
  have he : (0 : Fin (n+2)).succAbove = (Fin.succ : Fin (n+1) → Fin (n+2)) := by
    funext i
    simp
  rw [he, upper_minor]
  rw [neg_pow, ← mul_assoc, ← mul_assoc]
  have hs : (-1:ℂ)^(n+1) * (-1)^(n+1) = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = d 0 * (∏ i : Fin (n+1), d i.succ) -
        ((-1:ℂ)^(n+1)*(-1)^(n+1))* (r^(n+1)*r*w) := by ring
    _ = _ := by rw [hs, pow_succ]; ring

/-- Nonzero-radius row recurrence determines all components from component 0.
This is the recurrence underlying the one-dimensional eigenspace property. -/
theorem recurrence_unique (n : ℕ) (d : Fin (n+2) → ℂ) (r : ℂ)
    (hr : r ≠ 0) (v : Fin (n+2) → ℂ) (h0 : v 0 = 0)
    (h : ∀ i : Fin (n+1), r * v i.succ = d i.castSucc * v i.castSucc) :
    v = 0 := by
  funext j
  have aux : ∀ k : ℕ, ∀ hk : k < n+2, v ⟨k,hk⟩ = 0 := by
    intro k
    induction k with
    | zero => intro hk; exact h0
    | succ k ih =>
      intro hk
      have hk' : k < n+1 := by omega
      let i : Fin (n+1) := ⟨k,hk'⟩
      have he := h i
      have hz : v i.castSucc = 0 := ih (by omega)
      rw [hz, mul_zero] at he
      exact (mul_eq_zero.mp he).resolve_left hr
  exact aux j.val j.isLt

/-- Scalar Chebyshev specialization of the general determinant, using the
classical root factorization and the exact radius normalization. -/
theorem chebyshev_determinant (n : ℕ) (alpha : Fin (n+2) → ℂ) (r w z : ℂ)
    (hr : r^(n+2) = 1/(2:ℂ)^(n+1))
    (hfactor : (∏ i, (z-alpha i)) =
      (Polynomial.Chebyshev.T ℂ (n+2 : ℤ)).eval z / (2:ℂ)^(n+1)) :
    (pencil n (fun i => z-alpha i) r w).det =
      ((Polynomial.Chebyshev.T ℂ (n+2 : ℤ)).eval z-w)/(2:ℂ)^(n+1) := by
  rw [determinant, hr, hfactor]
  ring

#print axioms pencil_diag
#print axioms pencil_super
#print axioms pencil_corner
#print axioms pencil_column_zero
#print axioms upper_minor
#print axioms lower_minor
#print axioms determinant
#print axioms recurrence_unique
#print axioms chebyshev_determinant

end Manuscript17.StrongCycle
