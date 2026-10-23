import V033GramBasis

noncomputable section
namespace V033.Gram
open Polynomial Matrix Finset

/-- The defining algebraic properties of the monic three-term family. The
coefficient beta(n+1) is attached to P_n in the recurrence for P_(n+2). -/
structure IsLanczosFamily (L : ℝ[X] →ₗ[ℝ] ℝ) (P : ℕ → ℝ[X]) (β : ℕ → ℝ) : Prop where
  degree : ∀ n, (P n).natDegree = n
  monic : ∀ n, (P n).Monic
  orthogonal : ∀ n m, n ≠ m → L (P n*P m)=0
  initial_zero : P 0=1
  initial_one : P 1=X
  recurrence : ∀ n, P (n+2) = X*P (n+1)-C (β (n+1))*P n

def normSquare (L : ℝ[X] →ₗ[ℝ] ℝ) (P : ℕ → ℝ[X]) (n : ℕ) := L (P n*P n)
def normProduct (L : ℝ[X] →ₗ[ℝ] ℝ) (P : ℕ → ℝ[X]) (n : ℕ) :=
  ∏ i : Fin n, normSquare L P i.val

theorem linear_C_mul (L : ℝ[X] →ₗ[ℝ] ℝ) (a : ℝ) (p : ℝ[X]) :
    L (C a*p)=a*L p := by rw [← smul_eq_C_mul, map_smul]; rfl

theorem normProduct_succ (L : ℝ[X] →ₗ[ℝ] ℝ) (P : ℕ → ℝ[X]) (n : ℕ) :
    normProduct L P (n+1)=normProduct L P n*normSquare L P n := by
  unfold normProduct
  rw [Fin.prod_univ_castSucc]
  rfl

theorem IsLanczosFamily.norm_recurrence {L : ℝ[X] →ₗ[ℝ] ℝ}
    {P : ℕ → ℝ[X]} {β : ℕ → ℝ} (h : IsLanczosFamily L P β) (j : ℕ) :
    normSquare L P (j+1) = β (j+1)*normSquare L P j := by
  have hc : L (X*P (j+1)*P j) = normSquare L P (j+1) := by
    cases j with
    | zero =>
      simp only [zero_add, h.initial_zero, h.initial_one, mul_one, normSquare]
    | succ j =>
      have he : X*P (j+1)=P (j+2)+C (β (j+1))*P j := by rw [h.recurrence j]; ring
      rw [show X*P (j+1+1)*P (j+1) = P (j+2)*(X*P (j+1)) by ring, he, mul_add, map_add]
      rw [show P (j+2)*(C (β (j+1))*P j) = C (β (j+1))*(P (j+2)*P j) by ring,
        linear_C_mul, h.orthogonal (j+2) j (by omega), mul_zero, add_zero]
      rfl
  have hz := h.orthogonal (j+2) j (by omega)
  rw [h.recurrence j, sub_mul, map_sub,
    show C (β (j+1))*P j*P j = C (β (j+1))*(P j*P j) by ring,
    linear_C_mul, hc] at hz
  exact sub_eq_zero.mp hz

theorem IsLanczosFamily.determinant_product {L : ℝ[X] →ₗ[ℝ] ℝ}
    {P : ℕ → ℝ[X]} {β : ℕ → ℝ} (h : IsLanczosFamily L P β) (n : ℕ) :
    (hankel L n).det = normProduct L P n := by
  exact orthogonal_gram_det L (fun i : Fin n => P i.val)
    (fun i => h.degree _) (fun i => h.monic _)
    (fun i j hij => h.orthogonal _ _ (Fin.val_ne_of_ne hij))

/-- Determinant formula derived from the defining recurrence, not postulated. -/
theorem IsLanczosFamily.coefficient_as_determinants {L : ℝ[X] →ₗ[ℝ] ℝ}
    {P : ℕ → ℝ[X]} {β : ℕ → ℝ} (h : IsLanczosFamily L P β) (j : ℕ)
    (hd : (hankel L (j+1)).det ≠ 0) :
    β (j+1) = (hankel L (j+2)).det*(hankel L j).det / (hankel L (j+1)).det^2 := by
  simp only [h.determinant_product] at hd ⊢
  have hp := normProduct_succ L P j
  have hn : normProduct L P j ≠ 0 := by rw [hp] at hd; exact (mul_ne_zero_iff.mp hd).1
  have hs : normSquare L P j ≠ 0 := by rw [hp] at hd; exact (mul_ne_zero_iff.mp hd).2
  rw [normProduct_succ L P (j+1), hp, h.norm_recurrence j]
  field_simp

#print axioms IsLanczosFamily.coefficient_as_determinants
end V033.Gram
