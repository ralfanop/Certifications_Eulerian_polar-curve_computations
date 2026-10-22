import V033Core
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! Finite first-order algebra for arbitrary polynomial matrices. -/
noncomputable section
namespace V033.Jet
open Polynomial Matrix Finset

def Eq1 (p q : ℝ[X]) : Prop := p.coeff 0 = q.coeff 0 ∧ p.coeff 1 = q.coeff 1

theorem mul_coeff_one (p q : ℝ[X]) :
    (p*q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  rw [coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ]

theorem Eq1.refl (p : ℝ[X]) : Eq1 p p := ⟨rfl,rfl⟩
theorem Eq1.add {p q r s : ℝ[X]} (h : Eq1 p q) (h' : Eq1 r s) :
    Eq1 (p+r) (q+s) := by
  constructor <;> simp only [coeff_add, h.1, h.2, h'.1, h'.2]
theorem Eq1.mul {p q r s : ℝ[X]} (h : Eq1 p q) (h' : Eq1 r s) :
    Eq1 (p*r) (q*s) := by
  constructor
  · have hc (f g : ℝ[X]) : (f*g).coeff 0 = f.coeff 0 * g.coeff 0 := by
      rw [coeff_mul]
      simp
    simp only [hc, h.1, h'.1]
  · simp only [mul_coeff_one, h.1, h.2, h'.1, h'.2]
theorem Eq1.smul (a : ℤˣ) {p q : ℝ[X]} (h : Eq1 p q) : Eq1 (a • p) (a • q) := by
  constructor <;> simp only [coeff_smul, h.1, h.2]

theorem sum_eq1 {ι : Type*} (s : Finset ι) (p q : ι → ℝ[X])
    (h : ∀ i ∈ s, Eq1 (p i) (q i)) : Eq1 (∑ i ∈ s,p i) (∑ i ∈ s,q i) := by
  constructor <;> simp only [finset_sum_coeff]
  · exact sum_congr rfl (fun i hi => (h i hi).1)
  · exact sum_congr rfl (fun i hi => (h i hi).2)

theorem prod_eq1 {ι : Type*} (s : Finset ι) (p q : ι → ℝ[X])
    (h : ∀ i ∈ s, Eq1 (p i) (q i)) : Eq1 (∏ i ∈ s,p i) (∏ i ∈ s,q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Eq1.refl _
  | @insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi]
    exact (h i (mem_insert_self _ _)).mul (ih (fun j hj => h j (mem_insert_of_mem hj)))

theorem det_eq1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ[X]) (h : ∀ i j, Eq1 (A i j) (B i j)) : Eq1 A.det B.det := by
  rw [det_apply, det_apply]
  apply sum_eq1
  intro σ hσ
  apply Eq1.smul
  exact prod_eq1 _ _ _ (fun i hi => h (σ i) i)

/-- The linear coefficient of a polynomial matrix with identity constant term
is the trace of its linear-coefficient matrix; higher coefficients cannot enter. -/
theorem det_linear_of_constant_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ[X]) (h0 : ∀ i j, (A i j).coeff 0 = (1 : Matrix ι ι ℝ) i j) :
    A.det.coeff 1 = ∑ i, (A i i).coeff 1 := by
  let B : Matrix ι ι ℝ := fun i j => (A i j).coeff 1
  have he : Eq1 A.det (1 + (X:ℝ[X]) • B.map C).det := by
    apply det_eq1
    intro i j
    constructor
    · rw [h0]
      by_cases hij : i=j <;> simp [Matrix.add_apply, Matrix.one_apply, hij]
    · by_cases hij : i=j <;> simp [Matrix.add_apply, Matrix.one_apply, hij, B, coeff_one]
  rw [he.2, Matrix.coeff_det_one_add_X_smul_one]
  rfl

#print axioms det_linear_of_constant_one
end V033.Jet
