import V033GaussianAlgebra
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section
namespace V033.Gaussian
open Polynomial Matrix

/-- Strict positivity of the Gaussian functional on every nonzero square. -/
theorem square_positive (p : ℝ[X]) (hp : p ≠ 0) : 0 < expectation (p*p) := by
  generalize hn : p.natDegree = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    let a := p.leadingCoeff
    let q := p - C a * H n
    have ha : a ≠ 0 := leadingCoeff_ne_zero.mpr hp
    have hqdeg : q.degree < p.degree := by
      refine Polynomial.degree_sub_lt ?_ hp ?_
      · rw [degree_C_mul ha, degree_eq_natDegree hp,
          degree_eq_natDegree (monic_H n).ne_zero, degree_H, hn]
      · rw [leadingCoeff_mul, leadingCoeff_C, (monic_H n), mul_one]
    have hqnorm : 0 ≤ expectation (q*q) := by
      by_cases hq : q=0
      · simp [hq]
      · exact (ih q.natDegree (by simpa [hn] using natDegree_lt_natDegree hq hqdeg)
          q hq rfl).le
    have hcross : expectation (H n * q) = 0 := by
      by_cases hq : q=0
      · simp [hq]
      · exact hermite_orthogonal_lower n q
          (by simpa [hn] using natDegree_lt_natDegree hq hqdeg)
    have he : p*p = C (a*a) * (H n * H n) + C (2*a) * (H n*q) + q*q := by
      dsimp [q]
      simp only [map_mul, map_ofNat]
      ring
    rw [he, map_add, map_add, expectation_C_mul, expectation_C_mul,
      hermite_norm, hcross, mul_zero, add_zero]
    have hf : (0:ℝ) < n.factorial := by positivity
    have haa : 0 < a*a := mul_self_pos.mpr ha
    exact add_pos_of_pos_of_nonneg (mul_pos haa hf) hqnorm

def gram (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j => moment (i.val+j.val)
def vectorPolynomial {n : ℕ} (v : Fin n → ℝ) : ℝ[X] :=
  ∑ i, Polynomial.monomial i.val (v i)

@[simp] theorem vectorPolynomial_coeff {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    (vectorPolynomial v).coeff i.val = v i := by
  classical
  rw [vectorPolynomial, finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Polynomial.coeff_monomial, Fin.val_ne_of_ne hji]
  · simp

theorem vectorPolynomial_ne_zero {n : ℕ} {v : Fin n → ℝ} (hv : v ≠ 0) :
    vectorPolynomial v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hc := congrArg (fun p : ℝ[X] => p.coeff i.val) h
  simpa using hc

theorem gram_quadratic {n : ℕ} (v : Fin n → ℝ) :
    star v ⬝ᵥ (gram n *ᵥ v) = expectation (vectorPolynomial v * vectorPolynomial v) := by
  classical
  simp only [vectorPolynomial, Finset.sum_mul, Finset.mul_sum, map_sum,
    Polynomial.monomial_mul_monomial, expectation_monomial,
    dotProduct, Matrix.mulVec, gram, Pi.star_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.add_comm j.val i.val]
  ring

/-- Every finite Gaussian moment matrix is positive definite. -/
theorem gram_posDef (n : ℕ) : (gram n).PosDef := by
  classical
  constructor
  · ext i j
    simp [gram, Matrix.conjTranspose_apply, Nat.add_comm]
  · intro v hv
    rw [gram_quadratic]
    exact square_positive _ (vectorPolynomial_ne_zero hv)

/-- In particular, no Gaussian Gram determinant can vanish, at any order. -/
theorem gram_det_pos (n : ℕ) : 0 < (gram n).det := (gram_posDef n).det_pos

theorem gram_det_ne_zero (n : ℕ) : (gram n).det ≠ 0 := ne_of_gt (gram_det_pos n)

#print axioms square_positive
#print axioms gram_posDef
#print axioms gram_det_ne_zero
end V033.Gaussian
