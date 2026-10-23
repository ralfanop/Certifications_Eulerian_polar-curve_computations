import V033MomentFunctional
import Mathlib.LinearAlgebra.Matrix.Block

noncomputable section
namespace V033.Gram
open Polynomial Matrix Finset
variable {R : Type*} [CommRing R] [Algebra ℝ R]

def hankel (L : ℝ[X] →ₗ[ℝ] R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => L (X^(i.val+j.val))
def family (L : ℝ[X] →ₗ[ℝ] R) {n : ℕ} (p : Fin n → ℝ[X]) : Matrix (Fin n) (Fin n) R :=
  fun i j => L (p i*p j)
def coefficients {n : ℕ} (p : Fin n → ℝ[X]) : Matrix (Fin n) (Fin n) R :=
  fun i j => algebraMap ℝ R ((p j).coeff i.val)

theorem polynomial_sum {n : ℕ} (p : ℝ[X]) (hp : p.natDegree < n) :
    p = ∑ i : Fin n, C (p.coeff i.val)*X^i.val := by
  rw [Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i)*X^i) n]
  exact p.as_sum_range_C_mul_X_pow' hp

theorem pairing_expansion (L : ℝ[X] →ₗ[ℝ] R) {n : ℕ} (p q : ℝ[X])
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    L (p*q) = ∑ i : Fin n, ∑ j : Fin n,
      algebraMap ℝ R (p.coeff i.val) * L (X^(i.val+j.val)) * algebraMap ℝ R (q.coeff j.val) := by
  conv_lhs => rw [polynomial_sum p hp, polynomial_sum q hq]
  simp only [sum_mul, mul_sum, map_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [show C (p.coeff i.val)*X^i.val*(C (q.coeff j.val)*X^j.val) =
      C (p.coeff i.val*q.coeff j.val)*X^(i.val+j.val) by rw [map_mul, pow_add]; ring,
    ← smul_eq_C_mul, map_smul]
  simp only [Algebra.smul_def, map_mul]
  ring

theorem change_basis (L : ℝ[X] →ₗ[ℝ] R) {n : ℕ} (p : Fin n → ℝ[X])
    (hp : ∀ i, (p i).natDegree < n) :
    family L p = (coefficients p)ᵀ * hankel L n * coefficients p := by
  ext i j
  rw [family, pairing_expansion L _ _ (hp i) (hp j)]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, coefficients, hankel, sum_mul]
  rw [Finset.sum_comm]

theorem coefficients_det_one {n : ℕ} (p : Fin n → ℝ[X])
    (hd : ∀ i, (p i).natDegree = i.val) (hm : ∀ i, (p i).Monic) :
    (coefficients (R:=R) p).det = 1 := by
  have ht := Matrix.det_matrixOfPolynomials p hd hm
  have h := congrArg (algebraMap ℝ R) ht
  rw [RingHom.map_det, map_one] at h
  exact h

theorem monic_gram_det (L : ℝ[X] →ₗ[ℝ] R) {n : ℕ} (p : Fin n → ℝ[X])
    (hd : ∀ i, (p i).natDegree = i.val) (hm : ∀ i, (p i).Monic) :
    (family L p).det = (hankel L n).det := by
  rw [change_basis L p (fun i => by rw [hd]; exact i.isLt), det_mul, det_mul,
    det_transpose, coefficients_det_one p hd hm, one_mul, mul_one]

theorem orthogonal_gram_det (L : ℝ[X] →ₗ[ℝ] R) {n : ℕ} (p : Fin n → ℝ[X])
    (hd : ∀ i, (p i).natDegree = i.val) (hm : ∀ i, (p i).Monic)
    (ho : ∀ i j, i ≠ j → L (p i*p j) = 0) :
    (hankel L n).det = ∏ i : Fin n, L (p i*p i) := by
  rw [← monic_gram_det L p hd hm]
  have he : family L p = diagonal (fun i => L (p i*p i)) := by
    ext i j
    by_cases hij : i=j
    · subst j; simp [family]
    · simp [family, diagonal_apply, hij, ho i j hij]
  rw [he, det_diagonal]

#print axioms monic_gram_det
#print axioms orthogonal_gram_det
end V033.Gram
