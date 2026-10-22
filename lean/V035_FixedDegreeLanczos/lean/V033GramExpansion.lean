import V033MomentFunctional
import V033PolynomialJets
import Mathlib.LinearAlgebra.Matrix.Block

noncomputable section
namespace V033.UniformSum
open Polynomial Matrix Finset

def hermiteGram (n : ℕ) : Matrix (Fin n) (Fin n) ℝ[X] :=
  fun i j => momentMap (Gaussian.H i.val * Gaussian.H j.val)
def determinantPolynomial (n : ℕ) : ℝ[X] := (hermiteGram n).det
def gaussianDeterminant (n : ℕ) : ℝ := ∏ i : Fin n, (i.val.factorial : ℝ)
def normalizedGram (n : ℕ) : Matrix (Fin n) (Fin n) ℝ[X] :=
  fun i j => C ((i.val.factorial:ℝ)⁻¹) * hermiteGram n i j

theorem normalizedGram_constant (n : ℕ) (i j : Fin n) :
    (normalizedGram n i j).coeff 0 = (1:Matrix (Fin n) (Fin n) ℝ) i j := by
  rw [normalizedGram, coeff_C_mul, hermiteGram, momentMap_constant]
  by_cases hij : i=j
  · subst j
    rw [Gaussian.hermite_norm]
    simp [Matrix.one_apply, show (i.val.factorial:ℝ) ≠ 0 by positivity]
  · rw [Gaussian.hermite_orthogonal _ _ (Fin.val_ne_of_ne hij)]
    simp [Matrix.one_apply, hij]

theorem normalizedGram_linear_diagonal (n : ℕ) (i : Fin n) :
    (normalizedGram n i i).coeff 1 = -(3/10:ℝ)*(i.val:ℝ)*(i.val-1:ℝ) := by
  rw [normalizedGram, coeff_C_mul, hermiteGram, momentMap_linear,
    Gaussian.fourth_hermite_mixed_norm]
  have hf : (i.val.factorial:ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

theorem hermiteGram_factorization (n : ℕ) :
    hermiteGram n = diagonal (fun i : Fin n => C (i.val.factorial:ℝ)) * normalizedGram n := by
  ext i j
  rw [diagonal_mul]
  dsimp [normalizedGram]
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (by positivity : (i.val.factorial:ℝ) ≠ 0),
    map_one, one_mul]

theorem determinant_factorization (n : ℕ) :
    determinantPolynomial n = C (gaussianDeterminant n) * (normalizedGram n).det := by
  rw [determinantPolynomial, hermiteGram_factorization, det_mul, det_diagonal]
  simp only [gaussianDeterminant, map_prod]

theorem normalized_det_constant (n : ℕ) : ((normalizedGram n).det).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  have he : (normalizedGram n).map (Polynomial.evalRingHom (0:ℝ)) = 1 := by
    ext i j
    change (normalizedGram n i j).eval 0 = _
    rw [← coeff_zero_eq_eval_zero, normalizedGram_constant]
  change ((normalizedGram n).map (Polynomial.evalRingHom (0:ℝ))).det = 1
  rw [he, det_one]

theorem sum_quadratic (n : ℕ) :
    (∑ i ∈ range n, (i:ℝ)*(i-1)) = (n:ℝ)*(n-1)*(n-2)/3 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem normalized_det_linear (n : ℕ) :
    ((normalizedGram n).det).coeff 1 = -(n:ℝ)*(n-1)*(n-2)/10 := by
  rw [Jet.det_linear_of_constant_one _ (normalizedGram_constant n)]
  simp only [normalizedGram_linear_diagonal]
  rw [show (∑ i : Fin n, -(3/10:ℝ)*(i.val:ℝ)*(i.val-1:ℝ)) =
      ∑ i ∈ range n, -(3/10:ℝ)*(i:ℝ)*(i-1) from
        Fin.sum_univ_eq_sum_range (fun i : ℕ => -(3/10:ℝ)*(i:ℝ)*(i-1)) n]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [sum_quadratic]
  ring

theorem determinant_constant (n : ℕ) :
    (determinantPolynomial n).coeff 0 = gaussianDeterminant n := by
  rw [determinant_factorization, coeff_C_mul, normalized_det_constant, mul_one]

theorem determinant_linear (n : ℕ) :
    (determinantPolynomial n).coeff 1 =
      gaussianDeterminant n * (-(n:ℝ)*(n-1)*(n-2)/10) := by
  rw [determinant_factorization, coeff_C_mul, normalized_det_linear]

theorem gaussianDeterminant_pos (n : ℕ) : 0 < gaussianDeterminant n := by
  apply Finset.prod_pos
  intro i hi
  positivity

theorem gaussianDeterminant_succ (n : ℕ) :
    gaussianDeterminant (n+1) = gaussianDeterminant n * (n.factorial:ℝ) := by
  unfold gaussianDeterminant
  rw [Fin.prod_univ_castSucc]
  rfl

#print axioms determinant_constant
#print axioms determinant_linear
end V033.UniformSum
