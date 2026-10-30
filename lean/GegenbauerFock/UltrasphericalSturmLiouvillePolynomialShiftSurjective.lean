import GegenbauerFock.UltrasphericalSturmLiouvillePolynomialExpansion
import GegenbauerFock.UltrasphericalSturmLiouvilleEigenvalueOrder

/-!
# V007 — exact polynomial shifted Sturm resolvent at +1

For all real ultraspherical parameters λ>0, prove the algebraic
surjectivity of I-L_λ on all real polynomials, using the true exact
degree-two triangular recurrence. In particular EVERY polynomial
target has a genuine polynomial preimage, with no approximation.

The result is a polynomial-core step toward proving dense range of
the unbounded L² operator I-L_λ. The further operator-theoretic
essential-self-adjointness criterion is NOT asserted here.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open Polynomial

/-- The genuine polynomial shifted differential expression I-L_λ. -/
def sturmShiftPolynomial (lam : ℝ) (p : ℝ[X]) : ℝ[X] :=
  p - sturmPolynomial lam p

theorem sturmShiftPolynomial_add (lam : ℝ) (p q : ℝ[X]) :
    sturmShiftPolynomial lam (p + q) =
      sturmShiftPolynomial lam p + sturmShiftPolynomial lam q := by
  simp only [sturmShiftPolynomial, sturmPolynomial_add]
  abel

theorem sturmShiftPolynomial_smul (lam c : ℝ) (p : ℝ[X]) :
    sturmShiftPolynomial lam (c • p) =
      c • sturmShiftPolynomial lam p := by
  simp only [sturmShiftPolynomial, sturmPolynomial_smul, smul_sub]

/-- The shifted Sturm operator is a genuine real-linear polynomial
endomorphism. -/
def sturmShiftPolynomialLinear (lam : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := sturmShiftPolynomial lam
  map_add' := sturmShiftPolynomial_add lam
  map_smul' := sturmShiftPolynomial_smul lam

@[simp] theorem sturmShiftPolynomialLinear_apply
    (lam : ℝ) (p : ℝ[X]) :
    sturmShiftPolynomialLinear lam p = sturmShiftPolynomial lam p := rfl

@[simp] theorem sturmShiftPolynomial_one (lam : ℝ) :
    sturmShiftPolynomial lam 1 = 1 := by
  simp [sturmShiftPolynomial, sturmPolynomial_C]

theorem sturmShiftPolynomial_X (lam : ℝ) :
    sturmShiftPolynomial lam X = C (2 * lam + 2) * X := by
  simp only [sturmShiftPolynomial, sturmPolynomial_X, sub_neg_eq_add]
  rw [show C (2 * lam + 2) = 1 + C (2 * lam + 1) by
    rw [← map_one, ← map_add]
    congr 1
    ring]
  ring

/-- Exact upper diagonal coefficient 1+(n+2)(n+2+2λ) of I-L. -/
theorem sturmShiftPolynomial_X_pow_succ_succ (lam : ℝ) (n : ℕ) :
    sturmShiftPolynomial lam (X ^ (n + 2)) =
      C (1 + (((n + 2 : ℕ) : ℝ) *
        (((n + 2 : ℕ) : ℝ) + 2 * lam))) * X ^ (n + 2) -
      C ((((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))) * X ^ n := by
  unfold sturmShiftPolynomial
  rw [sturmPolynomial_X_pow_succ_succ]
  simp only [map_add, map_one]
  ring

/-- Every monomial has an EXACT polynomial preimage under I-L_λ,
obtained by two-step induction; this is not a formal power series. -/
theorem sturmShiftPolynomial_monomial_preimage
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    ∃ q : ℝ[X], sturmShiftPolynomial lam q = X ^ n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      refine ⟨1, ?_⟩
      simp
  | one =>
      have ha : 2 * lam + 2 ≠ 0 := ne_of_gt (by positivity)
      refine ⟨(2 * lam + 2)⁻¹ • X, ?_⟩
      rw [sturmShiftPolynomial_smul, sturmShiftPolynomial_X]
      simp only [pow_one, smul_eq_C_mul]
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  | more n hn _ =>
      let a : ℝ := 1 + (((n + 2 : ℕ) : ℝ) *
        (((n + 2 : ℕ) : ℝ) + 2 * lam))
      let b : ℝ := (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))
      have ha : a ≠ 0 := ne_of_gt (by
        dsimp [a]
        positivity)
      obtain ⟨q, hq⟩ := hn
      refine ⟨a⁻¹ • (X ^ (n + 2) + b • q), ?_⟩
      rw [sturmShiftPolynomial_smul, sturmShiftPolynomial_add,
        sturmShiftPolynomial_smul, hq,
        sturmShiftPolynomial_X_pow_succ_succ]
      change a⁻¹ • ((C a * X ^ (n + 2) - C b * X ^ n) +
        b • X ^ n) = X ^ (n + 2)
      have hcancel :
          (C a * X ^ (n + 2) - C b * X ^ n) + b • X ^ n =
            a • X ^ (n + 2) := by
        simp only [smul_eq_C_mul]
        ring
      rw [hcancel, smul_smul, inv_mul_cancel₀ ha, one_smul]

/-- A complete exact algebraic inverse preimage exists for EVERY
real polynomial, not merely bounded degrees or low-degree cases. -/
theorem sturmShiftPolynomial_surjective
    (lam : ℝ) (hlam : 0 < lam) :
    Function.Surjective (sturmShiftPolynomial lam) := by
  classical
  intro p
  let q (n : ℕ) : ℝ[X] :=
    Classical.choose (sturmShiftPolynomial_monomial_preimage lam hlam n)
  have hq (n : ℕ) : sturmShiftPolynomial lam (q n) = X ^ n :=
    Classical.choose_spec (sturmShiftPolynomial_monomial_preimage lam hlam n)
  refine ⟨∑ n ∈ p.support, p.coeff n • q n, ?_⟩
  change sturmShiftPolynomialLinear lam
      (∑ n ∈ p.support, p.coeff n • q n) = p
  calc
    sturmShiftPolynomialLinear lam
        (∑ n ∈ p.support, p.coeff n • q n) =
      ∑ n ∈ p.support,
        p.coeff n • sturmShiftPolynomialLinear lam (q n) := by
          simp only [map_sum, map_smul]
    _ = ∑ n ∈ p.support, p.coeff n • (X ^ n : ℝ[X]) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [sturmShiftPolynomialLinear_apply, hq]
    _ = p := sturmPolynomial_true_monomial_expansion p

#print axioms GegenbauerFock.Ultraspherical.sturmShiftPolynomialLinear_apply
#print axioms GegenbauerFock.Ultraspherical.sturmShiftPolynomial_X
#print axioms GegenbauerFock.Ultraspherical.sturmShiftPolynomial_X_pow_succ_succ
#print axioms GegenbauerFock.Ultraspherical.sturmShiftPolynomial_monomial_preimage
#print axioms GegenbauerFock.Ultraspherical.sturmShiftPolynomial_surjective

end GegenbauerFock.Ultraspherical
