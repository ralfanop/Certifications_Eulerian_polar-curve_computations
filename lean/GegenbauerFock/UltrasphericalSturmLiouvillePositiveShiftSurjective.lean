import GegenbauerFock.UltrasphericalSturmLiouvillePolynomialShiftSurjective

/-!
# V007 — all positive real spectral shifts: exact polynomial surjectivity

The true Gegenbauer polynomial differential expression
Lλ p = (1-X²)p'' -(2λ+1)Xp' is triangular on every monomial.

For every t>0 and λ>0, the polynomial operator tI-Lλ is
surjective on ALL real polynomials. Unlike a formal series inverse,
each preimage is a finite real polynomial constructed by an exact
two-step induction. This extends the already certified t=1 case.

The corresponding actual weighted-L² operator has dense shifted
range, but no full resolvent operator or self-adjointness is claimed
here without the separate unbounded-domain bridge.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical
open Polynomial

/-- The exact real polynomial shifted Gegenbauer operator tI-L. -/
def sturmPositiveShiftPolynomial (lam t : ℝ) (p : ℝ[X]) : ℝ[X] :=
  C t * p - sturmPolynomial lam p

theorem sturmPositiveShiftPolynomial_add (lam t : ℝ) (p q : ℝ[X]) :
    sturmPositiveShiftPolynomial lam t (p+q) =
      sturmPositiveShiftPolynomial lam t p +
        sturmPositiveShiftPolynomial lam t q := by
  simp only [sturmPositiveShiftPolynomial, sturmPolynomial_add]
  ring

theorem sturmPositiveShiftPolynomial_smul (lam t c : ℝ) (p : ℝ[X]) :
    sturmPositiveShiftPolynomial lam t (c • p) =
      c • sturmPositiveShiftPolynomial lam t p := by
  simp only [sturmPositiveShiftPolynomial, sturmPolynomial_smul, smul_sub,
    smul_eq_C_mul]
  ring

def sturmPositiveShiftPolynomialLinear (lam t : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := sturmPositiveShiftPolynomial lam t
  map_add' := sturmPositiveShiftPolynomial_add lam t
  map_smul' := sturmPositiveShiftPolynomial_smul lam t

@[simp] theorem sturmPositiveShiftPolynomialLinear_apply
    (lam t : ℝ) (p : ℝ[X]) :
    sturmPositiveShiftPolynomialLinear lam t p =
      sturmPositiveShiftPolynomial lam t p := rfl

@[simp] theorem sturmPositiveShiftPolynomial_one (lam t : ℝ) :
    sturmPositiveShiftPolynomial lam t 1 = C t := by
  simp [sturmPositiveShiftPolynomial, sturmPolynomial_C]

theorem sturmPositiveShiftPolynomial_X (lam t : ℝ) :
    sturmPositiveShiftPolynomial lam t X =
      C (t + 2 * lam + 1) * X := by
  rw [sturmPositiveShiftPolynomial, sturmPolynomial_X]
  simp only [sub_neg_eq_add]
  rw [← add_mul, ← map_add]
  ring

theorem sturmPositiveShiftPolynomial_X_pow_succ_succ
    (lam t : ℝ) (n : ℕ) :
    sturmPositiveShiftPolynomial lam t (X ^ (n + 2)) =
      C (t + (((n + 2 : ℕ) : ℝ) *
        (((n + 2 : ℕ) : ℝ) + 2 * lam))) * X ^ (n + 2) -
      C ((((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))) * X ^ n := by
  unfold sturmPositiveShiftPolynomial
  rw [sturmPolynomial_X_pow_succ_succ]
  rw [← sub_add_eq_add_sub]
  ring

/-- Each monomial has a FINITE polynomial preimage under tI-L. -/
theorem sturmPositiveShiftPolynomial_monomial_preimage
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    ∃ q : ℝ[X], sturmPositiveShiftPolynomial lam t q = X ^ n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      refine ⟨t⁻¹ • 1, ?_⟩
      rw [sturmPositiveShiftPolynomial_smul, sturmPositiveShiftPolynomial_one]
      simp only [smul_eq_C_mul, map_inv, map_one]
      rw [← map_mul, inv_mul_cancel₀ (ne_of_gt ht), map_one]
      simp
  | one =>
      have ha : t + 2 * lam + 1 ≠ 0 := ne_of_gt (by positivity)
      refine ⟨(t + 2 * lam + 1)⁻¹ • X, ?_⟩
      rw [sturmPositiveShiftPolynomial_smul, sturmPositiveShiftPolynomial_X]
      simp only [pow_one, smul_eq_C_mul]
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  | more n hn _ =>
      let a : ℝ := t + (((n + 2 : ℕ) : ℝ) *
        (((n + 2 : ℕ) : ℝ) + 2 * lam))
      let b : ℝ := (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))
      have ha : a ≠ 0 := ne_of_gt (by
        dsimp [a]
        positivity)
      obtain ⟨q, hq⟩ := hn
      refine ⟨a⁻¹ • (X ^ (n + 2) + b • q), ?_⟩
      rw [sturmPositiveShiftPolynomial_smul,
        sturmPositiveShiftPolynomial_add,
        sturmPositiveShiftPolynomial_smul,
        hq, sturmPositiveShiftPolynomial_X_pow_succ_succ]
      change a⁻¹ • ((C a * X ^ (n + 2) - C b * X ^ n) +
        b • X ^ n) = X ^ (n + 2)
      have hcancel :
          (C a * X ^ (n + 2) - C b * X ^ n) + b • X ^ n =
            a • X ^ (n + 2) := by
        simp only [smul_eq_C_mul]
        ring
      rw [hcancel, smul_smul, inv_mul_cancel₀ ha, one_smul]

/-- Every real polynomial has an exact polynomial preimage under the
positive shifted Sturm operator tI-L, uniformly in t>0 and λ>0. -/
theorem sturmPositiveShiftPolynomial_surjective
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Function.Surjective (sturmPositiveShiftPolynomial lam t) := by
  classical
  intro p
  let q (n : ℕ) : ℝ[X] :=
    Classical.choose (sturmPositiveShiftPolynomial_monomial_preimage lam t hlam ht n)
  have hq (n : ℕ) : sturmPositiveShiftPolynomial lam t (q n) = X ^ n :=
    Classical.choose_spec
      (sturmPositiveShiftPolynomial_monomial_preimage lam t hlam ht n)
  refine ⟨∑ n ∈ p.support, p.coeff n • q n, ?_⟩
  change sturmPositiveShiftPolynomialLinear lam t
      (∑ n ∈ p.support, p.coeff n • q n) = p
  calc
    sturmPositiveShiftPolynomialLinear lam t
      (∑ n ∈ p.support, p.coeff n • q n) =
      ∑ n ∈ p.support,
        p.coeff n • sturmPositiveShiftPolynomialLinear lam t (q n) := by
          simp only [map_sum, map_smul]
    _ = ∑ n ∈ p.support, p.coeff n • (X ^ n : ℝ[X]) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [sturmPositiveShiftPolynomialLinear_apply, hq]
    _ = p := sturmPolynomial_true_monomial_expansion p

#print axioms GegenbauerFock.Ultraspherical.sturmPositiveShiftPolynomial_one
#print axioms GegenbauerFock.Ultraspherical.sturmPositiveShiftPolynomial_X_pow_succ_succ
#print axioms GegenbauerFock.Ultraspherical.sturmPositiveShiftPolynomial_monomial_preimage
#print axioms GegenbauerFock.Ultraspherical.sturmPositiveShiftPolynomial_surjective

end GegenbauerFock.Ultraspherical
