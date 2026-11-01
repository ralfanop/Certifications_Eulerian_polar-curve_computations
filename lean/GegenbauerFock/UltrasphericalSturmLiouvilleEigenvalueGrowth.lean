import GegenbauerFock.UltrasphericalSturmLiouvilleEigenvalueOrder

/-!
# V007 — quantitative growth of actual Sturm polynomial eigenvalue scalars

For the strictly ordered ultraspherical scalar candidates
d_n(λ) = -n(n+2λ), with λ>0, the magnitude grows at least linearly:
|d_n(λ)| ≥ n for every natural degree n.

This prepares resolvent-tail estimates once a complete Gegenbauer
Hilbert eigenbasis is certified. It does not assert eigenbasis
completeness or compactness of any operator.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

theorem sturmEigenvalue_le_neg_degree
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    sturmEigenvalue lam n ≤ -(n : ℝ) := by
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    cases n with
    | zero => norm_num
    | succ k =>
        have hone : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
        have hnonneg : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
        nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hone)]
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmul : 0 ≤ (n : ℝ) * (2 * lam) :=
    mul_nonneg hnn (by positivity)
  unfold sturmEigenvalue
  nlinarith

theorem sturmEigenvalue_abs_ge_degree
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    (n : ℝ) ≤ |sturmEigenvalue lam n| := by
  rw [abs_of_nonpos (sturmEigenvalue_nonpos lam hlam n)]
  have h := sturmEigenvalue_le_neg_degree lam hlam n
  linarith

#print axioms GegenbauerFock.Ultraspherical.sturmEigenvalue_le_neg_degree
#print axioms GegenbauerFock.Ultraspherical.sturmEigenvalue_abs_ge_degree

end GegenbauerFock.Ultraspherical
