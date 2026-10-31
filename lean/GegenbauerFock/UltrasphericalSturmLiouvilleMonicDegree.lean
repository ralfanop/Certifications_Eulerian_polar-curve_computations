import GegenbauerFock.UltrasphericalSturmLiouvilleMonicEigenPolynomial

/-!
# V007 — exact top coefficient, degree and monicity for ALL Gegenbauer modes

The finite Gegenbauer polynomial G_{n,λ} has coefficient exactly 1
at X^n, and zero coefficients in all degrees >n. Therefore its
degree is exactly n and it is nonzero and monic, independently of
any Hilbert-space or spectral theorem.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open Polynomial

/-- The leading X^n coefficient of the explicit finite monic
Gegenbauer candidate is exactly one. -/
theorem sturmMonicEigenCandidate_coeff_top
    (lam : ℝ) (n : ℕ) :
    (sturmMonicEigenCandidate lam n).coeff n = 1 := by
  unfold sturmMonicEigenCandidate
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single_of_mem 0 (by simp)]
  · simp [sturmMonicCoeff_zero]
  · intro k hk hk0
    have hbound : k < n/2+1 := Finset.mem_range.mp hk
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hne : n ≠ n - 2*k := by omega
    simp [hne]

/-- Every coefficient strictly above the defining degree n
vanishes in the explicit finite sum. -/
theorem sturmMonicEigenCandidate_coeff_above
    (lam : ℝ) (n m : ℕ) (hm : n < m) :
    (sturmMonicEigenCandidate lam n).coeff m = 0 := by
  unfold sturmMonicEigenCandidate
  simp only [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro k hk
  have hne : m ≠ n - 2*k := by omega
  simp [hne]

/-- The explicit polynomial has EXACTLY degree n, not merely
at most n. The proof needs no claim of L²-nonvanishing. -/
theorem sturmMonicEigenCandidate_natDegree
    (lam : ℝ) (n : ℕ) :
    (sturmMonicEigenCandidate lam n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    exact sturmMonicEigenCandidate_coeff_above lam n m hm
  · rw [sturmMonicEigenCandidate_coeff_top]
    norm_num

/-- The entire constructed family consists of genuine monic
polynomials, of strictly increasing natural degrees. -/
theorem sturmMonicEigenCandidate_monic
    (lam : ℝ) (n : ℕ) :
    (sturmMonicEigenCandidate lam n).Monic := by
  change (sturmMonicEigenCandidate lam n).leadingCoeff = 1
  rw [leadingCoeff, sturmMonicEigenCandidate_natDegree]
  exact sturmMonicEigenCandidate_coeff_top lam n

#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_coeff_top
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_coeff_above
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_natDegree
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_monic

end GegenbauerFock.Ultraspherical
