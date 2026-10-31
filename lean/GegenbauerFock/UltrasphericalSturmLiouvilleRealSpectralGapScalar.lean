import GegenbauerFock.UltrasphericalSturmLiouvilleEigenvalueGrowth

/-!
# Exact first ultraspherical Sturm spectral gap

The complete Gegenbauer spectral realization has eigenvalues
- n(n+2λ) for n in ℕ. This module explicitly certifies that the
zero mode is separated from every positive degree by the sharp
first positive rate 1+2λ. It is the scalar ingredient for later
Poincare and mean-zero semigroup estimates.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

/-- The first strictly positive Gegenbauer spectral rate is 1+2λ. -/
theorem sturmFirstSpectralRate_pos
    (lam : ℝ) (hlam : 0 < lam) : 0 < 1 + 2 * lam := by
  linarith

/-- Every positive-degree rate is at least the sharp first gap. -/
theorem sturmPositiveDegree_spectralRate_ge_first
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (hn : 0 < n) :
    1 + 2 * lam ≤ (n : ℝ) * ((n : ℝ) + 2 * lam) := by
  have hreal : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnonneg : 0 ≤ ((n : ℝ) - 1) * ((n : ℝ) + 1 + 2 * lam) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith

/-- The closed Gegenbauer Sturm spectral values are at most
the negative first gap on every degree n≥1. -/
theorem sturmPositiveDegree_eigenvalue_le_neg_first
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (hn : 0 < n) :
    sturmEigenvalue lam n ≤ -(1 + 2 * lam) := by
  have hgap := sturmPositiveDegree_spectralRate_ge_first
    lam hlam n hn
  unfold sturmEigenvalue
  linarith

#print axioms GegenbauerFock.Ultraspherical.sturmFirstSpectralRate_pos
#print axioms GegenbauerFock.Ultraspherical.sturmPositiveDegree_spectralRate_ge_first
#print axioms GegenbauerFock.Ultraspherical.sturmPositiveDegree_eigenvalue_le_neg_first

end GegenbauerFock.Ultraspherical
