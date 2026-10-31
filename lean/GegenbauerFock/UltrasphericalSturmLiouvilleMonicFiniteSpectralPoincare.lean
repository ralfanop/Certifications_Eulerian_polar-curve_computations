import GegenbauerFock.UltrasphericalSturmLiouvilleMonicClosedSpectralGap

/-!
# Sharp finite Gegenbauer Fourier spectral Poincaré inequality

The normalized Hilbert basis and the exact closed Sturm diagonal
have already been established. Here we certify the elementary but
critical finite-energy estimate for all finite families of actual
Fourier coefficients with zero constant mode:

  (1 + 2λ) * Σ_{n ∈ s} a_n²
       ≤ Σ_{n ∈ s} n(n+2λ) a_n².

It holds for every finite index set, not just initial segments,
and its constant is attained exactly by pure degree-one data.
This is the algebraic Fourier-core estimate needed for the full
weighted-real-L² Poincaré inequality via Hilbert limits.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

/-- Finite spectral Poincaré estimate at the *sharp* Gegenbauer gap
on the zero-constant-mode Fourier core. -/
theorem sturmMonic_finite_spectral_poincare
    (lam : ℝ) (hlam : 0 < lam) (s : Finset ℕ)
    (a : ℕ → ℝ) (ha0 : a 0 = 0) :
    (1 + 2 * lam) * (∑ n ∈ s, (a n) ^ 2) ≤
      ∑ n ∈ s,
        ((n : ℝ) * ((n : ℝ) + 2 * lam)) * (a n) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp [ha0]
  · have hgap := sturmEigenvalue_positive_degree_gap lam hlam n hn0
    have hweight :
        1 + 2 * lam ≤ (n : ℝ) * ((n : ℝ) + 2 * lam) := by
      unfold sturmEigenvalue at hgap
      linarith
    exact mul_le_mul_of_nonneg_right hweight (sq_nonneg (a n))

/-- The finite Poincaré coefficient is attained by pure degree one.
Hence the factor 1+2λ cannot be replaced by any larger constant. -/
theorem sturmMonic_finite_spectral_poincare_degree_one_equality
    (lam : ℝ) :
    (1 + 2 * lam) *
      (∑ n ∈ ({1} : Finset ℕ),
        (if n = 1 then (1 : ℝ) else 0) ^ 2) =
      ∑ n ∈ ({1} : Finset ℕ),
        ((n : ℝ) * ((n : ℝ) + 2 * lam)) *
          (if n = 1 then (1 : ℝ) else 0) ^ 2 := by
  simp
  ring

/-- No coefficient strictly larger than the first positive Sturm
eigenvalue can satisfy the finite inequality on every mean-zero
Fourier coefficient family. -/
theorem sturmMonic_finite_spectral_poincare_constant_optimal
    (lam C : ℝ)
    (hbound : ∀ (s : Finset ℕ) (a : ℕ → ℝ), a 0 = 0 →
      C * (∑ n ∈ s, (a n) ^ 2) ≤
        ∑ n ∈ s,
          ((n : ℝ) * ((n : ℝ) + 2 * lam)) * (a n) ^ 2) :
    C ≤ 1 + 2 * lam := by
  have ha : (fun n : ℕ => if n = 1 then (1 : ℝ) else 0) 0 = 0 := by
    simp
  have h := hbound {1} (fun n : ℕ => if n = 1 then (1 : ℝ) else 0) ha
  simpa using h

#print axioms GegenbauerFock.Ultraspherical.sturmMonic_finite_spectral_poincare
#print axioms GegenbauerFock.Ultraspherical.sturmMonic_finite_spectral_poincare_degree_one_equality
#print axioms GegenbauerFock.Ultraspherical.sturmMonic_finite_spectral_poincare_constant_optimal

end GegenbauerFock.Ultraspherical
