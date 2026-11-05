import GegenbauerFock.GaussianAreaComplexMonomialGram

/-!
# V007 — Gaussian-area normalization of the complex monomial system

These are the exact factorial/Gaussian scalar normalization identities
needed to construct a true orthonormal family inside the holomorphic
Gaussian L² space.  The integral is the genuine planar complex Bochner
integral, not an abstract postulated Gram matrix.

No assertion about polynomial density or onto Bargmann–Fock isometry
is made in this intermediate module.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The positive real normalization coefficient of zⁿ. -/
noncomputable def monomialWeight (alpha : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ)

/-- The normalized entire Gaussian monomial. -/
noncomputable def normalizedMonomial (alpha : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  monomialWeight alpha n * z ^ n

/-- The factorial and inverse Gaussian weights cancel exactly. -/
theorem monomial_normalization_scalar
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    (alpha ^ n / (Nat.factorial n : ℝ)) *
      ((Nat.factorial n : ℝ) * alpha ^ (-(n : ℝ))) = 1 := by
  have hn : alpha ^ n ≠ 0 := pow_ne_zero _ (ne_of_gt ha)
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  rw [Real.rpow_neg (le_of_lt ha), Real.rpow_natCast]
  field_simp [hn, hf]

/-- Real scalar normalization of each Gaussian diagonal Gram entry. -/
theorem monomial_normalization_real
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ))) ^ 2 *
      ((Nat.factorial n : ℝ) * alpha ^ (-(n : ℝ))) = 1 := by
  rw [Real.sq_sqrt (by positivity)]
  exact monomial_normalization_scalar alpha ha n

/-- The entire normalized monomial Gram matrix is the Kronecker delta. -/
theorem integral_normalized_monomial_gram_delta
    (alpha : ℝ) (ha : 0 < alpha) (m n : ℕ) :
    (monomialWeight alpha m * monomialWeight alpha n) *
      (∫ z : ℂ,
        ((alpha / Real.pi : ℝ) : ℂ) *
          (z ^ m * star (z ^ n) *
            (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ))) =
      if m = n then (1 : ℂ) else 0 := by
  rw [integral_normalized_complex_monomial_gram alpha ha m n]
  by_cases h : m = n
  · subst n
    simp only [ite_true]
    have hr := monomial_normalization_real alpha ha m
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
    simpa [monomialWeight, pow_two] using hc
  · simp [h]

/-- The normalization coefficient is fixed by complex conjugation. -/
theorem star_monomialWeight (alpha : ℝ) (n : ℕ) :
    star (monomialWeight alpha n) = monomialWeight alpha n := by
  simp [monomialWeight, Complex.star_def]

/-- The actual normalized entire monomials are orthonormal for
the normalized two-dimensional Gaussian-area integral. -/
theorem integral_normalized_monomial_pair_delta
    (alpha : ℝ) (ha : 0 < alpha) (m n : ℕ) :
    (∫ z : ℂ,
      ((alpha / Real.pi : ℝ) : ℂ) *
        (normalizedMonomial alpha m z *
          star (normalizedMonomial alpha n z) *
          (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ))) =
      if m = n then (1 : ℂ) else 0 := by
  calc
    (∫ z : ℂ,
      ((alpha / Real.pi : ℝ) : ℂ) *
        (normalizedMonomial alpha m z *
          star (normalizedMonomial alpha n z) *
          (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ))) =
      (∫ z : ℂ,
        (monomialWeight alpha m * monomialWeight alpha n) *
          (((alpha / Real.pi : ℝ) : ℂ) *
            (z ^ m * star (z ^ n) *
              (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ)))) := by
        congr 1
        funext z
        simp only [normalizedMonomial, star_mul]
        rw [star_monomialWeight]
        ring
    _ = (monomialWeight alpha m * monomialWeight alpha n) *
      (∫ z : ℂ,
        ((alpha / Real.pi : ℝ) : ℂ) *
          (z ^ m * star (z ^ n) *
            (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ))) := by
        rw [integral_const_mul]
    _ = if m = n then (1 : ℂ) else 0 :=
      integral_normalized_monomial_gram_delta alpha ha m n

#print axioms GegenbauerFock.GaussianArea.monomial_normalization_scalar
#print axioms GegenbauerFock.GaussianArea.monomial_normalization_real
#print axioms GegenbauerFock.GaussianArea.integral_normalized_monomial_gram_delta
#print axioms GegenbauerFock.GaussianArea.star_monomialWeight
#print axioms GegenbauerFock.GaussianArea.integral_normalized_monomial_pair_delta

end GegenbauerFock.GaussianArea
