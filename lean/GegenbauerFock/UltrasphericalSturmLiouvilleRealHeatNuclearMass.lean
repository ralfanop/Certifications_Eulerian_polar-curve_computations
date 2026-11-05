import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatPositiveNuclear

/-!
# V007 — exact positive nuclear mass of the genuine Gegenbauer heat operator

Once the operator-norm convergent positive rank-one expansion of the true
heat operator is established, its explicit nuclear witness has total
operator-norm mass equal to the actual Gegenbauer-basis diagonal trace:

  sum_n ||exp(-s omega_n) rankOne(e_n,e_n)||
    = sum_n <e_n,H_s e_n>
    = sum_n exp(-s omega_n).

This is an exact positive REAL-Hilbert nuclear witness identity; it does
not assert an unformalized basis-independent universal real trace ideal.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory InnerProductSpace

/-- The exact total operator-norm mass of the positive rank-one
expansion equals the trace computed on the ACTUAL weighted-real-L²
complete Gegenbauer Hilbert basis. -/
theorem sturmRealHeat_positive_nuclear_mass_eq_actual_basis_trace
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    (∑' n : ℕ,
      ‖Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) •
        rankOne ℝ
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖) =
    (∑' n : ℕ,
      inner ℝ
        ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n)
        (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)
          ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n))) := by
  calc
    (∑' n : ℕ,
      ‖Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) •
        rankOne ℝ
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖) =
      ∑' n : ℕ, Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) := by
        apply tsum_congr
        intro n
        rw [norm_smul, norm_rankOne,
          sturmMonicEigenCandidate_realL2_normalized_norm lam hlam n]
        simp only [one_mul, mul_one, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
    _ = _ :=
      (sturmRealHeat_actual_basis_trace_eq_spectral_series lam s hlam hs).symm

/-- The squared operator-norm masses equal the squared heat spectral
multiplier series (which is summable for every positive time). -/
theorem sturmRealHeat_positive_nuclear_square_mass_eq_spectral_sq
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    (∑' n : ℕ,
      ‖Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) •
        rankOne ℝ
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n)‖ ^ 2) =
    (∑' n : ℕ,
      Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) ^ 2) := by
  apply tsum_congr
  intro n
  rw [norm_smul, norm_rankOne,
    sturmMonicEigenCandidate_realL2_normalized_norm lam hlam n]
  simp only [one_mul, mul_one, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_positive_nuclear_mass_eq_actual_basis_trace
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_positive_nuclear_square_mass_eq_spectral_sq

end GegenbauerFock.Ultraspherical
