import GegenbauerFock.CanonicalCFCGramTikhonovShift

/-!
# V007 — exact bounded-operator Tikhonov error identity

For the genuine positive compact source Gram G, positive shift
A_eps = G + eps I and filter T_eps = G A_eps^{-1}, certify in B(H)

          I - T_eps = eps A_eps^{-1}.

This is an equality of bounded complex-linear operators on the actual
weighted L²; it is stronger than an eigenvector calculation and is
the starting point for the quantitative strong convergence proof.
-/

noncomputable section
open MeasureTheory
namespace GegenbauerFock.GeneralUltrasphericalFock

private abbrev ErrorH (lam : ℝ) :=
  Lp ℂ 2 (Ultraspherical.measure lam)

/-- Exact resolvent regularization error on all actual weighted L²,
with no restriction to the polynomial or finite-spectral core. -/
theorem sourceGramTikhonov_filter_error_identity
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps) :
    (1 : ErrorH lam →L[ℂ] ErrorH lam) -
      sourceGramTikhonovFilter lam alpha hlam ha eps =
        (eps : ℂ) •
          (sourceGramPositiveShift lam alpha hlam ha eps)⁻¹ʳ := by
  let G := gram lam alpha hlam ha
  let A := sourceGramPositiveShift lam alpha hlam ha eps
  have hright :
      G * A⁻¹ʳ + (eps : ℂ) • A⁻¹ʳ =
        (1 : ErrorH lam →L[ℂ] ErrorH lam) := by
    have h := (sourceGramPositiveShift_two_sided_inverse
      lam alpha hlam ha eps heps).1
    change A * A⁻¹ʳ = 1 at h
    have hA : A = G + (eps : ℂ) •
        (1 : ErrorH lam →L[ℂ] ErrorH lam) := rfl
    rw [hA, add_mul, smul_mul_assoc, one_mul] at h
    exact h
  change (1 : ErrorH lam →L[ℂ] ErrorH lam) -
    G * A⁻¹ʳ = (eps : ℂ) • A⁻¹ʳ
  exact sub_eq_iff_eq_add.mpr (by
    calc
      (1 : ErrorH lam →L[ℂ] ErrorH lam) =
          G * A⁻¹ʳ + (eps : ℂ) • A⁻¹ʳ := hright.symm
      _ = (eps : ℂ) • A⁻¹ʳ + G * A⁻¹ʳ := add_comm _ _)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonov_filter_error_identity
end GegenbauerFock.GeneralUltrasphericalFock
