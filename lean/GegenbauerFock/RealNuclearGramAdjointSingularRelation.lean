import GegenbauerFock.RealNuclearGramCompactPositiveKernel

/-!
# V007 — genuine adjoint singular-pair relation from nonzero Gram modes

Given ANY bounded real Hilbert operator T and positive amplitudes
sigma_n with (T†T)b_n = sigma_n² b_n, each normalized output vector
c_n = sigma_n⁻¹ T b_n satisfies both singular-pair identities:
  T b_n = sigma_n c_n
  T† c_n = sigma_n b_n.

No positivity or self-adjointness assumption on T, and no global
unitary extension, common span, or equality of defects is needed.

The orthonormality of the c_n family is separately checked in
RealNuclearGramNonzeroSingularTransfer. This module proves the
two-sided singular equations without depending on that proof.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The adjoint maps a normalized nonzero output singular vector back
to its source with exactly the same positive singular amplitude. -/
theorem realNuclearGram_adjoint_normalized_output_eigen
    (T : H →L[ℝ] H) (b : ℕ → H)
    (sigma : ℕ → ℝ) (hpos : ∀ n, 0 < sigma n)
    (heig : ∀ n, realNuclearGram T (b n) =
      (sigma n)^2 • b n) (n : ℕ) :
    T.adjoint ((sigma n)⁻¹ • T (b n)) =
      sigma n • b n := by
  calc
    T.adjoint ((sigma n)⁻¹ • T (b n)) =
        (sigma n)⁻¹ • realNuclearGram T (b n) := by
      rw [map_smul] <;> rfl
    _ = (sigma n)⁻¹ • ((sigma n)^2 • b n) := by
      rw [heig n]
    _ = sigma n • b n := by
      rw [smul_smul]
      have hscalar : (sigma n)⁻¹ * (sigma n)^2 = sigma n := by
        have hn : sigma n ≠ 0 := ne_of_gt (hpos n)
        field_simp <;> ring
      rw [hscalar]

/-- Both actual operator and adjoint singular-pair equations hold on
each nonzero Gram mode, even for an operator with unequal defect
dimensions. -/
theorem realNuclearGram_singular_pair_equations
    (T : H →L[ℝ] H) (b : ℕ → H)
    (sigma : ℕ → ℝ) (hpos : ∀ n, 0 < sigma n)
    (heig : ∀ n, realNuclearGram T (b n) =
      (sigma n)^2 • b n) (n : ℕ) :
    T (b n) = sigma n • ((sigma n)⁻¹ • T (b n)) ∧
    T.adjoint ((sigma n)⁻¹ • T (b n)) =
      sigma n • b n := by
  constructor
  · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (hpos n)), one_smul]
  · exact realNuclearGram_adjoint_normalized_output_eigen
      T b sigma hpos heig n

#print axioms GegenbauerFock.Ultraspherical.realNuclearGram_adjoint_normalized_output_eigen
#print axioms GegenbauerFock.Ultraspherical.realNuclearGram_singular_pair_equations

end GegenbauerFock.Ultraspherical
