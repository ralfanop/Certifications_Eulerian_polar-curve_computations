import GegenbauerFock.RealNuclearGramCompactPositiveKernel
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# V007 — nonzero real Gram eigenmodes transfer to orthonormal outputs

Let T be ANY bounded real-Hilbert operator, with possibly different
source/kernel and output/cokernel defect dimensions. Suppose an
orthonormal family b of ACTUAL Gram eigenvectors obeys
  (T†T)b_n = sigma_n^2 b_n, sigma_n > 0.
Then the normalized OUTPUT singular vectors
  c_n = sigma_n^{-1} T b_n
are orthonormal without any completeness or global-unitary
assumption. Also T b_n = sigma_n c_n.

This is the nonzero-support singular transfer needed between the
compact positive Gram spectral theorem and the already certified
two-INCOMPLETE-family exact nuclear norm theorem.

No claim yet of the full SVD or of the zero-eigenspace support basis.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Norm preservation after dividing actual nonzero real Gram
eigenmodes by their positive singular amplitudes. -/
theorem realNuclearGram_nonzero_output_orthonormal
    (T : H →L[ℝ] H)
    (b : ℕ → H) (hb : Orthonormal ℝ b)
    (sigma : ℕ → ℝ) (hpos : ∀ n, 0 < sigma n)
    (heig : ∀ n, realNuclearGram T (b n) =
      (sigma n)^2 • b n) :
    Orthonormal ℝ
      (fun n : ℕ => (sigma n)⁻¹ • T (b n)) := by
  classical
  apply (orthonormal_iff_ite).2
  intro i j
  have hpair :
      inner ℝ (T (b i)) (T (b j)) =
        (sigma j)^2 * inner ℝ (b i) (b j) := by
    calc
      inner ℝ (T (b i)) (T (b j)) =
          inner ℝ (b i) (T.adjoint (T (b j))) :=
        (T.adjoint_inner_right (b i) (T (b j))).symm
      _ = inner ℝ (b i) (realNuclearGram T (b j)) := rfl
      _ = inner ℝ (b i) ((sigma j)^2 • b j) := by
        rw [heig j]
      _ = (sigma j)^2 * inner ℝ (b i) (b j) := by
        rw [real_inner_smul_right]
  change inner ℝ ((sigma i)⁻¹ • T (b i))
      ((sigma j)⁻¹ • T (b j)) =
        if i = j then (1 : ℝ) else (0 : ℝ)
  rw [real_inner_smul_left, real_inner_smul_right, hpair]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have hbi : inner ℝ (b i) (b i) = 1 := by
      rw [real_inner_self_eq_norm_sq, hb.norm_eq_one i]
      norm_num
    rw [hbi]
    have hne : sigma i ≠ 0 := ne_of_gt (hpos i)
    field_simp
    ring
  · rw [if_neg hij, hb.inner_eq_zero hij]
    ring

/-- The original operator sends a nonzero source Gram eigenvector
to its positive singular amplitude times the normalized output. -/
theorem realNuclearGram_nonzero_source_output_relation
    (T : H →L[ℝ] H)
    (b : ℕ → H) (sigma : ℕ → ℝ)
    (hpos : ∀ n, 0 < sigma n) (n : ℕ) :
    T (b n) = sigma n • ((sigma n)⁻¹ • T (b n)) := by
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (hpos n)), one_smul]

#print axioms GegenbauerFock.Ultraspherical.realNuclearGram_nonzero_output_orthonormal
#print axioms GegenbauerFock.Ultraspherical.realNuclearGram_nonzero_source_output_relation

end GegenbauerFock.Ultraspherical
