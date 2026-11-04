import GegenbauerFock.RealNuclearGramCompactPositiveKernel
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# V007 — exact zero eigenspace and orthogonal source support of the real Gram

The genuine source Gram G=T†T has zero eigenspace exactly ker(T), for
arbitrary bounded real Hilbert T. Each nonzero Gram eigenvector is
orthogonal to ker(T). These statements hold for nonnormal operators
with arbitrarily different source and output defect dimensions.

They are the support-level facts for a later genuine polar partial
isometry. In particular, they do NOT assert a unitary polar factor
or a spectral enumeration of the positive modes.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace Module End

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The zero eigenspace of the ACTUAL real Gram is precisely the
kernel of T (not the kernel of an auxiliary diagonal model). -/
theorem realNuclearGram_zero_eigenspace_eq_kernel
    (T : H →L[ℝ] H) :
    eigenspace ((realNuclearGram T : H →L[ℝ] H) : Module.End ℝ H) 0 =
      T.ker := by
  simpa only [Module.End.eigenspace_zero] using
    realNuclearGram_ker_eq T

/-- Nonzero Gram modes are orthogonal to the genuine source kernel,
even when the target cokernel has a different dimension. -/
theorem realNuclearGram_nonzero_mode_orthogonal_kernel
    (T : H →L[ℝ] H) (mu : ℝ) (hmu : mu ≠ 0)
    (x : H) (hx : realNuclearGram T x = mu • x)
    (y : H) (hy : y ∈ T.ker) :
    inner ℝ y x = 0 := by
  have hyzero : T y = 0 := by
    simpa only [LinearMap.mem_ker] using hy
  have hpair :
      inner ℝ y (realNuclearGram T x) =
        inner ℝ (T y) (T x) := by
    change inner ℝ y (T.adjoint (T x)) =
      inner ℝ (T y) (T x)
    exact T.adjoint_inner_right y (T x)
  rw [hx, real_inner_smul_right, hyzero] at hpair
  simp only [inner_zero_left] at hpair
  exact (mul_eq_zero.mp hpair).resolve_left hmu

/-- Every member of a nonzero real-Gram eigenfamily is perpendicular
to every vector in the actual kernel, independently of completeness. -/
theorem realNuclearGram_nonzero_family_orthogonal_kernel
    (T : H →L[ℝ] H) (b : ℕ → H)
    (mu : ℕ → ℝ) (hmu : ∀ n, mu n ≠ 0)
    (heig : ∀ n, realNuclearGram T (b n) = mu n • b n)
    (y : H) (hy : y ∈ T.ker) (n : ℕ) :
    inner ℝ y (b n) = 0 :=
  realNuclearGram_nonzero_mode_orthogonal_kernel
    T (mu n) (hmu n) (b n) (heig n) y hy

#print axioms GegenbauerFock.Ultraspherical.realNuclearGram_zero_eigenspace_eq_kernel
#print axioms GegenbauerFock.Ultraspherical.realNuclearGram_nonzero_mode_orthogonal_kernel
#print axioms GegenbauerFock.Ultraspherical.realNuclearGram_nonzero_family_orthogonal_kernel

end GegenbauerFock.Ultraspherical
