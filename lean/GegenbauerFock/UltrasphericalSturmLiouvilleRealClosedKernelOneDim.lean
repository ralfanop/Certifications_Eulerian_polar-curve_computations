import GegenbauerFock.UltrasphericalSturmLiouvilleRealClosedSpectralKernel
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Simplicity of the zero eigenvalue in the genuine closed Sturm operator

The canonical real weighted-L² ultraspherical Sturm operator has an
explicit normalized Gegenbauer Hilbert eigenbasis. Its previously
certified zero-kernel theorem says all positive-degree Fourier
coefficients vanish. The Hilbert-basis representation turns this
coordinate statement into the stronger vector-space identity:
every zero eigenvector is a scalar multiple of the constant mode.

The statement concerns the actual closed differential operator and
its genuine (possibly unbounded) graph domain.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Every nullvector of the genuine closed ultraspherical Sturm
operator is a scalar multiple of the explicit normalized constant
Gegenbauer mode; there are no further L² zero modes. -/
theorem sturmRealClosed_kernel_vector_eq_scalar_zero_mode
    (lam : ℝ) (hlam : 0 < lam)
    (x : (sturmRealPartialOperator lam hlam).closure.domain)
    (hx : (sturmRealPartialOperator lam hlam).closure x = 0) :
    ∃ c : ℝ, (x : SturmH lam) =
      c • sturmMonicEigenCandidate_realL2_normalized lam hlam 0 := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let c : ℝ := (b.repr (x : SturmH lam)) 0
  have hcoeff : ∀ n : ℕ, n ≠ 0 →
      (b.repr (x : SturmH lam)) n = 0 := by
    exact (sturmRealClosed_kernel_iff_monicHilbert_positive_coeff_zero
      lam hlam x).mp hx
  have hsingle : b.repr (x : SturmH lam) =
      lp.single 2 0 c := by
    ext n
    by_cases hn : n = 0
    · subst n
      simp [c]
    · simp [lp.single_apply, hn, hcoeff n hn]
  have hb : b 0 =
      sturmMonicEigenCandidate_realL2_normalized lam hlam 0 := by
    simp only [b, sturmMonicEigenCandidate_realL2_hilbertBasis,
      HilbertBasis.coe_mkOfOrthogonalEqBot]
  refine ⟨c, ?_⟩
  rw [← hb]
  apply b.repr.injective
  calc
    b.repr (x : SturmH lam) = lp.single 2 0 c := hsingle
    _ = c • lp.single 2 0 (1 : ℝ) := by
      simpa only [smul_eq_mul, mul_one] using
        (lp.single_smul (E := (fun _ : ℕ => ℝ)) 2 0 c (1 : ℝ))
    _ = b.repr (c • b 0) := by
      rw [map_smul, HilbertBasis.repr_self]

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_kernel_vector_eq_scalar_zero_mode

end GegenbauerFock.Ultraspherical
