import GegenbauerFock.UltrasphericalSturmLiouvilleMonicFiniteSpectralPoincare
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2Unitary
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# V007 — sharp *infinite* spectral Poincare inequality in true weighted real L²

Let b be the explicitly constructed normalized, complete Gegenbauer Hilbert
basis of the actual ultraspherical weighted real L². If the degree-zero
Fourier coefficient of f is zero and its spectral Dirichlet series is
summable, then

  (1 + 2λ) ‖f‖² ≤ ∑' n, n(n+2λ) |(b.repr f) n|².

Unlike the previously certified finite-coefficient statement, this
is a genuine infinite-series inequality for arbitrary weighted-L²
vectors in the spectral Dirichlet-form domain. Parseval is derived
from the built-in real Hilbert-basis identity, not postulated.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Parseval in sum-of-squares form, for the *actual* weighted-real-L²
Gegenbauer Hilbert basis. -/
theorem sturmMonic_realL2_parseval_tsum_sq
    (lam : ℝ) (hlam : 0 < lam) (f : SturmH lam) :
    (∑' n : ℕ,
      ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f n) ^ 2) =
      ‖f‖ ^ 2 := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  have hterm (n : ℕ) :
      ((b.repr f) n) ^ 2 = inner ℝ f (b n) * inner ℝ (b n) f := by
    rw [HilbertBasis.repr_apply_apply, real_inner_comm f (b n)]
    ring
  calc
    (∑' n : ℕ, ((b.repr f) n) ^ 2) =
        ∑' n : ℕ, inner ℝ f (b n) * inner ℝ (b n) f :=
      tsum_congr hterm
    _ = inner ℝ f f := b.tsum_inner_mul_inner f f
    _ = ‖f‖ ^ 2 := real_inner_self_eq_norm_sq f

/-- Full infinite Poincare inequality on the actual ultraspherical
Dirichlet-form domain, characterized by summable spectral energy.
The constant is the sharp degree-one spectral rate. -/
theorem sturmMonic_realL2_infinite_spectral_poincare
    (lam : ℝ) (hlam : 0 < lam) (f : SturmH lam)
    (hzero :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 = 0)
    (henergy : Summable (fun n : ℕ =>
      ((n : ℝ) * ((n : ℝ) + 2 * lam)) *
        ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f n) ^ 2)) :
    (1 + 2 * lam) * ‖f‖ ^ 2 ≤
      ∑' n : ℕ, ((n : ℝ) * ((n : ℝ) + 2 * lam)) *
        ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f n) ^ 2 := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let a := b.repr f
  have hgap : 0 ≤ 1 + 2 * lam := by linarith
  have hnonneg (n : ℕ) :
      0 ≤ (1 + 2 * lam) * (a n) ^ 2 :=
    mul_nonneg hgap (sq_nonneg _)
  have hpoint (n : ℕ) :
      (1 + 2 * lam) * (a n) ^ 2 ≤
        ((n : ℝ) * ((n : ℝ) + 2 * lam)) * (a n) ^ 2 := by
    by_cases hn : n = 0
    · subst n
      simp [a, b, hzero]
    · have hs := sturmEigenvalue_positive_degree_gap lam hlam n hn
      have hw : 1 + 2 * lam ≤
          (n : ℝ) * ((n : ℝ) + 2 * lam) := by
        unfold sturmEigenvalue at hs
        linarith
      exact mul_le_mul_of_nonneg_right hw (sq_nonneg (a n))
  have hsum : Summable (fun n : ℕ =>
      (1 + 2 * lam) * (a n) ^ 2) :=
    Summable.of_nonneg_of_le hnonneg hpoint henergy
  have hbound := hsum.tsum_le_tsum hpoint henergy
  rw [tsum_mul_left] at hbound
  have hp := sturmMonic_realL2_parseval_tsum_sq lam hlam f
  change (1 + 2 * lam) *
    (∑' n : ℕ, ((b.repr f) n) ^ 2) ≤
      ∑' n : ℕ, ((n : ℝ) * ((n : ℝ) + 2 * lam)) *
        ((b.repr f) n) ^ 2 at hbound
  rw [hp] at hbound
  exact hbound

#print axioms GegenbauerFock.Ultraspherical.sturmMonic_realL2_parseval_tsum_sq
#print axioms GegenbauerFock.Ultraspherical.sturmMonic_realL2_infinite_spectral_poincare

end GegenbauerFock.Ultraspherical
