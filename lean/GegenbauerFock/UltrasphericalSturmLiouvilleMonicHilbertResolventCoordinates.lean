import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2HilbertBasis
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealSpectralModes
import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventSpectralGraph

/-!
# V007 — diagonal positive Sturm resolvent in the ACTUAL normalized Hilbert basis

The explicitly constructed Gegenbauer Hilbert basis is certified with
no eigenbasis existence assumption. The real weighted-L² resolvent R_t
acts diagonally on each normalized basis vector and on the exact ℓ²
Fourier coordinates of EVERY Hilbert-space vector:

    (b.repr (R_t f)) n =
      (t+n(n+2λ))⁻¹ * (b.repr f) n.

This is the concrete bounded diagonal resolvent representation.
The next separate theorem identifies the unbounded Sturm domain
with the corresponding weighted-ℓ² domain.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Every NORMALIZED Gegenbauer basis vector is an eigenvector of
the actual closed Sturm resolvent, with its exact scalar multiplier. -/
theorem sturmMonicRealHilbertBasis_full_resolvent_eigen
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    sturmRealPositiveResolventFullCLM lam t hlam ht
      (sturmMonicEigenCandidate_realL2_normalized lam hlam n) =
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
      sturmMonicEigenCandidate_realL2_normalized lam hlam n := by
  let g : SturmH lam :=
    sturmRealPolynomialLp lam hlam (sturmMonicEigenCandidate lam n)
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  let beta : ℝ := (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹
  have hG : R g = beta • g :=
    sturmMonicEigenCandidate_full_resolvent_diagonal lam t hlam ht n
  change R ((‖g‖)⁻¹ • g) = beta • ((‖g‖)⁻¹ • g)
  calc
    R ((‖g‖)⁻¹ • g) = (‖g‖)⁻¹ • R g := by rw [map_smul]
    _ = (‖g‖)⁻¹ • (beta • g) := by rw [hG]
    _ = beta • ((‖g‖)⁻¹ • g) := by
      simp only [smul_smul]
      rw [mul_comm (‖g‖)⁻¹ beta]

/-- Concrete diagonal MULTIPLIER identity on every ℓ² Fourier
coordinate of the normalized actual weighted-real-L² Hilbert basis. -/
theorem sturmMonicRealHilbertBasis_full_resolvent_repr_diagonal
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) (n : ℕ) :
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (sturmRealPositiveResolventFullCLM lam t hlam ht f) n =
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ *
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f n := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  let beta : ℝ := (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹
  have hsym := sturmRealPositiveResolventFullCLM_inner_symmetric
    lam t hlam ht (b n) f
  have heigen : R (b n) = beta • b n :=
    sturmMonicRealHilbertBasis_full_resolvent_eigen
      lam t hlam ht n
  rw [heigen, real_inner_smul_left] at hsym
  change b.repr (R f) n = beta * b.repr f n
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
  exact hsym.symm

#print axioms GegenbauerFock.Ultraspherical.sturmMonicRealHilbertBasis_full_resolvent_eigen
#print axioms GegenbauerFock.Ultraspherical.sturmMonicRealHilbertBasis_full_resolvent_repr_diagonal

end GegenbauerFock.Ultraspherical
