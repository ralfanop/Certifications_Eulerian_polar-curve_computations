import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitHilbertCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertResolventCoordinates

/-!
# V007 — exact commutation of the genuine Sturm heat semigroup and resolvent

The actual strongly constructed full weighted real L² heat semigroup H_s,
s ≥ 0, commutes with the genuine full weighted real L² positive-shift
resolvent R_t = (t I - closure L₀)⁻¹, t > 0.

This is an identity of everywhere-defined bounded operators on the
concrete Hilbert space, not an identity only on Gegenbauer polynomials.
The proof compares their Fourier coefficients in the already certified
complete normalized Gegenbauer Hilbert basis. It invokes the independently
certified full-L² multiplier theorems and basis injectivity, with no
abstract spectral extension assumption.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The genuine full weighted-real-L² heat semigroup and positive
canonical Sturm resolvent commute on every Hilbert-space vector. -/
theorem sturmRealHeatLimitCLM_comp_fullResolvent_comm
    (lam t s : ℝ) (hlam : 0 < lam) (ht : 0 < t) (hs : 0 ≤ s) :
    (sturmRealHeatLimitCLM lam hlam s hs).comp
        (sturmRealPositiveResolventFullCLM lam t hlam ht) =
      (sturmRealPositiveResolventFullCLM lam t hlam ht).comp
        (sturmRealHeatLimitCLM lam hlam s hs) := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let T : SturmH lam →L[ℝ] SturmH lam :=
    sturmRealHeatLimitCLM lam hlam s hs
  let R : SturmH lam →L[ℝ] SturmH lam :=
    sturmRealPositiveResolventFullCLM lam t hlam ht
  apply ContinuousLinearMap.ext
  intro f
  apply b.repr.injective
  ext n
  change (b.repr (T (R f))) n = (b.repr (R (T f))) n
  rw [
    sturmRealHeatLimitCLM_hilbert_repr_diagonal lam hlam s hs (R f) n,
    sturmMonicRealHilbertBasis_full_resolvent_repr_diagonal
      lam t hlam ht f n,
    sturmMonicRealHilbertBasis_full_resolvent_repr_diagonal
      lam t hlam ht (T f) n,
    sturmRealHeatLimitCLM_hilbert_repr_diagonal lam hlam s hs f n
  ]
  ring

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_comp_fullResolvent_comm

end GegenbauerFock.Ultraspherical
