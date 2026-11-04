import GegenbauerFock.RealComplexPositiveSpectralIntertwining
import GegenbauerFock.PhyslibTraceBasisIndependence

/-!
# V007 — automatic complex CFC trace class from a positive summable eigenbasis

Previously, the formal real-projective/complex-CFC S1 spectral bridge
required genuine complex CFC IsTraceClass membership as an independent
hypothesis. This module DISCHARGES that hypothesis from:

* positivity of the ACTUAL complex bounded operator;
* a complete complex Hilbert basis of positive, summable eigenvalues.

The proof does not simply equate summability of a preferred diagonal
to the source-compatible Physlib predicate (which uses a Set-indexed
existential Hilbert basis). It forms the positive CFC square root and
uses selfadjoint Hilbert-Schmidt basis-independence to produce a
legitimate Set-indexed trace-class witness on the same complex space.

The resulting real-to-complex theorem still requires the explicitly
given real-linear spectral intertwiner between actual operators.
Its existence for a particular Sturm/Gram realization is NOT asserted.

No extra axioms, no unproved CFC real-to-complex equivalence.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open InnerProductSpace

variable {HR HC : Type*}
variable [NormedAddCommGroup HR] [InnerProductSpace ℝ HR] [CompleteSpace HR]
variable [NormedAddCommGroup HC] [InnerProductSpace ℂ HC] [CompleteSpace HC]

/-- A positive complex operator whose diagonal is summable in a
complete Nat-indexed complex Hilbert basis genuinely satisfies the
CFC-absolute source-compatible Physlib trace-class predicate. -/
theorem complex_nonneg_isTraceClass_of_summable_natBasis_diagonal
    (T : HC →L[ℂ] HC) (hTpos : 0 ≤ T)
    (b : HilbertBasis ℕ ℂ HC)
    (hs : Summable (fun n : ℕ =>
      (inner ℂ (b n) (T (b n))).re)) :
    ProbabilisticTheory.IsTraceClass T := by
  let S : HC →L[ℂ] HC := CFC.sqrt T
  have hSself : IsSelfAdjoint S :=
    .of_nonneg (CFC.sqrt_nonneg T)
  have hSstar : ContinuousLinearMap.adjoint S = S :=
    (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
  have hSS : S * S = T := CFC.sqrt_mul_sqrt_self T hTpos
  have hpt (x : HC) :
      (inner ℂ x (T x)).re = ‖S x‖ ^ 2 := by
    have hinner : inner ℂ x (T x) = inner ℂ (S x) (S x) := by
      rw [← hSS]
      show inner ℂ x ((S * S) x) = _
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left S (S x) x, hSstar]
    rw [hinner, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hb : Summable (fun n : ℕ => ‖S (b n)‖ ^ 2) :=
    hs.congr (fun n => hpt (b n))
  obtain ⟨w, c, _⟩ := exists_hilbertBasis ℂ HC
  have hc : Summable (fun i : w => ‖S (c i)‖ ^ 2) :=
    (ProbabilisticTheory.hasSum_norm_sq_apply_of_selfAdjoint
      hSself b c hb).summable
  have hcdiag : Summable (fun i : w =>
      (inner ℂ (c i) (T (c i))).re) :=
    hc.congr (fun i => (hpt (c i)).symm)
  exact ProbabilisticTheory.isTraceClass_of_nonneg_of_summable
    T hTpos c hcdiag

/-- A positive complex operator with the same nonnegative summable
eigenvalues as a real Hilbert operator is AUTOMATICALLY CFC trace-class.
The equality of the REAL universal projective nuclear norm and the
COMPLEX source-compatible Physlib CFC trace norm is then exact. -/
theorem realProjectiveNuclear_eq_complexPhyslibTraceNorm_autoClass_of_sharedSpectrum
    (R : HR →L[ℝ] HR) (T : HC →L[ℂ] HC)
    (bR : HilbertBasis ℕ ℝ HR) (bC : HilbertBasis ℕ ℂ HC)
    (σ : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n) (hs : Summable σ)
    (hR : ∀ n, R (bR n) = σ n • bR n)
    (hT : ∀ n, T (bC n) = (σ n : ℂ) • bC n)
    (hTpos : 0 ≤ T) :
    ∃ hTclass : ProbabilisticTheory.IsTraceClass T,
      realNuclearInfimum R =
        ProbabilisticTheory.traceNorm T hTclass := by
  have hCdiag (n : ℕ) :
      (inner ℂ (bC n) (T (bC n))).re = σ n := by
    rw [hT n, inner_smul_right, inner_self_eq_norm_sq_to_K,
      bC.orthonormal.norm_eq_one n]
    norm_num
  have hsC : Summable (fun n : ℕ =>
      (inner ℂ (bC n) (T (bC n))).re) :=
    hs.congr (fun n => (hCdiag n).symm)
  have hTclass : ProbabilisticTheory.IsTraceClass T :=
    complex_nonneg_isTraceClass_of_summable_natBasis_diagonal T hTpos bC hsC
  exact ⟨hTclass,
    realProjectiveNuclear_eq_complexPhyslibTraceNorm_of_shared_positive_spectrum
      R T bR bC σ hσ hs hR hT hTpos hTclass⟩

/-- A real-linear intertwiner matching complete real and complex
Hilbert eigenbases transfers the positive real trace spectrum. The
complex CFC trace-class membership and exact cross-field S1 equality
are then PRODUCED by the theorem, rather than assumed separately.
The intertwiner and complex positivity remain explicit obligations. -/
theorem realProjectiveNuclear_eq_complexPhyslibTraceNorm_autoClass_of_intertwining
    (R : HR →L[ℝ] HR) (T : HC →L[ℂ] HC)
    (bR : HilbertBasis ℕ ℝ HR) (bC : HilbertBasis ℕ ℂ HC)
    (J : HR →ₗ[ℝ] HC)
    (hJ : ∀ n, J (bR n) = bC n)
    (hcomm : ∀ x : HR, T (J x) = J (R x))
    (σ : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n) (hs : Summable σ)
    (hR : ∀ n, R (bR n) = σ n • bR n)
    (hTpos : 0 ≤ T) :
    ∃ hTclass : ProbabilisticTheory.IsTraceClass T,
      realNuclearInfimum R =
        ProbabilisticTheory.traceNorm T hTclass := by
  have hT := complex_eigen_of_real_spectral_intertwining
    R T bR bC J hJ hcomm σ hR
  exact realProjectiveNuclear_eq_complexPhyslibTraceNorm_autoClass_of_sharedSpectrum
    R T bR bC σ hσ hs hR hT hTpos

#print axioms GegenbauerFock.Ultraspherical.complex_nonneg_isTraceClass_of_summable_natBasis_diagonal
#print axioms GegenbauerFock.Ultraspherical.realProjectiveNuclear_eq_complexPhyslibTraceNorm_autoClass_of_sharedSpectrum
#print axioms GegenbauerFock.Ultraspherical.realProjectiveNuclear_eq_complexPhyslibTraceNorm_autoClass_of_intertwining

end GegenbauerFock.Ultraspherical
