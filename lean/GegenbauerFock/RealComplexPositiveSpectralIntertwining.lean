import GegenbauerFock.RealComplexPositiveSpectralTraceBridge

/-!
# V007 — real-to-complex spectral intertwining, with explicit assumptions

Let J : H_R -> H_C be a REAL-linear embedding candidate mapping the
chosen complete real Hilbert basis to a complete complex Hilbert basis.
If the bounded real and complex operators intertwine through J, the
complex eigenvalues follow automatically from the real eigenvalues.
Together with the previously kernel-certified positive spectral S1
bridge, this provides equality of the REAL projective nuclear S1
norm and the genuine Physlib-compatible COMPLEX CFC trace norm.

The existence of an intertwiner J for the concrete Gegenbauer Sturm
differential realization, and the complex operator's CFC IsTraceClass
membership, are NOT asserted here. They are explicit obligations.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open InnerProductSpace

variable {HR HC : Type*}
variable [NormedAddCommGroup HR] [InnerProductSpace ℝ HR] [CompleteSpace HR]
variable [NormedAddCommGroup HC] [InnerProductSpace ℂ HC] [CompleteSpace HC]

/-- A real-linear intertwiner preserving the chosen eigenbasis transfers
a REAL eigenvalue into the corresponding COMPLEX eigenvalue. -/
theorem complex_eigen_of_real_spectral_intertwining
    (R : HR →L[ℝ] HR) (T : HC →L[ℂ] HC)
    (bR : HilbertBasis ℕ ℝ HR) (bC : HilbertBasis ℕ ℂ HC)
    (J : HR →ₗ[ℝ] HC)
    (hJ : ∀ n, J (bR n) = bC n)
    (hcomm : ∀ x : HR, T (J x) = J (R x))
    (σ : ℕ → ℝ)
    (hR : ∀ n, R (bR n) = σ n • bR n) :
    ∀ n, T (bC n) = (σ n : ℂ) • bC n := by
  intro n
  calc
    T (bC n) = T (J (bR n)) := by rw [hJ n]
    _ = J (R (bR n)) := hcomm (bR n)
    _ = J (σ n • bR n) := by rw [hR n]
    _ = σ n • J (bR n) := by rw [map_smul]
    _ = (σ n : ℂ) • bC n := by
      rw [hJ n]
      exact (IsScalarTower.algebraMap_smul ℂ (σ n) (bC n)).symm

/-- A conditional exact real-projective / complex-CFC S1 comparison
from a verified real-linear spectral intertwining relation. -/
theorem realProjectiveNuclear_eq_complexPhyslibTraceNorm_of_intertwining
    (R : HR →L[ℝ] HR) (T : HC →L[ℂ] HC)
    (bR : HilbertBasis ℕ ℝ HR) (bC : HilbertBasis ℕ ℂ HC)
    (J : HR →ₗ[ℝ] HC)
    (hJ : ∀ n, J (bR n) = bC n)
    (hcomm : ∀ x : HR, T (J x) = J (R x))
    (σ : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n) (hs : Summable σ)
    (hR : ∀ n, R (bR n) = σ n • bR n)
    (hTpos : 0 ≤ T)
    (hTclass : ProbabilisticTheory.IsTraceClass T) :
    realNuclearInfimum R =
      ProbabilisticTheory.traceNorm T hTclass := by
  have hT := complex_eigen_of_real_spectral_intertwining
    R T bR bC J hJ hcomm σ hR
  exact realProjectiveNuclear_eq_complexPhyslibTraceNorm_of_shared_positive_spectrum
    R T bR bC σ hσ hs hR hT hTpos hTclass

#print axioms GegenbauerFock.Ultraspherical.complex_eigen_of_real_spectral_intertwining
#print axioms GegenbauerFock.Ultraspherical.realProjectiveNuclear_eq_complexPhyslibTraceNorm_of_intertwining

end GegenbauerFock.Ultraspherical
