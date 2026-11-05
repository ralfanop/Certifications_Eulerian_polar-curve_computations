import GegenbauerFock.UnitaryPolarSpectrumFactorization

/-!
# V007 — exact energy and injectivity of the polar spectral amplitude

The certified unitary phase W and bounded square-root spectral
amplitude P satisfy C = W P, P² = C†C and carry the strictly positive
complete singular data. These identities imply exactly equal operator
energies ‖P f‖ = ‖C f‖ for every source vector; since genuine C is
injective, so is P. No lower bound on P or bounded inverse is claimed.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- A genuine polar-type spectral factor of C is injective and has
exactly the same pointwise Hilbert norm as the original compact C,
as well as the exact Kummer square-singular-value spectral sum. -/
theorem exists_injective_unitary_polar_amplitude_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (u : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (v : HilbertBasis ι ℂ InfiniteAnalysis.FockCoefficients)
      (mu : ι → ℝ)
      (W : Lp ℂ 2 (Ultraspherical.measure lam) ≃ₗᵢ[ℂ]
        InfiniteAnalysis.FockCoefficients)
      (P : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)),
      (∀ i, 0 < mu i) ∧
      Summable mu ∧
      (∑' i : ι, mu i) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ i, W (u i) = v i) ∧
      (∀ i, P (u i) = (Real.sqrt (mu i) : ℂ) • u i) ∧
      (∀ f, C lam alpha hlam ha f = W (P f)) ∧
      (∀ f, gram lam alpha hlam ha f = P (P f)) ∧
      (∀ f, ‖P f‖ = ‖C lam alpha hlam ha f‖) ∧
      Function.Injective P := by
  obtain ⟨ι, u, v, mu, W, P, hp, hsum, hK, hWu, hPu, hC, hP2⟩ :=
    exists_unitary_positive_spectrum_factorization_kummer lam alpha hlam ha
  have hnorm : ∀ f, ‖P f‖ = ‖C lam alpha hlam ha f‖ := by
    intro f
    calc
      ‖P f‖ = ‖W (P f)‖ := (W.norm_map (P f)).symm
      _ = ‖C lam alpha hlam ha f‖ := congrArg norm (hC f).symm
  have hPinj : Function.Injective P := by
    intro f g hfg
    apply C_injective lam alpha hlam ha
    calc
      C lam alpha hlam ha f = W (P f) := hC f
      _ = W (P g) := congrArg W hfg
      _ = C lam alpha hlam ha g := (hC g).symm
  exact ⟨ι, u, v, mu, W, P, hp, hsum, hK,
    hWu, hPu, hC, hP2, hnorm, hPinj⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_injective_unitary_polar_amplitude_kummer

end GegenbauerFock.GeneralUltrasphericalFock
