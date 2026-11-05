import GegenbauerFock.SelfAdjointPolarAmplitude
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# V007 — true nonnegative polar amplitude in the infinite Hilbert model

For the genuine C, the compact spectral factor P is self-adjoint and
its complete Hilbert eigenbasis has positive real weights sqrt(mu_i).
Its quadratic form is the unconditional weighted Fourier energy
sum Σ sqrt(mu_i) * |<u_i,f>|², hence nonnegative for every f.

This certifies positivity of the ACTUAL bounded P without imposing a
finite-dimensional basis, surjectivity or spectral gap.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The true C admits C=W P, P²=C†C, with P self-adjoint AND
positive semidefinite on the complete infinite-dimensional source.
All singular weights are strictly positive and Kummer-summable. -/
theorem exists_positive_polar_amplitude_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (u : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (mu : ι → ℝ)
      (W : Lp ℂ 2 (Ultraspherical.measure lam) ≃ₗᵢ[ℂ]
        InfiniteAnalysis.FockCoefficients)
      (P : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)),
      (∀ i, 0 < mu i) ∧
      Summable mu ∧
      (∑' i : ι, mu i) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ i, P (u i) = (Real.sqrt (mu i) : ℂ) • u i) ∧
      (∀ f, C lam alpha hlam ha f = W (P f)) ∧
      (∀ f, gram lam alpha hlam ha f = P (P f)) ∧
      Function.Injective P ∧
      P.adjoint = P ∧
      (P : Lp ℂ 2 (Ultraspherical.measure lam) →ₗ[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)).IsPositive := by
  classical
  obtain ⟨ι, u, mu, W, P, hp, hsum, hK, hPu, hC, hP2, hnorm, hinj, hself⟩ :=
    exists_selfadjoint_polar_amplitude_kummer lam alpha hlam ha
  have hsym : (P : Lp ℂ 2 (Ultraspherical.measure lam) →ₗ[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)).IsSymmetric := by
    intro f g
    calc
      inner ℂ (P f) g = inner ℂ f (P.adjoint g) :=
        (P.adjoint_inner_right f g).symm
      _ = inner ℂ f (P g) := by rw [hself]
  have hpos (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
      0 ≤ RCLike.re (inner ℂ (P f) f) := by
    have hpair (i : ι) :
        inner ℂ (P f) (u i) =
          (Real.sqrt (mu i) : ℂ) * inner ℂ f (u i) := by
      calc
        inner ℂ (P f) (u i) =
            inner ℂ f (P.adjoint (u i)) :=
              (P.adjoint_inner_right f (u i)).symm
        _ = inner ℂ f (P (u i)) := by rw [hself]
        _ = inner ℂ f ((Real.sqrt (mu i) : ℂ) • u i) := by rw [hPu i]
        _ = (Real.sqrt (mu i) : ℂ) * inner ℂ f (u i) := by
          rw [inner_smul_right]
    have hterms (i : ι) :
        RCLike.re (inner ℂ (P f) (u i) * inner ℂ (u i) f) =
          Real.sqrt (mu i) * ‖inner ℂ (u i) f‖ ^ 2 := by
      rw [hpair i, mul_assoc]
      have hc : inner ℂ f (u i) = star (inner ℂ (u i) f) :=
        (inner_conj_symm f (u i)).symm
      rw [hc, Complex.star_def, Complex.conj_mul']
      norm_cast
    have hs0 : HasSum
        (fun i : ι => RCLike.re
          (inner ℂ (P f) (u i) * inner ℂ (u i) f))
        (RCLike.re (inner ℂ (P f) f)) :=
      RCLike.hasSum_re ℂ (u.hasSum_inner_mul_inner (P f) f)
    have hs : HasSum
        (fun i : ι => Real.sqrt (mu i) * ‖inner ℂ (u i) f‖ ^ 2)
        (RCLike.re (inner ℂ (P f) f)) := by
      simpa only [hterms] using hs0
    rw [← hs.tsum_eq]
    exact tsum_nonneg fun i =>
      mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  refine ⟨ι, u, mu, W, P, hp, hsum, hK, hPu, hC, hP2, hinj,
    hself, ?_⟩
  exact ⟨hsym, hpos⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_positive_polar_amplitude_kummer

end GegenbauerFock.GeneralUltrasphericalFock
