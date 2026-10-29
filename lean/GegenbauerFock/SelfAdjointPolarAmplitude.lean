import GegenbauerFock.InjectivePolarAmplitude

/-!
# V007 — self-adjointness of the exact positive-spectrum polar amplitude

The genuine polar spectral factor P has a complete complex Hilbert basis
of eigenvectors with strictly positive REAL eigenvalues sqrt(mu).
The Hilbert adjoint agrees with P on each basis vector; completeness
and continuity imply equality on the full infinite-dimensional source.
No finite-dimensional adjoint or surjectivity is used.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- An actual factorization C = W P with P² = C†C can be chosen with
P Hilbert-selfadjoint, injective and positive real point spectrum on
a complete Hilbert basis, with Kummer multiplicity sum. -/
theorem exists_selfadjoint_polar_amplitude_kummer
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
      (∀ f, ‖P f‖ = ‖C lam alpha hlam ha f‖) ∧
      Function.Injective P ∧ P.adjoint = P := by
  classical
  obtain ⟨ι, u, v, mu, W, P, hp, hsum, hK, hWu, hPu, hC, hP2, hnorm, hinj⟩ :=
    exists_injective_unitary_polar_amplitude_kummer lam alpha hlam ha
  have hAdjBasis (i : ι) : P.adjoint (u i) = P (u i) := by
    apply u.repr.injective
    ext j
    rw [u.repr_apply_apply, u.repr_apply_apply]
    calc
      inner ℂ (u j) (P.adjoint (u i)) =
          inner ℂ (P (u j)) (u i) :=
            P.adjoint_inner_right (u j) (u i)
      _ = inner ℂ ((Real.sqrt (mu j) : ℂ) • u j) (u i) := by
            rw [hPu j]
      _ = inner ℂ (u j) ((Real.sqrt (mu i) : ℂ) • u i) := by
            by_cases hji : j = i
            · subst j
              rw [inner_smul_left, inner_smul_right]
              simp only [map_real, conj_ofReal]
            · rw [inner_smul_left, inner_smul_right,
                u.orthonormal.inner_eq_zero hji]
              simp
      _ = inner ℂ (u j) (P (u i)) := by rw [hPu i]
  have hself : P.adjoint = P := by
    apply ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr u.dense_span)
    rintro _ ⟨i, rfl⟩
    exact hAdjBasis i
  exact ⟨ι, u, mu, W, P, hp, hsum, hK, hPu, hC, hP2,
    hnorm, hinj, hself⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_selfadjoint_polar_amplitude_kummer

end GegenbauerFock.GeneralUltrasphericalFock
