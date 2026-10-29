import GegenbauerFock.CompletePositiveSingularHilbertBasis

/-!
# V007 — exact infinite-dimensional coefficient diagonalization of C and C†

A pair of complete singular Hilbert bases simultaneously conjugates
the concrete Gegenbauer–Fock transform and its genuine Hilbert adjoint
to the same positive real-valued diagonal multiplier on ℓ², expressed
by pointwise Hilbert-basis repr coefficients. This does not assert
surjectivity or bounded invertibility of the compact transform.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Genuine exact singular-coordinate diagonalization for both C and
C†, with a common positive diagonal whose squares have the Kummer sum. -/
theorem exists_bilateral_singular_diagonal_coordinates_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (u : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (v : HilbertBasis ι ℂ InfiniteAnalysis.FockCoefficients)
      (mu : ι → ℝ),
      (∀ i, 0 < mu i) ∧
      Summable mu ∧
      (∑' i : ι, mu i) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ (f : Lp ℂ 2 (Ultraspherical.measure lam)) (i : ι),
        v.repr (C lam alpha hlam ha f) i =
          (Real.sqrt (mu i) : ℂ) * u.repr f i) ∧
      (∀ (F : InfiniteAnalysis.FockCoefficients) (i : ι),
        u.repr (C_adjoint lam alpha hlam ha F) i =
          (Real.sqrt (mu i) : ℂ) * v.repr F i) := by
  classical
  obtain ⟨ι, u, v, mu, hp, hsum, hK, hC, hAdj⟩ :=
    exists_complete_positive_singular_hilbert_bases_kummer lam alpha hlam ha
  refine ⟨ι, u, v, mu, hp, hsum, hK, ?_, ?_⟩
  · intro f i
    rw [v.repr_apply_apply, u.repr_apply_apply]
    calc
      inner ℂ (v i) (C lam alpha hlam ha f) =
          inner ℂ (C_adjoint lam alpha hlam ha (v i)) f :=
            (C_adjoint_pairing lam alpha hlam ha (v i) f).symm
      _ = inner ℂ ((Real.sqrt (mu i) : ℂ) • u i) f := by rw [hAdj i]
      _ = (Real.sqrt (mu i) : ℂ) * inner ℂ (u i) f := by
        simp [inner_smul_left]
  · intro F i
    rw [u.repr_apply_apply, v.repr_apply_apply]
    calc
      inner ℂ (u i) (C_adjoint lam alpha hlam ha F) =
          inner ℂ (C lam alpha hlam ha (u i)) F :=
            (C lam alpha hlam ha).adjoint_inner_right (u i) F
      _ = inner ℂ ((Real.sqrt (mu i) : ℂ) • v i) F := by rw [hC i]
      _ = (Real.sqrt (mu i) : ℂ) * inner ℂ (v i) F := by
        simp [inner_smul_left]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_bilateral_singular_diagonal_coordinates_kummer

end GegenbauerFock.GeneralUltrasphericalFock
