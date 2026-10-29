import GegenbauerFock.CompletePositiveSingularFamily

/-!
# V007 — complete bilateral positive singular-value decomposition

The source Gram has a complete real-positive Hilbert eigenbasis.
Its singular vectors are orthonormal on the Fock output side. The
output singular family is also COMPLETE, because any orthogonal
vector is killed by the genuine adjoint C†; its kernel vanishes
by independently certified analytic coefficient uniqueness.

Thus the same index type labels Hilbert bases in both distinct
infinite-dimensional spaces. Neither compact-map surjectivity nor
a finite truncation is assumed.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The actual compact Gegenbauer–Fock transform admits a complete
two-sided singular Hilbert basis with all positive singular values,
normalization, and the unregularized Kummer square-sum identity. -/
theorem exists_complete_positive_singular_hilbert_bases_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (u : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (v : HilbertBasis ι ℂ InfiniteAnalysis.FockCoefficients)
      (mu : ι → ℝ),
      (∀ i, 0 < mu i) ∧
      Summable mu ∧
      (∑' i : ι, mu i) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ i, C lam alpha hlam ha (u i) =
        (Real.sqrt (mu i) : ℂ) • v i) ∧
      (∀ i, C_adjoint lam alpha hlam ha (v i) =
        (Real.sqrt (mu i) : ℂ) • u i) := by
  classical
  obtain ⟨ι, u, mu, w, hp, hw, hsum, hK, hC, hAdj⟩ :=
    exists_orthonormal_singular_family_kummer lam alpha hlam ha
  have hspan : (Submodule.span ℂ (Set.range w))ᗮ =
      (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients) := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hyw (i : ι) : inner ℂ (w i) y = 0 := by
      exact (Submodule.mem_orthogonal y).mp hy (w i)
        (Submodule.subset_span ⟨i, rfl⟩)
    have hzero : C_adjoint lam alpha hlam ha y = 0 := by
      apply u.repr.injective
      ext i
      rw [u.repr_apply_apply, u.repr_apply_apply]
      simp only [inner_zero_right]
      calc
        inner ℂ (u i) (C_adjoint lam alpha hlam ha y) =
            inner ℂ (C lam alpha hlam ha (u i)) y := by
              exact (C lam alpha hlam ha).adjoint_inner_right (u i) y
        _ = inner ℂ ((Real.sqrt (mu i) : ℂ) • w i) y := by
              rw [hC i]
        _ = 0 := by rw [inner_smul_left, hyw i]; simp
    exact (C_adjoint_injective_unconditional lam alpha hlam ha)
      (by simpa using hzero)
  let v : HilbertBasis ι ℂ InfiniteAnalysis.FockCoefficients :=
    HilbertBasis.mkOfOrthogonalEqBot hw hspan
  refine ⟨ι, u, v, mu, hp, hsum, hK, ?_, ?_⟩
  · intro i
    simpa only [v, HilbertBasis.coe_mkOfOrthogonalEqBot] using hC i
  · intro i
    simpa only [v, HilbertBasis.coe_mkOfOrthogonalEqBot] using hAdj i

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_complete_positive_singular_hilbert_bases_kummer

end GegenbauerFock.GeneralUltrasphericalFock
