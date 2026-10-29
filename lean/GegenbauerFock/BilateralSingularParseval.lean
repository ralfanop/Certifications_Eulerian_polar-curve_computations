import GegenbauerFock.CompletePositiveSingularHilbertBasis
import GegenbauerFock.PhyslibTraceBasisIndependence

/-!
# V007 — bilateral weighted singular Parseval identities

For the actual bounded compact Gegenbauer–Fock operator C, complete
two-sided positive singular Hilbert bases give pointwise coefficient
identities and exact unconditional nonnegative energy sums for both
C and C†. The sums are in the original infinite Hilbert spaces;
there are no finite-matrix approximations or unproved density assumptions.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Complete two-sided singular bases simultaneously diagonalize the
source and output transform energies, with exact positive square-singular
weights and the common (unregularized) Kummer spectral mass. -/
theorem exists_bilateral_singular_parseval_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (ι : Type)
      (u : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      (v : HilbertBasis ι ℂ InfiniteAnalysis.FockCoefficients)
      (mu : ι → ℝ),
      (∀ i, 0 < mu i) ∧
      Summable mu ∧
      (∑' i : ι, mu i) =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) ∧
      (∀ i f, inner ℂ (v i) (C lam alpha hlam ha f) =
        (Real.sqrt (mu i) : ℂ) * inner ℂ (u i) f) ∧
      (∀ i F, inner ℂ (u i) (C_adjoint lam alpha hlam ha F) =
        (Real.sqrt (mu i) : ℂ) * inner ℂ (v i) F) ∧
      (∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
        HasSum (fun i : ι => mu i * ‖inner ℂ (u i) f‖ ^ 2)
          (‖C lam alpha hlam ha f‖ ^ 2)) ∧
      (∀ F : InfiniteAnalysis.FockCoefficients,
        HasSum (fun i : ι => mu i * ‖inner ℂ (v i) F‖ ^ 2)
          (‖C_adjoint lam alpha hlam ha F‖ ^ 2)) := by
  classical
  obtain ⟨ι, u, v, mu, hp, hsum, hK, hC, hAdj⟩ :=
    exists_complete_positive_singular_hilbert_bases_kummer lam alpha hlam ha
  have hsource (i : ι) (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
      inner ℂ (v i) (C lam alpha hlam ha f) =
        (Real.sqrt (mu i) : ℂ) * inner ℂ (u i) f := by
    calc
      inner ℂ (v i) (C lam alpha hlam ha f) =
          inner ℂ (C_adjoint lam alpha hlam ha (v i)) f :=
            (C_adjoint_pairing lam alpha hlam ha (v i) f).symm
      _ = inner ℂ ((Real.sqrt (mu i) : ℂ) • u i) f := by rw [hAdj i]
      _ = (Real.sqrt (mu i) : ℂ) * inner ℂ (u i) f := by
        rw [inner_smul_ofReal_left]
        ring
  have houtput (i : ι) (F : InfiniteAnalysis.FockCoefficients) :
      inner ℂ (u i) (C_adjoint lam alpha hlam ha F) =
        (Real.sqrt (mu i) : ℂ) * inner ℂ (v i) F := by
    calc
      inner ℂ (u i) (C_adjoint lam alpha hlam ha F) =
          inner ℂ (C lam alpha hlam ha (u i)) F :=
            (C lam alpha hlam ha).adjoint_inner_right (u i) F
      _ = inner ℂ ((Real.sqrt (mu i) : ℂ) • v i) F := by rw [hC i]
      _ = (Real.sqrt (mu i) : ℂ) * inner ℂ (v i) F := by
        rw [inner_smul_ofReal_left]
        ring
  have hweight (i : ι) (z : ℂ) :
      ‖(Real.sqrt (mu i) : ℂ) * z‖ ^ 2 =
        mu i * ‖z‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (hp i)), mul_pow,
      Real.sq_sqrt (hp i).le]
  refine ⟨ι, u, v, mu, hp, hsum, hK, hsource, houtput, ?_, ?_⟩
  · intro f
    have h := ProbabilisticTheory.hasSum_norm_sq_inner_basis
      v (C lam alpha hlam ha f)
    have heq :
        (fun i : ι => ‖inner ℂ (v i) (C lam alpha hlam ha f)‖ ^ 2) =
          (fun i : ι => mu i * ‖inner ℂ (u i) f‖ ^ 2) := by
      funext i
      rw [hsource i f, hweight i]
    rw [heq] at h
    exact h
  · intro F
    have h := ProbabilisticTheory.hasSum_norm_sq_inner_basis
      u (C_adjoint lam alpha hlam ha F)
    have heq :
        (fun i : ι => ‖inner ℂ (u i) (C_adjoint lam alpha hlam ha F)‖ ^ 2) =
          (fun i : ι => mu i * ‖inner ℂ (v i) F‖ ^ 2) := by
      funext i
      rw [houtput i F, hweight i]
    rw [heq] at h
    exact h

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_bilateral_singular_parseval_kummer

end GegenbauerFock.GeneralUltrasphericalFock
