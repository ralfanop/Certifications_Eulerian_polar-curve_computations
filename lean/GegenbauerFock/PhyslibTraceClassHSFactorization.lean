import GegenbauerFock.PhyslibPolarFactorCompat
import GegenbauerFock.PhyslibHilbertSchmidtCompat

/-!
# V007 — Hilbert--Schmidt polar factorization of arbitrary trace-class maps

For an arbitrary bounded trace-class endomorphism on a complete complex
Hilbert space, `S = CFC.sqrt (CFC.abs T)` is Hilbert--Schmidt. The
bounded polar contraction `U` then gives `T = (U*S)*S`, with both
factors genuinely in Physlib-compatible S₂.

This is a constructive analytical prerequisite for general S₁ addition.
It does NOT assume an unproved S₂*S₂ ⊆ S₁ theorem, nor claim the
triangle inequality or Banach completeness for S₁. No new axioms.
-/

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The positive square root of the actual CFC absolute value is
Hilbert--Schmidt whenever T has a genuine CFC trace-class witness. -/
theorem traceClass_sqrt_abs_isHS (T : H →L[ℂ] H)
    (hT : IsTraceClass T) :
    HilbertSchmidt.IsHilbertSchmidt (CFC.sqrt (CFC.abs T)) := by
  let A : H →L[ℂ] H := CFC.abs T
  let S : H →L[ℂ] H := CFC.sqrt A
  let b := hT.choose_spec.choose
  have hA : 0 ≤ A := CFC.abs_nonneg T
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA
  have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg A)
  have hSstar : ContinuousLinearMap.adjoint S = S :=
    (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
  have hpt (i : hT.choose) :
      (inner ℂ (b i) (A (b i))).re = ‖S (b i)‖ ^ 2 := by
    have hi : inner ℂ (b i) (A (b i)) =
        inner ℂ (S (b i)) (S (b i)) := by
      rw [← hSS]
      show inner ℂ (b i) ((S * S) (b i)) =
        inner ℂ (S (b i)) (S (b i))
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left S (S (b i)) (b i), hSstar]
    rw [hi, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hsum : Summable (fun i : hT.choose => ‖S (b i)‖ ^ 2) := by
    have hs : Summable (fun i : hT.choose =>
        (inner ℂ (b i) (A (b i))).re) := hT.choose_spec.choose_spec
    apply hs.congr
    intro i
    exact hpt i
  exact ⟨hT.choose, b, hsum⟩

/-- Bounded polar left multiplication preserves HS summability,
with the uniform contraction bound supplied by the polar factor. -/
theorem traceClass_polar_sqrt_abs_isHS (T : H →L[ℂ] H)
    (hT : IsTraceClass T) :
    HilbertSchmidt.IsHilbertSchmidt
      ((Polar.polarFactor T).comp (CFC.sqrt (CFC.abs T))) := by
  let S : H →L[ℂ] H := CFC.sqrt (CFC.abs T)
  let U : H →L[ℂ] H := Polar.polarFactor T
  let hS := traceClass_sqrt_abs_isHS T hT
  rcases hS with ⟨w, b, hsum⟩
  refine ⟨w, b, ?_⟩
  apply Summable.of_nonneg_of_le
  · intro i
    exact sq_nonneg _
  · intro i
    change ‖U (S (b i))‖ ^ 2 ≤ ‖S (b i)‖ ^ 2
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
      (Polar.polarFactor_norm_le T (S (b i)))
  · exact hsum

/-- Every actual trace-class bounded Hilbert endomorphism factors
as a product of TWO genuine Hilbert--Schmidt endomorphisms.
This is the missing constructive direction S₁ ⊆ S₂*S₂. -/
theorem traceClass_exists_HS_mul_HS (T : H →L[ℂ] H)
    (hT : IsTraceClass T) :
    ∃ R S : H →L[ℂ] H,
      HilbertSchmidt.IsHilbertSchmidt R ∧
      HilbertSchmidt.IsHilbertSchmidt S ∧
      R * S = T := by
  let S : H →L[ℂ] H := CFC.sqrt (CFC.abs T)
  let U : H →L[ℂ] H := Polar.polarFactor T
  let R : H →L[ℂ] H := U.comp S
  refine ⟨R, S, traceClass_polar_sqrt_abs_isHS T hT,
    traceClass_sqrt_abs_isHS T hT, ?_⟩
  have hsquare : S * S = CFC.abs T :=
    CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)
  calc
    R * S = (U * S) * S := rfl
    _ = U * (S * S) := mul_assoc _ _ _
    _ = U * CFC.abs T := by rw [hsquare]
    _ = T := Polar.polarFactor_mul_absOperator T

#print axioms ProbabilisticTheory.traceClass_sqrt_abs_isHS
#print axioms ProbabilisticTheory.traceClass_polar_sqrt_abs_isHS
#print axioms ProbabilisticTheory.traceClass_exists_HS_mul_HS

end ProbabilisticTheory
