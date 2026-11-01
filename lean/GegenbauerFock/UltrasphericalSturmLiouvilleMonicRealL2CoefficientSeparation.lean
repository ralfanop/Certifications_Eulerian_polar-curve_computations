import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2DenseSpan

/-!
# V007 — complete separation by actual ultraspherical Gegenbauer coefficients

The real weighted-L² span of the explicit all-degree monic
Gegenbauer eigenvectors is dense, with no nonzero-vector or
orthonormal-basis assumption. Hence a genuine L² vector is zero if
and only if all its inner products with those concrete modes vanish.
The Gegenbauer coefficient family therefore separates every pair
of actual weighted-real-L² functions.

This is a consequence of previously kernel-certified Hilbert
density and the exact orthogonal complement theorem.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

private def monicModes (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    SturmH lam :=
  sturmRealPolynomialLp lam hlam (sturmMonicEigenCandidate lam n)

/-- The complete family of exact monic Gegenbauer mode coefficients
separates zero in the actual ultraspherical real L² Hilbert space. -/
theorem sturmMonicEigenCandidate_realL2_coefficients_eq_zero_iff
    (lam : ℝ) (hlam : 0 < lam) (f : SturmH lam) :
    (∀ n : ℕ, inner ℝ (monicModes lam hlam n) f = 0) ↔ f = 0 := by
  constructor
  · intro hc
    let S : Submodule ℝ (SturmH lam) :=
      Submodule.span ℝ (Set.range (monicModes lam hlam))
    have hspan : S ≤ (innerSL ℝ f).ker := by
      apply Submodule.span_le.mpr
      rintro u ⟨n, rfl⟩
      change inner ℝ f (monicModes lam hlam n) = 0
      exact (inner_eq_zero_symm).mpr (hc n)
    have hf : f ∈ Sᗮ := by
      apply (Submodule.mem_orthogonal' S f).2
      intro u hu
      exact hspan hu
    have hdense : S.topologicalClosure = ⊤ := by
      exact sturmMonicEigenCandidate_realL2_span_dense lam hlam
    have hbot : Sᗮ = ⊥ := by
      rw [← Submodule.orthogonal_closure, hdense]
      simp
    rw [hbot] at hf
    simpa only [Submodule.mem_bot] using hf
  · intro hf n
    rw [hf]
    exact inner_zero_right _

/-- Two actual weighted-real-L² vectors with the same coefficients
against every explicit all-degree Gegenbauer mode are equal. -/
theorem sturmMonicEigenCandidate_realL2_coefficients_injective
    (lam : ℝ) (hlam : 0 < lam)
    (f g : SturmH lam)
    (heq : ∀ n : ℕ,
      inner ℝ (monicModes lam hlam n) f =
      inner ℝ (monicModes lam hlam n) g) :
    f = g := by
  have hz : ∀ n : ℕ,
      inner ℝ (monicModes lam hlam n) (f - g) = 0 := by
    intro n
    rw [inner_sub_right, heq n, sub_self]
  have hf : f - g = 0 :=
    (sturmMonicEigenCandidate_realL2_coefficients_eq_zero_iff
      lam hlam (f - g)).mp hz
  exact sub_eq_zero.mp hf

#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_coefficients_eq_zero_iff
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_coefficients_injective

end GegenbauerFock.Ultraspherical
