import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2Nonzero
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2Totality
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# V007 — normalized all-degree real L² Gegenbauer Hilbert eigenbasis

The explicitly constructed monic Sturm–Gegenbauer polynomials form a
complete orthogonal family. Their genuine L² norms are nonzero by the
separate atomless-measure and finite-root argument. Scaling each by its
own reciprocal norm yields an orthonormal family whose closed span is all
of the concrete weighted real L², so Mathlib constructs a HilbertBasis.
No abstract spectral completeness hypothesis is used.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

private def monicMode (lam : ℝ) (hlam : 0 < lam) (n : ℕ) : SturmH lam :=
  sturmRealPolynomialLp lam hlam (sturmMonicEigenCandidate lam n)

/-- Explicit genuinely normalized degree-n Gegenbauer eigenmode. -/
noncomputable def sturmMonicEigenCandidate_realL2_normalized
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) : SturmH lam :=
  (‖monicMode lam hlam n‖)⁻¹ • monicMode lam hlam n

/-- Every normalized mode has L² norm exactly one. -/
theorem sturmMonicEigenCandidate_realL2_normalized_norm
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    ‖sturmMonicEigenCandidate_realL2_normalized lam hlam n‖ = 1 := by
  have hp : 0 < ‖monicMode lam hlam n‖ :=
    sturmMonicEigenCandidate_realL2_norm_pos lam hlam n
  change ‖(‖monicMode lam hlam n‖)⁻¹ • monicMode lam hlam n‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg hp.le]
  exact inv_mul_cancel₀ (ne_of_gt hp)

/-- The actual normalized Gegenbauer family is orthonormal in real L². -/
theorem sturmMonicEigenCandidate_realL2_normalized_orthonormal
    (lam : ℝ) (hlam : 0 < lam) :
    Orthonormal ℝ (sturmMonicEigenCandidate_realL2_normalized lam hlam) := by
  refine ⟨sturmMonicEigenCandidate_realL2_normalized_norm lam hlam, ?_⟩
  intro n m hnm
  change inner ℝ
    ((‖monicMode lam hlam n‖)⁻¹ • monicMode lam hlam n)
    ((‖monicMode lam hlam m‖)⁻¹ • monicMode lam hlam m) = 0
  rw [inner_smul_left, inner_smul_right]
  have ho : inner ℝ (monicMode lam hlam n) (monicMode lam hlam m) = 0 :=
    sturmMonicEigenCandidate_realL2_orthogonal lam hlam n m hnm
  simp [ho]

/-- Scaling by the nonzero norms does not destroy totality: the
normalized family has trivial common orthogonal complement. -/
theorem sturmMonicEigenCandidate_realL2_normalized_orthogonal_eq_bot
    (lam : ℝ) (hlam : 0 < lam) :
    (Submodule.span ℝ
      (Set.range (sturmMonicEigenCandidate_realL2_normalized lam hlam)))ᗮ = ⊥ := by
  let S : Submodule ℝ (SturmH lam) :=
    Submodule.span ℝ (Set.range (monicMode lam hlam))
  let N : Submodule ℝ (SturmH lam) :=
    Submodule.span ℝ
      (Set.range (sturmMonicEigenCandidate_realL2_normalized lam hlam))
  have hSN : S ≤ N := by
    apply Submodule.span_le.mpr
    rintro z ⟨n, rfl⟩
    have hp : 0 < ‖monicMode lam hlam n‖ :=
      sturmMonicEigenCandidate_realL2_norm_pos lam hlam n
    have heq :
        (‖monicMode lam hlam n‖) •
          sturmMonicEigenCandidate_realL2_normalized lam hlam n =
            monicMode lam hlam n := by
      change (‖monicMode lam hlam n‖) •
        ((‖monicMode lam hlam n‖)⁻¹ • monicMode lam hlam n) =
          monicMode lam hlam n
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hp), one_smul]
    rw [← heq]
    exact N.smul_mem _ (Submodule.subset_span (Set.mem_range_self n))
  have htotal : Sᗮ = ⊥ :=
    sturmMonicEigenCandidate_realL2_orthogonalComplement_eq_bot lam hlam
  have hle : Nᗮ ≤ Sᗮ := Submodule.orthogonal_le hSN
  rw [htotal] at hle
  exact le_antisymm hle bot_le

/-- A genuine normalized Hilbert basis of the true ultraspherical
real weighted L², indexed by every natural Gegenbauer degree. -/
noncomputable def sturmMonicEigenCandidate_realL2_hilbertBasis
    (lam : ℝ) (hlam : 0 < lam) :
    HilbertBasis ℕ ℝ (SturmH lam) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (sturmMonicEigenCandidate_realL2_normalized_orthonormal lam hlam)
    (sturmMonicEigenCandidate_realL2_normalized_orthogonal_eq_bot lam hlam)

#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_normalized_norm
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_normalized_orthonormal
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_normalized_orthogonal_eq_bot
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_hilbertBasis

end GegenbauerFock.Ultraspherical
