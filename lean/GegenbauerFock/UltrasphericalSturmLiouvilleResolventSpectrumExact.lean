import GegenbauerFock.UltrasphericalSturmLiouvilleResolventCompactExact
import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventZeroSpectrum
import GegenbauerFock.UltrasphericalSturmLiouvilleRealFullResolventSelfAdjoint
import GegenbauerFock.UltrasphericalSturmLiouvilleRealFullResolventPositive
import GegenbauerFock.DiagonalMultiplierSpectrum

/-!
# Manuscript 13, Corollary 5.2: exact spectrum of the closed Gegenbauer–Sturm resolvent

For `λ, t > 0` let `R_t` be the bounded resolvent `(tI + D_λ)⁻¹` of the canonical closure of the
ultraspherical Sturm–Liouville operator on the real weighted `L²`, and
`β_n = (t + n(n+2λ))⁻¹`. Then

* `sturmRealResolvent_spectrum_eq`: `spectrum ℝ R_t = {0} ∪ {β_n : n ∈ ℕ}`;
* `sturmRealResolvent_spectrum_isolated`: every nonzero spectral value is isolated;
* `sturmRealResolvent_zero_accumulation`: `0` is an accumulation point of the spectrum;
* `corollary_5_2`: all statements of Corollary 5.2 together — compact, positive, selfadjoint,
  eigenvalues `β_n` on the normalized Gegenbauer eigenmodes, spectrum `{0} ∪ {β_n}`, zero its
  only accumulation point.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter Topology GegenbauerFock.DiagonalSpectrum

private abbrev H (lam : ℝ) := Lp ℝ 2 (measure lam)

theorem sturmRealResolvent_spectrum_eq (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    spectrum ℝ (sturmRealPositiveResolventFullCLM lam t hlam ht) =
      insert 0 (Set.range fun n : ℕ => (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹) := by
  apply le_antisymm
  · exact spectrum_subset_insert_zero_range (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam)
      _ _ (sturmMonicRealHilbertBasis_full_resolvent_repr_diagonal lam t hlam ht)
      (sturmResolventMultiplier_tendsto_zero lam t hlam ht)
  · rintro μ (rfl | ⟨n, rfl⟩)
    · exact sturmRealResolvent_zero_mem_spectrum lam t hlam ht
    · refine eigen_mem_spectrum _ (e := sturmMonicEigenCandidate_realL2_normalized lam hlam n)
        (fun hz => ?_) (sturmMonicRealHilbertBasis_full_resolvent_eigen lam t hlam ht n)
      have h := sturmMonicEigenCandidate_realL2_normalized_norm lam hlam n
      rw [hz, norm_zero] at h
      exact zero_ne_one h

theorem sturmRealResolvent_spectrum_isolated (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (μ : ℝ) (hμ : μ ≠ 0) :
    ∀ᶠ ν in 𝓝[≠] μ, ν ∉ spectrum ℝ (sturmRealPositiveResolventFullCLM lam t hlam ht) :=
  isolated_of_ne_zero _ (sturmResolventMultiplier_tendsto_zero lam t hlam ht) _
    (sturmRealResolvent_spectrum_eq lam t hlam ht).le hμ

theorem sturmRealResolvent_zero_accumulation (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    (0 : ℝ) ∈ closure
      (spectrum ℝ (sturmRealPositiveResolventFullCLM lam t hlam ht) \ {0}) :=
  zero_mem_closure _ (sturmResolventMultiplier_tendsto_zero lam t hlam ht) _
    (fun n => (sturmRealResolvent_spectrum_eq lam t hlam ht).ge (Or.inr ⟨n, rfl⟩))
    (fun n => (sturmResolventMultiplier_pos lam t hlam ht n).ne')

/-- **Corollary 5.2** of manuscript 13, in full. -/
theorem corollary_5_2 (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    let R := sturmRealPositiveResolventFullCLM lam t hlam ht
    let β : ℕ → ℝ := fun n => (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹
    IsCompactOperator R ∧ IsSelfAdjoint R ∧ (∀ f : H lam, 0 ≤ inner ℝ (R f) f) ∧
      (∀ n, R (sturmMonicEigenCandidate_realL2_normalized lam hlam n) =
        β n • sturmMonicEigenCandidate_realL2_normalized lam hlam n) ∧
      spectrum ℝ R = insert 0 (Set.range β) ∧
      (∀ μ ≠ 0, ∀ᶠ ν in 𝓝[≠] μ, ν ∉ spectrum ℝ R) ∧
      (0 : ℝ) ∈ closure (spectrum ℝ R \ {0}) :=
  ⟨sturmRealClosedResolvent_isCompactOperator lam t hlam ht,
    sturmRealPositiveResolventFullCLM_isSelfAdjoint lam t hlam ht,
    sturmRealPositiveResolventFullCLM_inner_nonneg lam t hlam ht,
    sturmMonicRealHilbertBasis_full_resolvent_eigen lam t hlam ht,
    sturmRealResolvent_spectrum_eq lam t hlam ht,
    sturmRealResolvent_spectrum_isolated lam t hlam ht,
    sturmRealResolvent_zero_accumulation lam t hlam ht⟩

#print axioms GegenbauerFock.Ultraspherical.sturmRealResolvent_spectrum_eq
#print axioms GegenbauerFock.Ultraspherical.corollary_5_2

end GegenbauerFock.Ultraspherical
