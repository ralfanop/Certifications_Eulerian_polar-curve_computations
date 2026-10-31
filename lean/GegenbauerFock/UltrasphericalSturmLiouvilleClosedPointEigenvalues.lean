import GegenbauerFock.UltrasphericalSturmLiouvilleExactGegenbauerSpectralClosure

/-!
# Point eigenvalues of the closed ultraspherical Sturm operator

The kernel-certified all-degree Gegenbauer Hilbert basis and exact closed
diagonal realization exclude every nonzero eigenvector at a spectral
parameter outside the explicitly enumerated eigenvalue sequence. The
result concerns the canonical closure of the actual polynomial operator,
not an unrelated diagonal model.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- A scalar outside the explicit Gegenbauer sequence has no nonzero
eigenvector for the genuine closed real ultraspherical Sturm operator. -/
theorem sturmRealClosed_no_eigenvector_off_Gegenbauer_sequence
    (lam : ℝ) (hlam : 0 < lam) (μ : ℝ)
    (hμ : ∀ n : ℕ, μ ≠ -(n : ℝ) * ((n : ℝ) + 2 * lam))
    (x : (sturmRealPartialOperator lam hlam).closure.domain)
    (hx : (sturmRealPartialOperator lam hlam).closure x =
      μ • (x : SturmH lam)) :
    (x : SturmH lam) = 0 := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  apply b.repr.injective
  ext n
  have hdiag :=
    sturmRealClosed_monicHilbert_diagonal_action
      lam 1 hlam (by norm_num) x n
  rw [hx] at hdiag
  change (b.repr (μ • (x : SturmH lam))) n =
    (-(n : ℝ) * ((n : ℝ) + 2 * lam)) *
      (b.repr (x : SturmH lam)) n at hdiag
  rw [map_smul] at hdiag
  change μ * (b.repr (x : SturmH lam)) n =
    (-(n : ℝ) * ((n : ℝ) + 2 * lam)) *
      (b.repr (x : SturmH lam)) n at hdiag
  have hw :
      μ - (-(n : ℝ) * ((n : ℝ) + 2 * lam)) ≠ 0 :=
    sub_ne_zero.mpr (hμ n)
  have hz :
      (μ - (-(n : ℝ) * ((n : ℝ) + 2 * lam))) *
        (b.repr (x : SturmH lam)) n = 0 := by
    calc
      _ = μ * (b.repr (x : SturmH lam)) n -
          (-(n : ℝ) * ((n : ℝ) + 2 * lam)) *
            (b.repr (x : SturmH lam)) n := by ring
      _ = 0 := sub_eq_zero.mpr hdiag
  have hn : (b.repr (x : SturmH lam)) n = 0 :=
    (mul_eq_zero.mp hz).resolve_left hw
  simpa using hn

/-- Every eigenvalue admitting a nonzero closed-domain eigenvector
must be one of the explicitly computed Gegenbauer eigenvalues. -/
theorem sturmRealClosed_eigenvalue_in_Gegenbauer_sequence
    (lam : ℝ) (hlam : 0 < lam) (μ : ℝ)
    (x : (sturmRealPartialOperator lam hlam).closure.domain)
    (hnz : (x : SturmH lam) ≠ 0)
    (hx : (sturmRealPartialOperator lam hlam).closure x =
      μ • (x : SturmH lam)) :
    ∃ n : ℕ, μ = -(n : ℝ) * ((n : ℝ) + 2 * lam) := by
  by_contra hn
  have hμ : ∀ n : ℕ, μ ≠ -(n : ℝ) * ((n : ℝ) + 2 * lam) := by
    intro n heq
    exact hn ⟨n, heq⟩
  exact hnz
    (sturmRealClosed_no_eigenvector_off_Gegenbauer_sequence
      lam hlam μ hμ x hx)

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_no_eigenvector_off_Gegenbauer_sequence
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_eigenvalue_in_Gegenbauer_sequence

end GegenbauerFock.Ultraspherical
