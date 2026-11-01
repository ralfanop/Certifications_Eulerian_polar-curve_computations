import GegenbauerFock.UltrasphericalSturmLiouvilleExactGegenbauerSpectralClosure

/-!
# The zero eigenspace of the closed ultraspherical Sturm operator

The complete normalized Gegenbauer Hilbert basis and the exact diagonal
representation identify the nullspace of the *genuine canonical closed*
Sturm operator: a domain vector is in its kernel precisely when every
strictly positive-degree Gegenbauer Fourier coefficient vanishes.
No auxiliary operator or hypothesized basis is used.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The true closed Sturm operator annihilates exactly those domain
vectors whose positive-degree Gegenbauer coefficients all vanish. -/
theorem sturmRealClosed_kernel_iff_monicHilbert_positive_coeff_zero
    (lam : ℝ) (hlam : 0 < lam)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    (sturmRealPartialOperator lam hlam).closure x = 0 ↔
      ∀ n : ℕ, n ≠ 0 →
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
          (x : SturmH lam) n = 0 := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let A := (sturmRealPartialOperator lam hlam).closure
  have hdiag (n : ℕ) :
      (b.repr (A x)) n =
        (-(n : ℝ) * ((n : ℝ) + 2 * lam)) *
          (b.repr (x : SturmH lam)) n :=
    (sturmRealClosed_eq_exact_monicGegenbauer_spectral_realization
      lam hlam).2 x n
  constructor
  · intro hx n hn
    have hnpositive : (0 : ℝ) < (n : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hfactor : -(n : ℝ) * ((n : ℝ) + 2 * lam) ≠ 0 := by
      apply mul_ne_zero
      · exact neg_ne_zero.mpr (ne_of_gt hnpositive)
      · have hsum : 0 < (n : ℝ) + 2 * lam := by positivity
        exact ne_of_gt hsum
    have hcoord := hdiag n
    rw [hx, map_zero] at hcoord
    exact (mul_eq_zero.mp hcoord.symm).resolve_left hfactor
  · intro hcoeff
    apply (b.repr).injective
    ext n
    change (b.repr (A x)) n = (b.repr (0 : SturmH lam)) n
    rw [map_zero]
    rw [hdiag n]
    by_cases hn : n = 0
    · subst n
      simp
    · rw [hcoeff n hn, mul_zero]
      simp

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_kernel_iff_monicHilbert_positive_coeff_zero

end GegenbauerFock.Ultraspherical
