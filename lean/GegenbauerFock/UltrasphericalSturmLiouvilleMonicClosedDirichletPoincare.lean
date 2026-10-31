import GegenbauerFock.UltrasphericalSturmLiouvilleMonicClosedPoincare

/-!
# V007 — exact closed Sturm Dirichlet energy and sharp Poincare inequality

The genuine closed real ultraspherical Sturm operator A has
Fourier-Gegenbauer multiplier -n(n+2λ). By the real Hilbert-basis
Parseval identity for *two* vectors, its full operator quadratic form
is the negative of the spectral Dirichlet energy:

  -⟪A x, x⟫ = ∑' n, n(n+2λ) |x_n|².

This identity holds for every x in the actual closed differential
operator domain, not only polynomial functions. In particular, for
zero-constant-mode vectors:

  (1+2λ) ‖x‖² ≤ -⟪A x,x⟫.

The optimal gap comes from the existing certified degree-one
nonzero genuine eigenvector.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The negative Dirichlet quadratic form of the *canonical closed*
Sturm differential operator is exactly the spectral Gegenbauer
energy, with convergence in real numbers. -/
theorem sturmMonic_realL2_closed_Dirichlet_energy_eq
    (lam : ℝ) (hlam : 0 < lam)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    (∑' n : ℕ, ((n : ℝ) * ((n : ℝ) + 2 * lam)) *
      ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (x : SturmH lam) n) ^ 2) =
      -inner ℝ ((sturmRealPartialOperator lam hlam).closure x)
        (x : SturmH lam) := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let A := (sturmRealPartialOperator lam hlam).closure
  have hdiag (n : ℕ) :
      (b.repr (A x)) n =
        (-(n : ℝ) * ((n : ℝ) + 2 * lam)) *
          (b.repr (x : SturmH lam)) n :=
    (sturmRealClosed_eq_exact_monicGegenbauer_spectral_realization
      lam hlam).2 x n
  have hterm (n : ℕ) :
      inner ℝ (A x) (b n) * inner ℝ (b n) (x : SturmH lam) =
      -(((n : ℝ) * ((n : ℝ) + 2 * lam)) *
        ((b.repr (x : SturmH lam)) n) ^ 2) := by
    rw [real_inner_comm (b n) (x : SturmH lam)]
    rw [← HilbertBasis.repr_apply_apply b (A x) n]
    rw [← HilbertBasis.repr_apply_apply b (x : SturmH lam) n]
    rw [hdiag n]
    ring
  have hsum :
      (∑' n : ℕ,
        -(((n : ℝ) * ((n : ℝ) + 2 * lam)) *
          ((b.repr (x : SturmH lam)) n) ^ 2)) =
        inner ℝ (A x) (x : SturmH lam) := by
    calc
      _ = ∑' n : ℕ,
        inner ℝ (A x) (b n) * inner ℝ (b n) (x : SturmH lam) :=
          tsum_congr (fun n => (hterm n).symm)
      _ = inner ℝ (A x) (x : SturmH lam) :=
          b.tsum_inner_mul_inner (A x) (x : SturmH lam)
  rw [tsum_neg] at hsum
  change -(∑' n : ℕ,
      ((n : ℝ) * ((n : ℝ) + 2 * lam)) *
        ((b.repr (x : SturmH lam)) n) ^ 2) =
    inner ℝ (A x) (x : SturmH lam) at hsum
  linarith

/-- Sharp operator-form spectral-gap/Poincare inequality for each
zero-constant-mode vector in the full closed Sturm graph domain. -/
theorem sturmMonic_realL2_closed_Dirichlet_poincare
    (lam : ℝ) (hlam : 0 < lam)
    (x : (sturmRealPartialOperator lam hlam).closure.domain)
    (hzero :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
        (x : SturmH lam) 0 = 0) :
    (1 + 2 * lam) * ‖(x : SturmH lam)‖ ^ 2 ≤
      -inner ℝ ((sturmRealPartialOperator lam hlam).closure x)
        (x : SturmH lam) := by
  have hp := sturmMonic_realL2_closed_spectral_poincare lam hlam x hzero
  rw [sturmMonic_realL2_closed_Dirichlet_energy_eq lam hlam x] at hp
  exact hp

#print axioms GegenbauerFock.Ultraspherical.sturmMonic_realL2_closed_Dirichlet_energy_eq
#print axioms GegenbauerFock.Ultraspherical.sturmMonic_realL2_closed_Dirichlet_poincare

end GegenbauerFock.Ultraspherical
