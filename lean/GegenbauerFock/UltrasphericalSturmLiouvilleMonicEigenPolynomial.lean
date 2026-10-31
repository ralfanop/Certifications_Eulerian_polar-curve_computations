import GegenbauerFock.UltrasphericalSturmLiouvilleMonicEigenSum
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicFiniteShift

/-!
# V007 — all-degree explicit monic Gegenbauer Sturm eigenpolynomials

The finite coefficient recurrence and exact triangular monomial rule
yield the unconditionally quantified polynomial eigen-equation

  L_λ G_{n,λ} = -n(n+2λ) G_{n,λ}.

No spectral extension or completeness assumption enters this finite
algebraic proof. The certified monic coefficient cancellation supplies
the only interior terms; parity makes the final lowering term vanish.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open Polynomial

private def monicLowerTerm (lam : ℝ) (n k : ℕ) : ℝ[X] :=
  C (sturmMonicCoeff lam n k) *
    C (((n-2*k : ℕ) : ℝ) * (((n-2*k : ℕ) : ℝ) - 1)) *
      X ^ (n-2*k-2)

private def monicDiagonalTerm (lam : ℝ) (n k : ℕ) : ℝ[X] :=
  (C (sturmMonicCoeff lam n k) *
      C (sturmEigenvalue lam (n-2*k)) -
    C (sturmEigenvalue lam n) *
      C (sturmMonicCoeff lam n k)) * X ^ (n-2*k)

/-- Adjacent monic terms cancel as full REAL POLYNOMIALS, not
only as scalars. This is the finite sum's exact index-shift bridge. -/
private theorem monicLower_add_nextDiagonal
    (lam : ℝ) (hlam : 0 < lam) (n k : ℕ)
    (hk : k < n/2) :
    monicLowerTerm lam n k +
      monicDiagonalTerm lam n (k+1) = 0 := by
  have hstep : 2*(k+1) ≤ n := sturmMonic_step_range n k hk
  have hexp : n - 2*k - 2 = n - 2*(k+1) :=
    sturmMonic_step_exponent n k hk
  have hkn : 2*k ≤ n := by omega
  have hcast : (((n-2*k : ℕ) : ℝ)) =
      (n : ℝ) - 2*(k : ℝ) := by
    rw [Nat.cast_sub hkn]
    push_cast
    ring
  have hscalar :
      (((n-2*k : ℕ) : ℝ) *
        (((n-2*k : ℕ) : ℝ) - 1)) *
          sturmMonicCoeff lam n k +
      (sturmEigenvalue lam (n-2*(k+1)) -
        sturmEigenvalue lam n) *
          sturmMonicCoeff lam n (k+1) = 0 := by
    rw [hcast]
    calc
      _ = (sturmEigenvalue lam (n-2*(k+1)) -
            sturmEigenvalue lam n) *
            sturmMonicCoeff lam n (k+1) +
          ((n : ℝ) - 2*(k : ℝ)) *
            ((n : ℝ) - 2*(k : ℝ) - 1) *
              sturmMonicCoeff lam n k := by ring
      _ = 0 :=
        sturmMonicCoeff_spectral_gap_cancellation
          lam hlam n k hstep
  calc
    monicLowerTerm lam n k + monicDiagonalTerm lam n (k+1) =
        (C (sturmMonicCoeff lam n k) *
          C (((n-2*k : ℕ) : ℝ) *
            (((n-2*k : ℕ) : ℝ) - 1)) +
         C (sturmMonicCoeff lam n (k+1)) *
          C (sturmEigenvalue lam (n-2*(k+1))) -
         C (sturmEigenvalue lam n) *
          C (sturmMonicCoeff lam n (k+1))) *
          X ^ (n-2*(k+1)) := by
      dsimp [monicLowerTerm, monicDiagonalTerm]
      rw [hexp]
      ring
    _ = C ((((n-2*k : ℕ) : ℝ) *
          (((n-2*k : ℕ) : ℝ) - 1)) *
          sturmMonicCoeff lam n k +
         (sturmEigenvalue lam (n-2*(k+1)) -
           sturmEigenvalue lam n) *
             sturmMonicCoeff lam n (k+1)) *
          X ^ (n-2*(k+1)) := by
      simp only [← C_mul, ← C_add, ← C_sub]
      congr 1
      ring
    _ = 0 := by rw [hscalar]; simp

/-- The explicitly constructed monic polynomial satisfies the
Gegenbauer differential eigen-equation for EVERY natural degree n. -/
theorem sturmMonicEigenCandidate_eigen
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    sturmPolynomial lam (sturmMonicEigenCandidate lam n) =
      sturmEigenvalue lam n • sturmMonicEigenCandidate lam n := by
  let E : ℕ → ℝ[X] := monicLowerTerm lam n
  let D : ℕ → ℝ[X] := monicDiagonalTerm lam n
  have hD0 : D 0 = 0 := by
    dsimp [D, monicDiagonalTerm]
    simp
  have hEfinal : E (n/2) = 0 := by
    dsimp [E, monicLowerTerm]
    rw [sturmMonic_last_lower_coeff_zero]
    simp
  have hadj : ∀ k < n/2, E k + D (k+1) = 0 := by
    intro k hk
    exact monicLower_add_nextDiagonal lam hlam n k hk
  have hsum :
      sturmPolynomial lam (sturmMonicEigenCandidate lam n) -
        C (sturmEigenvalue lam n) *
          sturmMonicEigenCandidate lam n =
        ∑ k ∈ Finset.range (n/2+1), (E k + D k) := by
    rw [sturmPolynomial_monicCandidate_as_sum]
    unfold sturmMonicEigenCandidate
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [sturmPolynomial_X_pow_diagonal_lower]
    dsimp [E, D, monicLowerTerm, monicDiagonalTerm]
    ring
  have hzero :
      (∑ k ∈ Finset.range (n/2+1), (E k + D k)) = 0 :=
    sturmFinite_shift_cancellation (n/2) E D hD0 hEfinal hadj
  apply (sub_eq_zero.mp ?_)
  change sturmPolynomial lam (sturmMonicEigenCandidate lam n) -
    C (sturmEigenvalue lam n) * sturmMonicEigenCandidate lam n = 0
  rw [hsum]
  exact hzero

#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_eigen

end GegenbauerFock.Ultraspherical
