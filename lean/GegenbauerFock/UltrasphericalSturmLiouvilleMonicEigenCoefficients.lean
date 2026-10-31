import GegenbauerFock.UltrasphericalSturmLiouvilleEigenvalueOrder
import Mathlib

/-!
# V007 — finite monic Gegenbauer coefficients: all-degree construction

For every λ>0 and degree n, define the finite scalar recurrence

  a(n,0)=1,
  a(n,k+1)=-[(n-2k)(n-2k-1)/(4(k+1)(n-k-1+λ))] a(n,k).

The finite polynomial ∑_{k≤n/2} a(n,k) X^(n-2k) is an
explicit monic Gegenbauer eigenpolynomial CANDIDATE.
We certify the essential scalar cancellation for the Sturm
differential identity, but do NOT claim the full polynomial
eigenrelation until the finite-sum shift is itself proved.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open Polynomial

/-- Recursive coefficients of the monic degree-n Gegenbauer polynomial. -/
noncomputable def sturmMonicCoeff (lam : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => 1
  | k+1 =>
    -((((n : ℝ) - 2 * (k : ℝ)) *
        ((n : ℝ) - 2 * (k : ℝ) - 1) *
          sturmMonicCoeff lam n k) /
       (4 * (((k+1 : ℕ) : ℝ)) *
        ((n : ℝ) - (k : ℝ) - 1 + lam)))

@[simp] theorem sturmMonicCoeff_zero (lam : ℝ) (n : ℕ) :
    sturmMonicCoeff lam n 0 = 1 := rfl

/-- Every denominator used in the finite recurrence is strictly
positive on its actual range; no Gamma-function assumptions. -/
theorem sturmMonicCoeff_den_pos
    (lam : ℝ) (hlam : 0 < lam) (n k : ℕ)
    (hk : 2 * (k+1) ≤ n) :
    0 < (4 : ℝ) * (((k+1 : ℕ) : ℝ)) *
      ((n : ℝ) - (k : ℝ) - 1 + lam) := by
  have hreal : (2 : ℝ) * ((k : ℝ) + 1) ≤ (n : ℝ) := by
    exact_mod_cast hk
  have hknonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hsucc : 0 < (((k+1 : ℕ) : ℝ)) := by positivity
  have hterm : 0 < (n : ℝ) - (k : ℝ) - 1 + lam := by
    nlinarith
  positivity

/-- Exact two-step coefficient cancellation used in
L_lambda G_n = -n(n+2λ) G_n. -/
theorem sturmMonicCoeff_cancellation
    (lam : ℝ) (hlam : 0 < lam) (n k : ℕ)
    (hk : 2 * (k+1) ≤ n) :
    (4 * (((k+1 : ℕ) : ℝ)) *
        ((n : ℝ) - (k : ℝ) - 1 + lam)) *
      sturmMonicCoeff lam n (k+1) +
      ((n : ℝ) - 2 * (k : ℝ)) *
        ((n : ℝ) - 2 * (k : ℝ) - 1) *
          sturmMonicCoeff lam n k = 0 := by
  have hden := sturmMonicCoeff_den_pos lam hlam n k hk
  have hne : (4 : ℝ) * (((k+1 : ℕ) : ℝ)) *
      ((n : ℝ) - (k : ℝ) - 1 + lam) ≠ 0 := ne_of_gt hden
  rw [sturmMonicCoeff]
  field_simp [hne]
  ring

/-- Explicit finite polynomial, monic by construction; the all-degree
differential eigenrelation is the next separate verification goal. -/
noncomputable def sturmMonicEigenCandidate (lam : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n/2+1),
    C (sturmMonicCoeff lam n k) * X^(n-2*k)

#print axioms GegenbauerFock.Ultraspherical.sturmMonicCoeff_zero
#print axioms GegenbauerFock.Ultraspherical.sturmMonicCoeff_den_pos
#print axioms GegenbauerFock.Ultraspherical.sturmMonicCoeff_cancellation

end GegenbauerFock.Ultraspherical
