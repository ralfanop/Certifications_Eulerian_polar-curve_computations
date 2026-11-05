import GegenbauerFock.UltrasphericalSturmLiouvilleMonicEigenCoefficients

/-!
# V007 — finite telescope underlying all-degree Gegenbauer eigenpolynomials

A finite cancellation lemma in the additive group of real polynomials,
and the precise Nat exponent arithmetic at the parity endpoint.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open Polynomial

/-- A finite boundary-aware telescope: adjacent lowering and
diagonal terms cancel; the initial and final boundary terms vanish.
This works for arbitrary polynomial-valued sequences. -/
theorem sturmFinite_shift_cancellation
    (m : ℕ) (E D : ℕ → ℝ[X])
    (hzero : D 0 = 0)
    (hfinal : E m = 0)
    (hadj : ∀ k < m, E k + D (k+1) = 0) :
    (∑ k ∈ Finset.range (m+1), (E k + D k)) = 0 := by
  have hprefix : ∀ j : ℕ,
      (∀ k < j, E k + D (k+1) = 0) →
      (∑ k ∈ Finset.range (j+1), (E k + D k)) = E j := by
    intro j
    induction j with
    | zero =>
        intro _
        simp [hzero]
    | succ j ih =>
        intro h
        have hprev : ∀ k < j, E k + D (k+1) = 0 := by
          intro k hk
          exact h k (Nat.lt_succ_of_lt hk)
        have hlast : E j + D (j+1) = 0 :=
          h j (Nat.lt_succ_self j)
        calc
          (∑ k ∈ Finset.range ((j+1)+1), (E k + D k)) =
              (∑ k ∈ Finset.range (j+1), (E k + D k)) +
                (E (j+1) + D (j+1)) :=
                  Finset.sum_range_succ _ (j+1)
          _ = E j + (E (j+1) + D (j+1)) := by
                rw [ih hprev]
          _ = (E j + D (j+1)) + E (j+1) := by abel
          _ = E (j+1) := by rw [hlast]; simp
  rw [hprefix m hadj, hfinal]

/-- Natural-number parity leaves degree zero or one at the final
index of the finite Gegenbauer monic sum. -/
theorem sturmMonic_last_degree_eq_zero_or_one (n : ℕ) :
    n - 2*(n/2) = 0 ∨ n - 2*(n/2) = 1 := by
  omega

/-- The lowering scalar of the terminal term is exactly zero,
without an out-of-range negative exponent. -/
theorem sturmMonic_last_lower_coeff_zero (n : ℕ) :
    ((n - 2*(n/2) : ℕ) : ℝ) *
        (((n - 2*(n/2) : ℕ) : ℝ) - 1) = 0 := by
  rcases sturmMonic_last_degree_eq_zero_or_one n with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

/-- An interior index always has at least two powers of X left;
the exponent after differentiation is the next parity index. -/
theorem sturmMonic_step_exponent (n k : ℕ)
    (hk : k < n/2) :
    n - 2*k - 2 = n - 2*(k+1) := by
  omega

/-- For every interior term the monic coefficient cancellation
theorem is available with its exact Nat range hypothesis. -/
theorem sturmMonic_step_range (n k : ℕ) (hk : k < n/2) :
    2*(k+1) ≤ n := by
  omega

#print axioms GegenbauerFock.Ultraspherical.sturmFinite_shift_cancellation
#print axioms GegenbauerFock.Ultraspherical.sturmMonic_last_degree_eq_zero_or_one
#print axioms GegenbauerFock.Ultraspherical.sturmMonic_last_lower_coeff_zero
#print axioms GegenbauerFock.Ultraspherical.sturmMonic_step_exponent
#print axioms GegenbauerFock.Ultraspherical.sturmMonic_step_range

end GegenbauerFock.Ultraspherical
