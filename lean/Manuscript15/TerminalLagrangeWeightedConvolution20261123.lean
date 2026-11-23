import Manuscript15.TerminalLagrangeFiniteCoefficients20261123
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

/-!
# M15 §6.2: weighted convolution without substitution of Laurent residues

After the verified degree-shift/diagonal identities of PR #524, this is a
separate, unconditional identity that makes the candidate coefficients of
closed Lagrange--Bürmann compatible with the triangular recurrence.

For ψ an arbitrary real formal power series, m > 0 and k ≥ 0:
  (m+k) * [u^(m-1)]((ψ^k)' * ψ^m)
    = k*m * [u^m] ψ^(m+k).
The left side is a genuinely *finite* convolution of coefficients of ψ^k
and ψ^m; the equality is a consequence of the derivative-power identity.

This by itself is not the fixed-point coefficient transfer theorem. The
subsequent step is induction on n in H = X * ψ(H), using this identity and
the certified triangularity of PRs #491 and #524.
-/

namespace Manuscript15.TerminalLagrangeWeighted

open PowerSeries

abbrev P := PowerSeries ℝ

/-- The weighted derivative-power identity behind finite Lagrange inversion.
This is valid for all natural exponents, including k = 0. -/
theorem weighted_derivative (ψ : P) (m k : ℕ) :
    ((m + k : ℕ) : P) *
        ((PowerSeries.derivative (R := ℝ)) (ψ ^ k) * ψ ^ m) =
      (k : P) * ((PowerSeries.derivative (R := ℝ)) (ψ ^ (m + k))) := by
  by_cases hk : k = 0
  · subst k
    simp
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have he : m + k - 1 = m + (k - 1) := by omega
  rw [PowerSeries.derivative_pow, PowerSeries.derivative_pow, he, pow_add]
  push_cast
  ring

/-- Coefficient-level identity: no infinite summation is needed. -/
theorem weighted_coefficient (ψ : P) (m k : ℕ) (hm : 0 < m) :
    ((m + k : ℕ) : ℝ) *
        PowerSeries.coeff (m - 1)
          (((PowerSeries.derivative (R := ℝ)) (ψ ^ k)) * ψ ^ m) =
      ((k : ℝ) * (m : ℝ)) *
        PowerSeries.coeff m (ψ ^ (m + k)) := by
  have h := congrArg (PowerSeries.coeff (m - 1))
    (weighted_derivative ψ m k)
  simp only [PowerSeries.coeff_natCast_mul,
    PowerSeries.coeff_derivative] at h
  have hm' : m - 1 + 1 = m := by omega
  rw [hm'] at h
  have hc : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hm'
  push_cast at h
  rw [hc] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc, Nat.cast_add] using h

/-- The weighted finite Cauchy convolution, indexed by the antidiagonal.
This is the key identity required to prove that Lagrange--Bürmann's
candidate coefficients satisfy the inverse-series recurrence. -/
theorem weighted_finite_convolution (ψ : P) (m k : ℕ) (hm : 0 < m) :
    ((m + k : ℕ) : ℝ) *
        (∑ p ∈ Finset.antidiagonal (m - 1),
          (PowerSeries.coeff (p.1 + 1) (ψ ^ k) * ((p.1 + 1 : ℕ) : ℝ)) *
            PowerSeries.coeff p.2 (ψ ^ m)) =
      ((k : ℝ) * (m : ℝ)) *
        PowerSeries.coeff m (ψ ^ (m + k)) := by
  simpa only [PowerSeries.coeff_mul, PowerSeries.coeff_derivative,
    Nat.cast_add, Nat.cast_one, mul_assoc]
    using weighted_coefficient ψ m k hm


/-- Substitution has an exact *finite* coefficient expansion when the
inner series H has zero constant term. The bound j ≤ m follows from
H = X * ψ(H), without any analytic convergence assumption. -/
theorem fixedpoint_subst_finite (H ψ : P)
    (hH : H = PowerSeries.X * PowerSeries.subst H ψ)
    (m k : ℕ) :
    PowerSeries.coeff m ((PowerSeries.subst H ψ) ^ k) =
      ∑ j ∈ Finset.range (m + 1),
        PowerSeries.coeff j (ψ ^ k) * PowerSeries.coeff m (H ^ j) := by
  have h0 := Manuscript15.TerminalLagrangeFinite.fixedpoint_constantCoeff_zero H ψ hH
  have hs : PowerSeries.HasSubst H :=
    PowerSeries.HasSubst.of_constantCoeff_zero' h0
  rw [← PowerSeries.subst_pow hs ψ k, PowerSeries.coeff_subst' hs]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (m + 1))]
  · simp only [smul_eq_mul]
  · intro j hj
    by_contra hj'
    have hjgt : m < j := by
      have hn : ¬ j < m + 1 := by
        intro hlt
        exact hj' (Finset.mem_range.mpr hlt)
      omega
    have hz : PowerSeries.coeff m (H ^ j) = 0 :=
      Manuscript15.TerminalLagrangeFinite.coeff_factored_below
        H (PowerSeries.subst H ψ) hH m j hjgt
    have hzero :
        PowerSeries.coeff j (ψ ^ k) • PowerSeries.coeff m (H ^ j) = 0 := by
      simp [hz]
    exact (Function.mem_support.mp hj) hzero

/-- A true *finite* triangular recurrence for powers of the implicit
solution H = X * ψ(H), valid uniformly in m and k. -/
theorem fixedpoint_power_finite_sum (H ψ : P)
    (hH : H = PowerSeries.X * PowerSeries.subst H ψ)
    (m k : ℕ) :
    PowerSeries.coeff (m + k) (H ^ k) =
      ∑ j ∈ Finset.range (m + 1),
        PowerSeries.coeff j (ψ ^ k) * PowerSeries.coeff m (H ^ j) := by
  rw [Manuscript15.TerminalLagrangeFinite.fixedpoint_coeff_shift H ψ hH m k]
  exact fixedpoint_subst_finite H ψ hH m k

#print axioms Manuscript15.TerminalLagrangeWeighted.fixedpoint_subst_finite
#print axioms Manuscript15.TerminalLagrangeWeighted.fixedpoint_power_finite_sum


/-- The same weighted convolution indexed directly by a finite range
j = 0,...,m. This is the form consumed by strong induction on the
coefficients of H = X * ψ(H). -/
theorem weighted_range_convolution (ψ : P) (m k : ℕ) (hm : 0 < m) :
    ((m + k : ℕ) : ℝ) *
        (∑ j ∈ Finset.range (m + 1),
          PowerSeries.coeff j (ψ ^ k) *
            ((j : ℝ) * PowerSeries.coeff (m - j) (ψ ^ m))) =
      ((k : ℝ) * (m : ℝ)) *
        PowerSeries.coeff m (ψ ^ (m + k)) := by
  have hr :
      (∑ j ∈ Finset.range (m + 1),
        PowerSeries.coeff j (ψ ^ k) *
          ((j : ℝ) * PowerSeries.coeff (m - j) (ψ ^ m))) =
      (∑ p ∈ Finset.antidiagonal (m - 1),
        (PowerSeries.coeff (p.1 + 1) (ψ ^ k) * ((p.1 + 1 : ℕ) : ℝ)) *
          PowerSeries.coeff p.2 (ψ ^ m)) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := fun a b =>
      (PowerSeries.coeff (a + 1) (ψ ^ k) * ((a + 1 : ℕ) : ℝ)) *
        PowerSeries.coeff b (ψ ^ m))]
    have hm' : (m - 1).succ = m := by omega
    rw [hm']
    apply Finset.sum_congr rfl
    intro j _
    have hsub : m - (j + 1) = m - 1 - j := by omega
    rw [hsub]
    ring
  rw [hr]
  exact weighted_finite_convolution ψ m k hm

#print axioms Manuscript15.TerminalLagrangeWeighted.weighted_range_convolution


/-- The *all-order closed monomial Lagrange--Bürmann identity*, proved
by strong induction on n from finite coefficient substitution, the
fixed-point recurrence and the weighted Cauchy identity. No residue
substitution or analytic convergence is assumed. -/
theorem closed_monomial_coeff (H ψ : P)
    (hH : H = PowerSeries.X * PowerSeries.subst H ψ)
    (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    (n : ℝ) * PowerSeries.coeff n (H ^ k) =
      (k : ℝ) * PowerSeries.coeff (n - k) (ψ ^ n) := by
  have hstrong : ∀ n : ℕ, ∀ k : ℕ, 0 < k → k ≤ n →
      (n : ℝ) * PowerSeries.coeff n (H ^ k) =
        (k : ℝ) * PowerSeries.coeff (n - k) (ψ ^ n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k hk hkn
      by_cases heq : k = n
      · subst n
        rw [Manuscript15.TerminalLagrangeFinite.fixedpoint_diagonal H ψ hH k]
        simp
      · have hklt : k < n := by omega
        let m : ℕ := n - k
        have hm : 0 < m := by dsimp [m]; omega
        have hm_lt : m < n := by dsimp [m]; omega
        have hnmk : m + k = n := by dsimp [m]; omega
        have hsub : n - k = m := by rfl
        have hcoeff :=
          Manuscript15.TerminalLagrangeWeighted.fixedpoint_power_finite_sum
            H ψ hH m k
        have hrec :
            (m : ℝ) * PowerSeries.coeff (m + k) (H ^ k) =
              ∑ j ∈ Finset.range (m + 1),
                PowerSeries.coeff j (ψ ^ k) *
                  ((j : ℝ) * PowerSeries.coeff (m - j) (ψ ^ m)) := by
          rw [hcoeff, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hjzero : j = 0
          · subst j
            have hmne : m ≠ 0 := by omega
            simp [hmne]
          · have hjle : j ≤ m := by
              have hlt := Finset.mem_range.mp hj
              omega
            have hjpos : 0 < j := Nat.pos_of_ne_zero hjzero
            have hih := ih m hm_lt j hjpos hjle
            calc
              (m : ℝ) *
                  (PowerSeries.coeff j (ψ ^ k) * PowerSeries.coeff m (H ^ j)) =
                    PowerSeries.coeff j (ψ ^ k) *
                      ((m : ℝ) * PowerSeries.coeff m (H ^ j)) := by ring
              _ = PowerSeries.coeff j (ψ ^ k) *
                    ((j : ℝ) * PowerSeries.coeff (m - j) (ψ ^ m)) := by rw [hih]
        have hmain :
            ((m + k : ℕ) : ℝ) *
                ((m : ℝ) * PowerSeries.coeff (m + k) (H ^ k)) =
              ((k : ℝ) * (m : ℝ)) *
                PowerSeries.coeff m (ψ ^ (m + k)) := by
          rw [hrec]
          exact weighted_range_convolution ψ m k hm
        have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
        have hcancel :
            ((m + k : ℕ) : ℝ) * PowerSeries.coeff (m + k) (H ^ k) =
              (k : ℝ) * PowerSeries.coeff m (ψ ^ (m + k)) := by
          have h2 :
              (m : ℝ) *
                  (((m + k : ℕ) : ℝ) * PowerSeries.coeff (m + k) (H ^ k)) =
                (m : ℝ) *
                  ((k : ℝ) * PowerSeries.coeff m (ψ ^ (m + k))) := by
            calc
              _ = ((m + k : ℕ) : ℝ) *
                    ((m : ℝ) * PowerSeries.coeff (m + k) (H ^ k)) := by ring
              _ = ((k : ℝ) * (m : ℝ)) *
                    PowerSeries.coeff m (ψ ^ (m + k)) := hmain
              _ = (m : ℝ) *
                    ((k : ℝ) * PowerSeries.coeff m (ψ ^ (m + k))) := by ring
          exact mul_left_cancel₀ hmne h2
        simpa only [hnmk, hsub] using hcancel
  exact hstrong n k hk hkn

#print axioms Manuscript15.TerminalLagrangeWeighted.closed_monomial_coeff


/-- Coefficients of a general outer series after substitution are finite
when H has order at least one. -/
theorem general_subst_finite (H ψ G : P)
    (hH : H = PowerSeries.X * PowerSeries.subst H ψ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst H G) =
      ∑ k ∈ Finset.range (n + 1),
        PowerSeries.coeff k G * PowerSeries.coeff n (H ^ k) := by
  have h0 := Manuscript15.TerminalLagrangeFinite.fixedpoint_constantCoeff_zero H ψ hH
  have hs : PowerSeries.HasSubst H :=
    PowerSeries.HasSubst.of_constantCoeff_zero' h0
  rw [PowerSeries.coeff_subst' hs]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · simp only [smul_eq_mul]
  · intro k hk
    by_contra hkn
    have hkgt : n < k := by
      have hnot : ¬ k < n + 1 := by
        intro hlt
        exact hkn (Finset.mem_range.mpr hlt)
      omega
    have hz : PowerSeries.coeff n (H ^ k) = 0 :=
      Manuscript15.TerminalLagrangeFinite.coeff_factored_below
        H (PowerSeries.subst H ψ) hH n k hkgt
    have heq :
        PowerSeries.coeff k G • PowerSeries.coeff n (H ^ k) = 0 := by
      simp [hz]
    exact (Function.mem_support.mp hk) heq

/-- Coefficients of G'Q as a finite derivative-weighted range sum. -/
theorem coeff_derivative_mul_as_range (G Q : P) (n : ℕ) (hn : 0 < n) :
    PowerSeries.coeff (n - 1)
        (((PowerSeries.derivative (R := ℝ)) G) * Q) =
      ∑ k ∈ Finset.range (n + 1),
        ((k : ℝ) * PowerSeries.coeff k G) *
          PowerSeries.coeff (n - k) Q := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := fun a b =>
    PowerSeries.coeff a ((PowerSeries.derivative (R := ℝ)) G) * PowerSeries.coeff b Q)]
  simp_rw [PowerSeries.coeff_derivative]
  have hn' : (n - 1).succ = n := by omega
  rw [hn']
  conv_rhs => rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  have hsub : n - (k + 1) = n - 1 - k := by omega
  rw [hsub]
  ring

/-- Closed Lagrange--Bürmann coefficient identity for any outer formal
power series G and every positive order n. This follows from the
already established monomial identity and finite coefficient substitution. -/
theorem closed_general_coeff (H ψ G : P)
    (hH : H = PowerSeries.X * PowerSeries.subst H ψ)
    (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * PowerSeries.coeff n (PowerSeries.subst H G) =
      PowerSeries.coeff (n - 1)
        (((PowerSeries.derivative (R := ℝ)) G) * ψ ^ n) := by
  rw [general_subst_finite H ψ G hH n, Finset.mul_sum,
    coeff_derivative_mul_as_range G (ψ ^ n) n hn]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkzero : k = 0
  · subst k
    have hnzero : n ≠ 0 := by omega
    simp [hnzero]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
    have hkle : k ≤ n := by
      have hlt := Finset.mem_range.mp hk
      omega
    have hmono := closed_monomial_coeff H ψ hH n k hkpos hkle
    calc
      (n : ℝ) *
          (PowerSeries.coeff k G * PowerSeries.coeff n (H ^ k)) =
        PowerSeries.coeff k G *
          ((n : ℝ) * PowerSeries.coeff n (H ^ k)) := by ring
      _ = PowerSeries.coeff k G *
          ((k : ℝ) * PowerSeries.coeff (n - k) (ψ ^ n)) := by rw [hmono]
      _ = ((k : ℝ) * PowerSeries.coeff k G) *
          PowerSeries.coeff (n - k) (ψ ^ n) := by ring

#print axioms Manuscript15.TerminalLagrangeWeighted.general_subst_finite
#print axioms Manuscript15.TerminalLagrangeWeighted.coeff_derivative_mul_as_range
#print axioms Manuscript15.TerminalLagrangeWeighted.closed_general_coeff

#print axioms Manuscript15.TerminalLagrangeWeighted.weighted_derivative
#print axioms Manuscript15.TerminalLagrangeWeighted.weighted_coefficient
#print axioms Manuscript15.TerminalLagrangeWeighted.weighted_finite_convolution

end Manuscript15.TerminalLagrangeWeighted
