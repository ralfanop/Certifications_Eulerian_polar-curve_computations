import UniformLanczos.Rate514Assembly
import UniformLanczos.Theorem59
import Mathlib

/-!
# Manuscript 12, Theorem 5.14: actual coefficients and a compact-uniform bridge

Unlike `Rate514Assembly.theorem_5_14_conclusion`, the final original rate is
NOT an assumption here. The squared central gap is derived directly from
`Rate514Assembly.rate_assembly` after defining the actual bond sequences
a_m = sqrt(betaM M m)/M, b_m = xi(m/M)/2 and their windowed hybrid.

The one remaining interface is explicitly named `LocalOperatorCertificate`:
its fields assert the positivity, decay, residual equation and hybrid residual
bounds for the actual difference sequence, which should follow from the
published functional-calculus inputs plus the original residual estimates.
The functions f(J(u)) and B_{km} are not yet constructed in Lean. Therefore
this theorem is a rigorous *conditional* compact-uniform bridge, not an
unconditional formalisation of the manuscript's Theorem 5.14.

No sorry, new axioms, or additional assumptions of the desired rate.
-/

namespace UniformLanczos.Rate514ConcreteBridge

open Finset UniformLanczos.Rate514
open UniformLanczos.Rate514Assembly
open UniformLanczos.Theorem59

/-- Actual Jacobi bond, zero-extended to the nonpositive indices. -/
noncomputable def actualBond (M : ℕ) (m : ℤ) : ℝ :=
  if 0 < m then Real.sqrt (betaM M m.toNat) / (M : ℝ) else 0

/-- Limiting-profile bond, also zero-extended to nonpositive indices. -/
noncomputable def profileBond (M : ℕ) (m : ℤ) : ℝ :=
  if 0 < m then Profile.ξ ((m.toNat : ℝ) / (M : ℝ)) / 2 else 0

/-- Hybrid of the actual and limiting bonds: profile within W, actual outside W. -/
noncomputable def hybridBond (M : ℕ) (j : ℤ) (L : ℕ) (m : ℤ) : ℝ :=
  if m ∈ Finset.Icc (j - L) (j + L) then profileBond M m else actualBond M m

/-- Actual finite-window bond difference, supported on W. -/
noncomputable def actualDifference (M : ℕ) (j : ℤ) (L : ℕ) (m : ℤ) : ℝ :=
  actualBond M m - hybridBond M j L m

theorem actualDifference_outside (M : ℕ) (j : ℤ) (L : ℕ) {m : ℤ}
    (hm : m ∉ Finset.Icc (j - L) (j + L)) :
    actualDifference M j L m = 0 := by
  simp [actualDifference, hybridBond, hm]

/-- The *centre* of the difference is the literal coefficient gap printed
in (160), not an arbitrary real sequence or an assumed squared rate. -/
theorem actualDifference_center {M j L : ℕ} (hj : 0 < j) :
    actualDifference M (j : ℤ) L (j : ℤ) =
      Real.sqrt (betaM M j) / (M : ℝ) -
        Profile.ξ ((j : ℝ) / (M : ℝ)) / 2 := by
  have hjmem : (j : ℤ) ∈
      Finset.Icc ((j : ℤ) - (L : ℤ)) ((j : ℤ) + (L : ℤ)) := by
    simp only [Finset.mem_Icc]
    omega
  have hjpos : (0 : ℤ) < (j : ℤ) := by exact_mod_cast hj
  simp [actualDifference, hybridBond, actualBond, profileBond, hjmem, hjpos, hj]

/-- Exact uniform constant obtained from the already kernel-verified
weighted strong monotonicity/energy inequality. -/
noncomputable def rateConstant (ε Ch c μ₀ : ℝ) : ℝ :=
  1 + |4 / μ₀ ^ 2 *
    (2 * Ch ^ 2 * (Ωε ε + 8 * Z2 / (ε ^ 2 * c ^ 2)))|

theorem rateConstant_pos (ε Ch c μ₀ : ℝ) : 0 < rateConstant ε Ch c μ₀ := by
  unfold rateConstant
  have ha := abs_nonneg (4 / μ₀ ^ 2 *
    (2 * Ch ^ 2 * (Ωε ε + 8 * Z2 / (ε ^ 2 * c ^ 2))))
  linarith

/-- The data that remain to be identified with the actual Jacobi spectral
calculus. The discrepancy `actualDifference` is already the genuine betaM /
Profile.xi discrepancy; in particular, NO pointwise or squared rate is a field. -/
structure LocalOperatorCertificate (M j L : ℕ) (ε Ch c μ₀ CB : ℝ) where
  B : ℤ → ℤ → ℝ
  h : ℤ → ℝ
  μ : ℤ → ℝ
  L_two : 2 ≤ L
  L_linear : c * (M : ℝ) ≤ (L : ℝ)
  symmetric : ∀ k ∈ Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L),
    ∀ m ∈ Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L), B k m = B m k
  positive : ∀ x : ℤ → ℝ,
    0 ≤ ∑ k ∈ Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L),
      ∑ m ∈ Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L),
        B k m * x k * x m
  decay : ∀ k m : ℤ,
    |B k m| ≤ CB * ((1 + |(k : ℝ) - (m : ℝ)|) ^ 5)⁻¹
  mu_lower : ∀ k ∈ Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L),
    μ₀ ≤ μ k
  residual_identity : ∀ k ∈ Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L),
    h k =
      ∑ m ∈ Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L),
        B k m * actualDifference M (j : ℤ) L m +
          μ k * actualDifference M (j : ℤ) L k
  residual_decay : ∀ k ∈ Finset.Icc ((j : ℤ) - L) ((j : ℤ) + L),
    |h k| ≤ Ch * (1 / (M : ℝ) +
      ((1 + Rate514.Dist L (j : ℤ) k) ^ 3)⁻¹)

/-- MAIN NEW BRIDGE: both inequalities of (160) for the ACTUAL betaM and xi
are derived from the weighted residual/energy machinery, without assuming the
central quadratic rate. Here the explicit operator-certificate fields are
the remaining analytic obligation. -/
theorem actual_rate_from_operator_certificate {M j L : ℕ} (hM : 0 < M) (hj : 0 < j)
    {ε Ch c μ₀ CB : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 < c)
    (hμ₀ : 0 < μ₀) (hCB : 0 ≤ CB)
    (hsmall : ε ^ 2 * (CB * Z3) ≤ μ₀)
    (hβ : 0 ≤ betaM M j)
    (hupper : Real.sqrt (betaM M j) / (M : ℝ) ≤ 1 / 2)
    (w : LocalOperatorCertificate M j L ε Ch c μ₀ CB) :
    |betaM M j / (M : ℝ) ^ 2 - Profile.F ((j : ℝ) / (M : ℝ))| ≤
        rateConstant ε Ch c μ₀ / (M : ℝ) ∧
      |Real.sqrt (betaM M j) / (M : ℝ) -
        Profile.ξ ((j : ℝ) / (M : ℝ)) / 2| ≤
        rateConstant ε Ch c μ₀ / (M : ℝ) := by
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have ht : 0 < (j : ℝ) / (M : ℝ) := div_pos (by exact_mod_cast hj) hMr
  let A : ℝ := 4 / μ₀ ^ 2 *
    (2 * Ch ^ 2 * (Ωε ε + 8 * Z2 / (ε ^ 2 * c ^ 2)))
  have hsq := Rate514Assembly.rate_assembly
    (j : ℤ) L w.L_two hε hε1 hMr hc w.L_linear hμ₀ hCB
    w.B (actualDifference M (j : ℤ) L) w.h w.μ
    w.symmetric w.positive w.decay w.mu_lower w.residual_identity
    hsmall w.residual_decay
  have hsqA : (actualDifference M (j : ℤ) L (j : ℤ)) ^ 2 ≤
      A / (M : ℝ) ^ 2 := by
    dsimp [A]
    convert hsq using 1 <;> ring
  have hCA : A ≤ (rateConstant ε Ch c μ₀) ^ 2 := by
    change A ≤ (1 + |A|) ^ 2
    nlinarith [le_abs_self A, abs_nonneg A, sq_nonneg (|A|)]
  have hd : (Real.sqrt (betaM M j) / (M : ℝ) -
      Profile.ξ ((j : ℝ) / (M : ℝ)) / 2) ^ 2 ≤
      (rateConstant ε Ch c μ₀) ^ 2 / (M : ℝ) ^ 2 := by
    rw [← actualDifference_center hj]
    exact hsqA.trans (div_le_div_of_nonneg_right hCA (by positivity))
  have hconclusion :=
    Rate514Assembly.theorem_5_14_conclusion hM hβ ht hupper
      (rateConstant_pos ε Ch c μ₀).le hd
  exact ⟨hconclusion.2, hconclusion.1⟩

/-- The full COMPACT-UNIFORM quantified form with one constant independent of
both M and j, conditional on a *uniform family* of genuine operator certificates.
It does not assume any squared or pointwise rate. -/
theorem compact_uniform_rate_from_operator_certificates {t₁ t₂ : ℝ}
    (ht₁ : 0 < t₁) (ht₂ : t₁ ≤ t₂)
    {ε Ch c μ₀ CB : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 < c)
    (hμ₀ : 0 < μ₀) (hCB : 0 ≤ CB)
    (hsmall : ε ^ 2 * (CB * Z3) ≤ μ₀)
    (M₀ : ℕ) (hM₀ : 1 ≤ M₀)
    (hβ : ∀ M j : ℕ, M₀ ≤ M →
      (j : ℝ) / (M : ℝ) ∈ Set.Icc t₁ t₂ → 0 ≤ betaM M j)
    (hupper : ∀ M j : ℕ, M₀ ≤ M →
      (j : ℝ) / (M : ℝ) ∈ Set.Icc t₁ t₂ →
      Real.sqrt (betaM M j) / (M : ℝ) ≤ 1 / 2)
    (hcert : ∀ M j : ℕ, M₀ ≤ M →
      (j : ℝ) / (M : ℝ) ∈ Set.Icc t₁ t₂ →
      Σ L : ℕ, LocalOperatorCertificate M j L ε Ch c μ₀ CB) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ℕ, M₀ ≤ M → ∀ j : ℕ,
        (j : ℝ) / (M : ℝ) ∈ Set.Icc t₁ t₂ →
          |betaM M j / (M : ℝ) ^ 2 -
            Profile.F ((j : ℝ) / (M : ℝ))| ≤ C / (M : ℝ) ∧
          |Real.sqrt (betaM M j) / (M : ℝ) -
            Profile.ξ ((j : ℝ) / (M : ℝ)) / 2| ≤ C / (M : ℝ) := by
  refine ⟨rateConstant ε Ch c μ₀, rateConstant_pos ε Ch c μ₀, ?_⟩
  intro M hM j hj
  have hMn : 0 < M := by omega
  have hJ : 0 < j := by
    by_contra hn
    have hz : j = 0 := Nat.eq_zero_of_not_pos hn
    have hp : (0 : ℝ) < (j : ℝ) / (M : ℝ) := lt_of_lt_of_le ht₁ hj.1
    simp [hz] at hp
  obtain ⟨L, w⟩ := hcert M j hM hj
  exact actual_rate_from_operator_certificate hMn hJ hε hε1 hc hμ₀ hCB
    hsmall (hβ M j hM hj) (hupper M j hM hj) w

end UniformLanczos.Rate514ConcreteBridge

#print axioms UniformLanczos.Rate514ConcreteBridge.actualDifference_outside
#print axioms UniformLanczos.Rate514ConcreteBridge.actualDifference_center
#print axioms UniformLanczos.Rate514ConcreteBridge.rateConstant_pos
#print axioms UniformLanczos.Rate514ConcreteBridge.actual_rate_from_operator_certificate
#print axioms UniformLanczos.Rate514ConcreteBridge.compact_uniform_rate_from_operator_certificates
