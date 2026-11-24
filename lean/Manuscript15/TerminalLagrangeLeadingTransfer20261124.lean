import Manuscript15.TerminalLagrangeWeightedConvolution20261123
import Mathlib.Tactic

/-!
# Manuscript 15 §6.2 — leading-jet transfer under actual formal inversion

The all-order Lagrange--Bürmann formula in
`TerminalLagrangeWeightedConvolution20261123` controls arbitrary formal
outer series. Here we prove, for the same *actual fixed-point equation*
`H = X * subst H ψ`, that composition preserves the exact initial
vanishing order and transports the first nonzero coefficient by
`(coeff 0 ψ)^d`. This is a finite-coefficient statement, not a
claim about convergence of the terminal analytic graph.

It isolates precisely the coefficientwise fact needed to join the
independent-variable analytic contact jets to the formal inversion
formula. The identification of the particular analytic Taylor series
of the terminal functions and the spectral determinant remains separate.
-/

namespace Manuscript15.TerminalLagrangeLeadingTransfer

open PowerSeries
open Manuscript15.TerminalLagrangeWeighted
open Manuscript15.TerminalLagrangeFinite

abbrev P := PowerSeries ℝ

/-- Every coefficient strictly below the first potentially nonzero
degree remains zero after substitution into the actual fixed-point
solution. The proof uses the finite substitution formula, not an
infinite rearrangement. -/
theorem lower_coeff_vanish (H ψ G : P)
    (hH : H = PowerSeries.X * PowerSeries.subst H ψ)
    (d n : ℕ) (hn : n < d)
    (hG : ∀ j < d, PowerSeries.coeff j G = 0) :
    PowerSeries.coeff n (PowerSeries.subst H G) = 0 := by
  rw [general_subst_finite H ψ G hH n]
  apply Finset.sum_eq_zero
  intro j hj
  have hjle : j ≤ n := by
    have hj' := Finset.mem_range.mp hj
    omega
  have hjlt : j < d := lt_of_le_of_lt hjle hn
  simp [hG j hjlt]

/-- The first possible nonzero coefficient is transported by the
diagonal coefficient of the fixed-point solution. No normalization
of ψ is required here. -/
theorem leading_coeff_transfer (H ψ G : P)
    (hH : H = PowerSeries.X * PowerSeries.subst H ψ)
    (d : ℕ)
    (hG : ∀ j < d, PowerSeries.coeff j G = 0) :
    PowerSeries.coeff d (PowerSeries.subst H G) =
      PowerSeries.coeff d G * PowerSeries.coeff 0 (ψ ^ d) := by
  rw [general_subst_finite H ψ G hH d]
  rw [Finset.sum_range_succ]
  have hz :
      (∑ j ∈ Finset.range d,
        PowerSeries.coeff j G * PowerSeries.coeff d (H ^ j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [hG j (Finset.mem_range.mp hj)]
  rw [hz, zero_add]
  rw [fixedpoint_diagonal H ψ hH d]

/-- When ψ(0)=1, the first nonzero coefficient is unchanged:
an exact algebraic transfer of the leading Taylor jet. -/
theorem leading_coeff_normalized (H ψ G : P)
    (hH : H = PowerSeries.X * PowerSeries.subst H ψ)
    (hψ : PowerSeries.coeff 0 ψ = 1)
    (d : ℕ)
    (hG : ∀ j < d, PowerSeries.coeff j G = 0) :
    PowerSeries.coeff d (PowerSeries.subst H G) =
      PowerSeries.coeff d G := by
  have h := leading_coeff_transfer H ψ G hH d hG
  have hψ' : PowerSeries.constantCoeff ψ = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hψ
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_pow, hψ', one_pow, mul_one] using h

/-- A nonzero leading jet remains nonzero under normalized inversion;
together with lower_coeff_vanish, its order is exactly d. -/
theorem leading_coeff_nonzero (H ψ G : P)
    (hH : H = PowerSeries.X * PowerSeries.subst H ψ)
    (hψ : PowerSeries.coeff 0 ψ = 1)
    (d : ℕ)
    (hG : ∀ j < d, PowerSeries.coeff j G = 0)
    (hd : PowerSeries.coeff d G ≠ 0) :
    PowerSeries.coeff d (PowerSeries.subst H G) ≠ 0 := by
  rw [leading_coeff_normalized H ψ G hH hψ d hG]
  exact hd

/-- Division-form all-order Lagrange--Bürmann coefficient identity,
with the `1/n` normalization actually printed in M15 §6.2.
The coefficient on the right is that of the formal derivative of G,
multiplied by ψ^n; no nonconvergent formal substitution is used. -/
theorem closed_general_coeff_div (H ψ G : P)
    (hH : H = PowerSeries.X * PowerSeries.subst H ψ)
    (n : ℕ) (hn : 0 < n) :
    PowerSeries.coeff n (PowerSeries.subst H G) =
      PowerSeries.coeff (n - 1)
        (((PowerSeries.derivative (R := ℝ)) G) * ψ ^ n) / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hc := closed_general_coeff H ψ G hH n hn
  apply (eq_div_iff hn0).2
  calc
    PowerSeries.coeff n (PowerSeries.subst H G) * (n : ℝ) =
        (n : ℝ) * PowerSeries.coeff n (PowerSeries.subst H G) := by ring
    _ = PowerSeries.coeff (n - 1)
          (((PowerSeries.derivative (R := ℝ)) G) * ψ ^ n) := hc


/-- Construct the actual formal inverse from any normalized series
φ(0)=1. The fixed-point equation is derived from the two-sided
composition inverse in Mathlib, not assumed. -/
theorem exists_fixedpoint_from_normalized_phi (φ : P)
    (hφ : PowerSeries.coeff 0 φ = 1) :
    ∃ H : P,
      H = PowerSeries.X * PowerSeries.subst H (φ⁻¹) ∧
      PowerSeries.subst H (PowerSeries.X * φ) = PowerSeries.X := by
  have hφ0 : PowerSeries.constantCoeff φ = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hφ
  have hF0 : PowerSeries.constantCoeff (PowerSeries.X * φ) = 0 := by
    simp
  have hF1 : PowerSeries.coeff 1 (PowerSeries.X * φ) = 1 := by
    have h := PowerSeries.coeff_X_pow_mul φ 1 0
    simpa only [pow_one, zero_add, hφ] using h
  have hFu : IsUnit (PowerSeries.coeff 1 (PowerSeries.X * φ)) := by
    rw [hF1]
    exact isUnit_one
  let H : P := PowerSeries.substInvOfIsUnit
    (PowerSeries.X * φ) hFu
  have hs : PowerSeries.HasSubst H := by
    exact PowerSeries.HasSubst.substInvOfIsUnit
      (PowerSeries.X * φ) hFu
  have hright : PowerSeries.subst H (PowerSeries.X * φ) = PowerSeries.X := by
    exact PowerSeries.subst_substInvOfIsUnit_right
      (PowerSeries.X * φ) hF0 hFu
  have hproduct : H * PowerSeries.subst H φ = PowerSeries.X := by
    simpa only [PowerSeries.subst_mul hs, PowerSeries.subst_X hs]
      using hright
  have hmul : φ * φ⁻¹ = 1 := by
    exact PowerSeries.mul_inv_cancel φ (by simp [hφ0])
  have hmapone : PowerSeries.subst H (1 : P) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hs]
    exact map_one _
  have hsubstunit :
      PowerSeries.subst H φ * PowerSeries.subst H (φ⁻¹) = 1 := by
    rw [← PowerSeries.subst_mul hs, hmul]
    exact hmapone
  refine ⟨H, ?_, hright⟩
  calc
    H = H * 1 := by ring
    _ = H * (PowerSeries.subst H φ * PowerSeries.subst H (φ⁻¹)) := by
      rw [hsubstunit]
    _ = (H * PowerSeries.subst H φ) * PowerSeries.subst H (φ⁻¹) := by
      ring
    _ = PowerSeries.X * PowerSeries.subst H (φ⁻¹) := by rw [hproduct]

/-- Closed all-order Lagrange--Bürmann formula with an ACTUALLY CONSTRUCTED
formal compositional inverse of F=X·φ. There is no fixed-point
hypothesis in the statement. This remains an algebraic power-series
result, distinct from analytic convergence at the terminal graph. -/
theorem exists_closed_general_for_normalized_phi (φ G : P)
    (hφ : PowerSeries.coeff 0 φ = 1) :
    ∃ H : P,
      PowerSeries.subst H (PowerSeries.X * φ) = PowerSeries.X ∧
      ∀ n : ℕ, 0 < n →
        PowerSeries.coeff n (PowerSeries.subst H G) =
          PowerSeries.coeff (n - 1)
            (((PowerSeries.derivative (R := ℝ)) G) * (φ⁻¹) ^ n) /
              (n : ℝ) := by
  obtain ⟨H, hH, hF⟩ :=
    exists_fixedpoint_from_normalized_phi φ hφ
  exact ⟨H, hF, fun n hn => closed_general_coeff_div H (φ⁻¹) G hH n hn⟩

#print axioms Manuscript15.TerminalLagrangeLeadingTransfer.exists_fixedpoint_from_normalized_phi
#print axioms Manuscript15.TerminalLagrangeLeadingTransfer.exists_closed_general_for_normalized_phi

#print axioms Manuscript15.TerminalLagrangeLeadingTransfer.lower_coeff_vanish
#print axioms Manuscript15.TerminalLagrangeLeadingTransfer.leading_coeff_transfer
#print axioms Manuscript15.TerminalLagrangeLeadingTransfer.leading_coeff_normalized
#print axioms Manuscript15.TerminalLagrangeLeadingTransfer.leading_coeff_nonzero
#print axioms Manuscript15.TerminalLagrangeLeadingTransfer.closed_general_coeff_div

end Manuscript15.TerminalLagrangeLeadingTransfer
