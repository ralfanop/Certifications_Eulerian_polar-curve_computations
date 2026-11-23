import Mathlib

/-!
# Manuscript 13 — Costa–Natário ultrastationary magnetic reduction (23 Nov 2026)

Source: the user's `Manuscript_13_20261123_COSTA_NATARIO_HOLONOMY_COMPLETE`,
`13/13.tex`, equations
`ultrastationary-covariant-derivative`,
`ultrastationary-gauge-intertwiner`, and
`ultrastationary-covariant-commutator`.

This file *extends* previously certified M13 modules without modifying them.

A derivation is supplied by its Leibniz rule on a commutative coefficient
ring, with additive linearity encoded by `R →+ R`.
The results are exact first- and second-order differential *algebra*
statements (the local calculation). They do not assert Poincaré's lemma,
existence of global S¹ phases, or unbounded selfadjoint-domain transport.
-/

namespace Manuscript13.CostaNatario20261123

variable {R : Type*} [CommRing R]

/-- The local covariant differential operator `D_i = ∂_i - ζ A_i`,
where `ζ = iω` in the manuscript. -/
def magneticCovDerivative (d : R →+ R) (ζ A u : R) : R :=
  d u - ζ * A * u

/-- Exact local gauge covariance
`D_{A+dχ}(h u) = h D_A u` whenever `d h = ζ (dχ) h`.
No global phase is postulated or constructed. -/
theorem gauge_first_order (d : R →+ R)
    (hLeibniz : ∀ x y : R, d (x * y) = d x * y + x * d y)
    (ζ A dχ h u : R) (hPhase : d h = ζ * dχ * h) :
    magneticCovDerivative d ζ (A + dχ) (h * u) =
      h * magneticCovDerivative d ζ A u := by
  simp only [magneticCovDerivative, hLeibniz, hPhase]
  ring

/-- Composition of two magnetic derivatives is gauge covariant on a
common phase. This is a building block, not yet a complete weighted
magnetic Laplace–Beltrami theorem. -/
theorem gauge_second_order (d₁ d₂ : R →+ R)
    (hLeibniz₁ : ∀ x y : R, d₁ (x * y) = d₁ x * y + x * d₁ y)
    (hLeibniz₂ : ∀ x y : R, d₂ (x * y) = d₂ x * y + x * d₂ y)
    (ζ A₁ A₂ χ₁ χ₂ h u : R)
    (hPhase₁ : d₁ h = ζ * χ₁ * h)
    (hPhase₂ : d₂ h = ζ * χ₂ * h) :
    magneticCovDerivative d₁ ζ (A₁ + χ₁)
        (magneticCovDerivative d₂ ζ (A₂ + χ₂) (h * u)) =
      h * magneticCovDerivative d₁ ζ A₁
        (magneticCovDerivative d₂ ζ A₂ u) := by
  rw [gauge_first_order d₂ hLeibniz₂ ζ A₂ χ₂ h u hPhase₂]
  exact gauge_first_order d₁ hLeibniz₁ ζ A₁ χ₁ h
    (magneticCovDerivative d₂ ζ A₂ u) hPhase₁

/-- `[D_i,D_j]u = -ζ(∂_i A_j - ∂_j A_i)u`.
Assumes commuting background derivatives and constant frequency `ζ`.
This formalises the local curvature obstruction independently of
the global holonomy condition. -/
theorem magnetic_curvature_commutator (d₁ d₂ : R →+ R)
    (hLeibniz₁ : ∀ x y : R, d₁ (x * y) = d₁ x * y + x * d₁ y)
    (hLeibniz₂ : ∀ x y : R, d₂ (x * y) = d₂ x * y + x * d₂ y)
    (ζ A₁ A₂ u : R)
    (hFrequency₁ : d₁ ζ = 0) (hFrequency₂ : d₂ ζ = 0)
    (hComm : d₁ (d₂ u) = d₂ (d₁ u)) :
    magneticCovDerivative d₁ ζ A₁
        (magneticCovDerivative d₂ ζ A₂ u) -
      magneticCovDerivative d₂ ζ A₂
        (magneticCovDerivative d₁ ζ A₁ u) =
      -(ζ * (d₁ A₂ - d₂ A₁) * u) := by
  simp only [magneticCovDerivative, map_sub, hLeibniz₁,
    hLeibniz₂, hFrequency₁, hFrequency₂, zero_mul, zero_add, hComm]
  ring

/-- Exact potentials have zero abstract curvature when derivatives commute. -/
theorem exact_potential_flatness (d₁ d₂ : R →+ R) (χ : R)
    (hComm : d₁ (d₂ χ) = d₂ (d₁ χ)) :
    d₁ (d₂ χ) - d₂ (d₁ χ) = 0 := by
  rw [hComm]
  ring

#print axioms Manuscript13.CostaNatario20261123.gauge_first_order
#print axioms Manuscript13.CostaNatario20261123.gauge_second_order
#print axioms Manuscript13.CostaNatario20261123.magnetic_curvature_commutator
#print axioms Manuscript13.CostaNatario20261123.exact_potential_flatness

end Manuscript13.CostaNatario20261123
