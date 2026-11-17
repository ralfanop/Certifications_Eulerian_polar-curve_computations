import Mathlib

/-! Manuscript 14.119, (175)–(179). The exact geometric/electromagnetic
rewriting is independent of the precision of the empirical SI estimate. -/

open MeasureTheory
open scoped ENNReal

namespace Manuscript14.Permeability

theorem sphere_density_cancel (k μ₀ : ℝ)
    (hSI : μ₀ = (4 * Real.pi) * k) :
    μ₀ * (1 / (4 * Real.pi)) = k := by
  have hp : (4 * Real.pi) ≠ 0 := by positivity
  rw [hSI]
  field_simp [hp] <;> ring

theorem scaled_bloch_measure {α : Type*} [MeasurableSpace α]
    (ν Ω : Measure α) (k μ₀ : ℝ) (hμ : 0 ≤ μ₀)
    (hν : ν = ENNReal.ofReal (1 / (4 * Real.pi)) • Ω)
    (hSI : μ₀ = (4 * Real.pi) * k) :
    ENNReal.ofReal μ₀ • ν = ENNReal.ofReal k • Ω := by
  rw [hν, smul_smul, ← ENNReal.ofReal_mul hμ,
    sphere_density_cancel k μ₀ hSI]

theorem permeability_ratio (μ₀ : ℝ) :
    μ₀ / (4 * Real.pi * (1 / 10 ^ 7)) =
      μ₀ / (1 / 10 ^ 7) * (1 / (4 * Real.pi)) := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hp] <;> ring

theorem oeis_factor : 4 * Real.pi = 10 * (2 * Real.pi / 5) := by ring

end Manuscript14.Permeability

#print axioms Manuscript14.Permeability.sphere_density_cancel
#print axioms Manuscript14.Permeability.scaled_bloch_measure
#print axioms Manuscript14.Permeability.permeability_ratio
#print axioms Manuscript14.Permeability.oeis_factor
