import Mathlib.Tactic

/-!
# V007 — exact scalar energy inequality for Tikhonov Fock-data noise

The direct Hilbert-energy proof of the regularized inverse's
1/(2 sqrt(eps)) noise amplification bound reduces to a scalar
complete-the-square inequality.

Given eps>0 and three real numbers a,b,c with a,c≥0, the energy
inequality eps*a²+b²≤c*b implies a≤c/(2 sqrt(eps)).

In the actual Gegenbauer–Fock application, a=‖R_eps eta‖,
b=‖C(R_eps eta)‖ and c=‖eta‖. This module certifies the scalar
step; the genuine Hilbert operator energy identity is a separate
formalization obligation, not assumed here to hold automatically.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Sharp scalar completion-of-squares bound needed for regularized
data-space noise amplification. No spectral diagonalization. -/
theorem tikhonov_scalar_energy_noise_bound
    (eps a b c : ℝ) (heps : 0 < eps) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (henergy : eps * a ^ 2 + b ^ 2 ≤ c * b) :
    a ≤ c / (2 * Real.sqrt eps) := by
  have hsqrt : 0 < Real.sqrt eps := Real.sqrt_pos.2 heps
  have hquadr : eps * a ^ 2 ≤ c ^ 2 / 4 := by
    nlinarith [sq_nonneg (b - c / 2)]
  have hsquare :
      (2 * Real.sqrt eps * a) ^ 2 = 4 * (eps * a ^ 2) := by
    calc
      (2 * Real.sqrt eps * a) ^ 2 =
          4 * ((Real.sqrt eps) ^ 2 * a ^ 2) := by ring
      _ = 4 * (eps * a ^ 2) := by rw [Real.sq_sqrt heps.le]
  have hsq_le : (2 * Real.sqrt eps * a) ^ 2 ≤ c ^ 2 := by
    rw [hsquare]
    nlinarith [hquadr]
  have hnonneg : 0 ≤ 2 * Real.sqrt eps * a := by positivity
  have hlinear : 2 * Real.sqrt eps * a ≤ c :=
    (sq_le_sq₀ hnonneg hc).mp hsq_le
  have hden : 0 < 2 * Real.sqrt eps := by positivity
  apply (le_div_iff₀ hden).2
  nlinarith [hlinear]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.tikhonov_scalar_energy_noise_bound

end GegenbauerFock.GeneralUltrasphericalFock
