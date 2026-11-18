import Mathlib
import Manuscript16.V165ResonanceGenerating

/-! M16 v16.5, §14.3, eq. res-gen-function. Unlike #339, the
actual infinite scalar energy sum is formalized. Operator trace
realization and termwise differentiation remain separate. -/
namespace Manuscript16.V165

theorem resonance_hasSum (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => resonanceWeight n * q^n)
      (4 * (3-q) / (1-q)^3) := by
  have hn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq] using hq1
  have h0 := hasSum_geometric_of_norm_lt_one hn
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have h2 := hasSum_sq_mul_geometric_of_norm_lt_one hn
  have h := (h2.mul_left (4 : ℝ)).add ((h1.mul_left (16 : ℝ)).add (h0.mul_left (12 : ℝ)))
  convert h using 1
  · funext n
    unfold resonanceWeight
    ring
  · have hd : 1-q ≠ 0 := by linarith
    field_simp [hd] <;> ring

theorem resonance_tsum (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    (∑' n : ℕ, resonanceWeight n * q^n) = 4 * (3-q) / (1-q)^3 :=
  (resonance_hasSum q hq hq1).tsum_eq

theorem odd_energy_exp (x : ℝ) (n : ℕ) :
    Real.exp (-x * (2 * (n : ℝ) + 1)) =
      Real.exp (-x) * (Real.exp (-2*x))^n := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- The actual infinite scalar Maxwell Boltzmann series at positive time. -/
theorem maxwell_heat_hasSum (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℕ => resonanceWeight n * Real.exp (-x * (2 * (n : ℝ) + 1)))
      (Real.exp (-x) * (4 * (3-Real.exp (-2*x)) / (1-Real.exp (-2*x))^3)) := by
  have hp : 0 < Real.exp (-2*x) := Real.exp_pos _
  have hl : Real.exp (-2*x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := (resonance_hasSum (Real.exp (-2*x)) hp hl).mul_left (Real.exp (-x))
  convert h using 1
  · funext n
    rw [odd_energy_exp]
    ring

/-- Unit multiplicity odd-ladder series, with the same parameterization. -/
theorem magnetic_heat_hasSum (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℕ => Real.exp (-x * (2 * (n : ℝ) + 1)))
      (Real.exp (-x) * (1-Real.exp (-2*x))⁻¹) := by
  have hq : ‖Real.exp (-2*x)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have h := (hasSum_geometric_of_norm_lt_one hq).mul_left (Real.exp (-x))
  convert h using 1
  funext n
  exact odd_energy_exp x n

#print axioms Manuscript16.V165.resonance_hasSum
#print axioms Manuscript16.V165.resonance_tsum
#print axioms Manuscript16.V165.odd_energy_exp
#print axioms Manuscript16.V165.maxwell_heat_hasSum
#print axioms Manuscript16.V165.magnetic_heat_hasSum
end Manuscript16.V165
