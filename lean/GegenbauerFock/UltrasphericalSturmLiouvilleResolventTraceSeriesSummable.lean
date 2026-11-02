import GegenbauerFock.UltrasphericalSturmLiouvilleResolventQuadraticDecay
import Mathlib.Analysis.PSeries

/-!
# V007 — summability of the canonical closed Sturm resolvent multipliers

For every λ,t>0, the exact positive eigenvalues
  βₙ = (t + n(n+2λ))⁻¹
are summable. Their sum is finite, as required for the **scalar**
trace series and a future genuine trace-class/Schatten S₁
certification on the real weighted L².

Important: this module proves scalar spectral summability; it
does NOT equate a general operator trace with this scalar sum or
declare the resolvent trace-class without an operator-ideal bridge.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

/-- The actual positive closed Gegenbauer Sturm resolvent has
summable real spectral multipliers, by the certified 1/n² comparison
away from the degree-zero mode. -/
theorem sturmResolventMultiplier_summable
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Summable (fun n : ℕ =>
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹) := by
  let β : ℕ → ℝ := fun n =>
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹
  have hpseries :
      Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
  have hpseries_tail :
      Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    exact (summable_nat_add_iff
      (f := fun n : ℕ => 1 / ((n : ℝ) ^ 2)) 1).mpr hpseries
  have htail :
      Summable (fun n : ℕ => β (n + 1)) := by
    refine Summable.of_nonneg_of_le
      (fun n => le_of_lt (sturmResolventMultiplier_pos lam t hlam ht (n + 1)))
      (fun n => ?_) hpseries_tail
    have h := sturmResolventMultiplier_le_inv_degree_sq
      lam t hlam ht (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    simpa only [β, one_div] using h
  exact (summable_nat_add_iff (f := β) 1).mp htail

/-- The positive real scalar spectral trace series of the canonical
closed resolvent exists (without yet asserting an operator trace). -/
noncomputable def sturmResolventSpectralTrace
    (lam t : ℝ) : ℝ :=
  ∑' n : ℕ, (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹

#print axioms GegenbauerFock.Ultraspherical.sturmResolventMultiplier_summable

end GegenbauerFock.Ultraspherical
