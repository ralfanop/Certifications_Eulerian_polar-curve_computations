import GegenbauerFock.UltrasphericalSturmLiouvilleResolventTraceSeriesSummable
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventMultiplierMonotone

/-!
# V007 — squared spectral multipliers of the true closed Sturm resolvent

The canonical closed Gegenbauer–Sturm resolvent has nonnegative
summable eigenvalues βₙ. Because 0<βₙ≤β₀=1/t, it also has a
summable squared spectral sequence ∑ βₙ².

This proves the SCALAR Schatten-2 summability condition without
claiming to have constructed an actual Hilbert–Schmidt ideal
element or an operator trace on the real weighted L². The latter
requires an explicit operator-ideal compatibility bridge.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

/-- Every positive-shift canonical closed Sturm resolvent has
a summable squared real spectral multiplier sequence. -/
theorem sturmResolventMultiplier_sq_summable
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Summable (fun n : ℕ =>
      ((t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹) ^ 2) := by
  let β : ℕ → ℝ := fun n =>
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹
  have hsum : Summable β :=
    sturmResolventMultiplier_summable lam t hlam ht
  have hmax (n : ℕ) : β n ≤ β 0 :=
    sturmResolventMultiplier_antitone lam t hlam ht (Nat.zero_le n)
  have hnonneg (n : ℕ) : 0 ≤ β n := by
    exact le_of_lt (sturmResolventMultiplier_pos lam t hlam ht n)
  have hcomp (n : ℕ) : β n ^ 2 ≤ β 0 * β n := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (hmax n)) (hnonneg n)]
  have hscalar : Summable (fun n : ℕ => β 0 * β n) :=
    hsum.mul_left (β 0)
  exact Summable.of_nonneg_of_le
    (fun n => sq_nonneg (β n)) hcomp hscalar

/-- The scalar squared spectral trace of the actual canonical
Sturm resolvent is finite (operator HS-class is not asserted). -/
noncomputable def sturmResolventSquaredSpectralTrace
    (lam t : ℝ) : ℝ :=
  ∑' n : ℕ,
    ((t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹) ^ 2

#print axioms GegenbauerFock.Ultraspherical.sturmResolventMultiplier_sq_summable

end GegenbauerFock.Ultraspherical
