import GegenbauerFock.UltrasphericalSturmLiouvilleRealClosedFullResolvent

/-!
# V007 — sharp full-real-Hilbert Sturm positive resolvent bound

The genuine canonical closure of the ultraspherical Sturm operator
has a positive full-space bounded resolvent for every t > 0.
The closed-graph identity and the certified nonpositive quadratic
form imply the sharp global estimate ‖R_t f‖ ≤ ‖f‖ / t.

This module does not assume a spectral eigenbasis or essential
self-adjointness; it concerns the actual weighted real Hilbert L².
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The full-space bounded real Sturm resolvent satisfies the sharp
pointwise positive-shift estimate for every L² vector. -/
theorem sturmRealPositiveResolventFullCLM_norm_le
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) :
    ‖sturmRealPositiveResolventFullCLM lam t hlam ht f‖ ≤
      ‖f‖ / t := by
  let A := sturmRealPartialOperator lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  obtain ⟨x, hx⟩ := (A.closure.mem_graph_iff').mp
    (sturmRealPositiveResolventFullCLM_closed_graph lam t hlam ht f)
  have h1 : (x : SturmH lam) = R f := congrArg Prod.fst hx
  have h2 : A.closure x = t • R f - f := congrArg Prod.snd hx
  have hshift : t • (x : SturmH lam) - A.closure x = f := by
    rw [h1, h2]
    abel
  have hb := sturmRealClosedPositiveShift_norm lam t hlam ht x
  rw [hshift] at hb
  have hmul : ‖R f‖ * t ≤ ‖f‖ := by
    rw [← h1]
    nlinarith [hb]
  exact (le_div_iff₀ ht).2 hmul

/-- The full bounded resolvent has operator norm at most the sharp
constant 1/t for every positive real shift. -/
theorem sturmRealPositiveResolventFullCLM_opNorm_le
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    ‖sturmRealPositiveResolventFullCLM lam t hlam ht‖ ≤ t⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (le_of_lt (inv_pos.mpr ht))
  intro f
  calc
    ‖sturmRealPositiveResolventFullCLM lam t hlam ht f‖ ≤
        ‖f‖ / t :=
      sturmRealPositiveResolventFullCLM_norm_le lam t hlam ht f
    _ = t⁻¹ * ‖f‖ := by
      rw [div_eq_mul_inv]
      ring

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_norm_le
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_opNorm_le

end GegenbauerFock.Ultraspherical
