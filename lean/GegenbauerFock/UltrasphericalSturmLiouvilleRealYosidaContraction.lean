import GegenbauerFock.UltrasphericalSturmLiouvilleRealFullResolventNorm
import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventSpectralGraph

/-!
# V007 — Yosida resolvent contractions on genuine real ultraspherical L²

For the ACTUAL canonical polynomial Sturm closure A and all t > 0,
the bounded full-space resolvent R_t = (tI - A)⁻¹ satisfies:

* ‖t R_t f‖ ≤ ‖f‖ for every f in the full weighted real L² space;
* t R_t x - x = R_t (A x) for every x in the closed operator domain;
* ‖t R_t x - x‖ ≤ ‖A x‖ / t.

The last estimate is the quantitative core step for strong convergence
of the Yosida contractions to the identity. These results alone do not
construct or certify a C₀ semigroup.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The actual positive Sturm resolvent scaled by t is a contraction
on the ENTIRE weighted-real-L² Hilbert space. -/
theorem sturmRealYosidaContraction_norm_le
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) :
    ‖t • sturmRealPositiveResolventFullCLM lam t hlam ht f‖ ≤ ‖f‖ := by
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  have hb : ‖R f‖ ≤ ‖f‖ / t :=
    sturmRealPositiveResolventFullCLM_norm_le lam t hlam ht f
  have hmul : ‖R f‖ * t ≤ ‖f‖ :=
    (le_div_iff₀ ht).mp hb
  calc
    ‖t • R f‖ = t * ‖R f‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    _ ≤ ‖f‖ := by nlinarith

/-- Exact domain-aware Yosida identity for the genuine closed
unbounded Sturm differential operator, not an abstract core model. -/
theorem sturmRealYosidaContraction_on_closed_domain
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    t • sturmRealPositiveResolventFullCLM lam t hlam ht
        (x : SturmH lam) - (x : SturmH lam) =
      sturmRealPositiveResolventFullCLM lam t hlam ht
        ((sturmRealPartialOperator lam hlam).closure x) := by
  let A := (sturmRealPartialOperator lam hlam).closure
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  have hleft : R (t • (x : SturmH lam) - A x) = (x : SturmH lam) :=
    sturmRealPositiveResolventFullCLM_left_inverse_closed_shift
      lam t hlam ht x
  have hlinear : t • R (x : SturmH lam) - R (A x) = (x : SturmH lam) := by
    simpa only [map_sub, map_smul] using hleft
  calc
    t • R (x : SturmH lam) - (x : SturmH lam) =
        t • R (x : SturmH lam) -
          (t • R (x : SturmH lam) - R (A x)) := by rw [hlinear]
    _ = R (A x) := by abel

/-- Quantitative convergence rate O(1/t) of the exact
Yosida contraction for every element of the closed Sturm domain. -/
theorem sturmRealYosidaContraction_closed_domain_error_le
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    ‖t • sturmRealPositiveResolventFullCLM lam t hlam ht
       (x : SturmH lam) - (x : SturmH lam)‖ ≤
      ‖(sturmRealPartialOperator lam hlam).closure x‖ / t := by
  rw [sturmRealYosidaContraction_on_closed_domain lam t hlam ht x]
  exact sturmRealPositiveResolventFullCLM_norm_le lam t hlam ht
    ((sturmRealPartialOperator lam hlam).closure x)

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaContraction_norm_le
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaContraction_on_closed_domain
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaContraction_closed_domain_error_le

end GegenbauerFock.Ultraspherical
