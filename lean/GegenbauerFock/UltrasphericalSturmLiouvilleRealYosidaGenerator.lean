import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaStrongApproximation
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# V007 — bounded dissipative Yosida generators of the true Sturm closure

The canonical closed ultraspherical real Sturm operator A is densely defined,
nonpositive, and has a full-space positive resolvent R_t for all t > 0.
The bounded Yosida approximation to A is the actual continuous linear map

  A_t := t² R_t - t I = t (t R_t - I).

The contraction bound for t R_t proves dissipativity of A_t directly in
the genuine weighted real L² inner product. In particular, this does not
assume an already constructed semigroup or a diagonal Gegenbauer basis.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory
private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Bounded real-Hilbert Yosida approximation to the actual closed
ultraspherical Sturm operator, on the entire weighted real L² space. -/
noncomputable def sturmRealYosidaGenerator
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    SturmH lam →L[ℝ] SturmH lam :=
  t • (t • sturmRealPositiveResolventFullCLM lam t hlam ht -
    ContinuousLinearMap.id ℝ (SturmH lam))

/-- Explicit vector action of the actual bounded Yosida generator. -/
theorem sturmRealYosidaGenerator_apply
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) :
    sturmRealYosidaGenerator lam t hlam ht f =
      t • (t • sturmRealPositiveResolventFullCLM lam t hlam ht f - f) := by
  simp [sturmRealYosidaGenerator]

/-- Dissipativity of the bounded Yosida generator on ALL of weighted L²:
⟪A_t f, f⟫ ≤ 0, with no extra analytic hypothesis. -/
theorem sturmRealYosidaGenerator_inner_nonpos
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) :
    inner ℝ (sturmRealYosidaGenerator lam t hlam ht f) f ≤ 0 := by
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  have hc : ‖t • R f‖ ≤ ‖f‖ :=
    sturmRealYosidaContraction_norm_le lam t hlam ht f
  have hcs : inner ℝ (t • R f) f ≤ ‖t • R f‖ * ‖f‖ :=
    real_inner_le_norm _ _
  have hm : ‖t • R f‖ * ‖f‖ ≤ ‖f‖ * ‖f‖ :=
    mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  have hinner : inner ℝ (t • R f) f ≤ inner ℝ f f := by
    rw [real_inner_self_eq_norm_sq]
    nlinarith
  have heq : inner ℝ (sturmRealYosidaGenerator lam t hlam ht f) f =
      t * (inner ℝ (t • R f) f - inner ℝ f f) := by
    rw [sturmRealYosidaGenerator_apply]
    simp only [real_inner_smul_left, inner_sub_left]
    ring
  rw [heq]
  exact mul_nonpos_of_nonneg_of_nonpos ht.le (sub_nonpos.mpr hinner)

/-- Explicit norm estimate on the whole Hilbert space. -/
theorem sturmRealYosidaGenerator_norm_le
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) :
    ‖sturmRealYosidaGenerator lam t hlam ht f‖ ≤ 2 * t * ‖f‖ := by
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  have hc : ‖t • R f‖ ≤ ‖f‖ :=
    sturmRealYosidaContraction_norm_le lam t hlam ht f
  rw [sturmRealYosidaGenerator_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos ht]
  have htri : ‖t • R f - f‖ ≤ ‖t • R f‖ + ‖f‖ :=
    norm_sub_le _ _
  have hb : t * ‖t • R f - f‖ ≤
      t * (‖t • R f‖ + ‖f‖) :=
    mul_le_mul_of_nonneg_left htri ht.le
  nlinarith [norm_nonneg f]

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaGenerator_apply
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaGenerator_inner_nonpos
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaGenerator_norm_le

end GegenbauerFock.Ultraspherical
