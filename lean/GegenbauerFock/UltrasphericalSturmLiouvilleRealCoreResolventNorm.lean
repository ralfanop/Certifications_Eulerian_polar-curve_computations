import GegenbauerFock.UltrasphericalSturmLiouvilleRealPositiveResolventIdentity
import GegenbauerFock.UltrasphericalSturmLiouvilleRealEnergyNonpositive
import GegenbauerFock.UltrasphericalSturmLiouvillePositiveShiftNormBound

/-!
# V007 — sharp boundedness of the positive resolvent on the true L² core

Unlike the algebraic finite-polynomial inverse, the following
estimate is in the actual real weighted-Hilbert L² norm:

  ‖R_t f‖_{L²} ≤ ‖f‖_{L²} / t   (t>0).

It comes from the NOW certified unconditional Dirichlet-energy
nonpositivity of the real ultraspherical Sturm operator and the
exact positive shifted polynomial-domain equation.

This is the quantitative ingredient for extending R_t uniquely to
the entire real Hilbert space by completion. An everywhere-defined
full-L² extension is not yet constructed here.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev D (lam : ℝ) (hlam : 0 < lam) :=
  sturmRealPolynomialDomain lam hlam

/-- The exact positive polynomial-core Sturm resolvent has the sharp
real weighted-L² operator norm bound 1/t. -/
theorem sturmRealCorePositiveResolvent_norm_le
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : D lam hlam) :
    ‖(sturmRealDomainPositiveResolvent lam t hlam ht f :
        SturmH lam)‖ ≤ ‖(f : SturmH lam)‖ / t := by
  let u : D lam hlam :=
    sturmRealDomainPositiveResolvent lam t hlam ht f
  have hu : t • (u : SturmH lam) -
      sturmRealPartialOperator lam hlam u = (f : SturmH lam) := by
    have hv := congrArg Subtype.val
      (sturmRealDomainPositiveShift_resolvent lam t hlam ht f)
    simpa [sturmRealDomainPositiveShift, sturmRealPartialOperator_apply, u]
      using hv
  have hb := sturmReal_nonpositive_positive_shift_norm
    lam t ht
    (sturmRealPartialOperator lam hlam)
    (sturmRealPartialOperator_nonpositive lam hlam)
    (u : (sturmRealPartialOperator lam hlam).domain)
  rw [hu] at hb
  exact (le_div_iff₀ ht).2 hb

/-- Quantitative Lipschitz bound for the inverse of tI-L
on the TRUE polynomial-image L² domain. -/
theorem sturmRealCorePositiveResolvent_lipschitz
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f g : D lam hlam) :
    ‖(sturmRealDomainPositiveResolvent lam t hlam ht f :
        SturmH lam) -
      (sturmRealDomainPositiveResolvent lam t hlam ht g :
        SturmH lam)‖ ≤
      ‖(f : SturmH lam) - (g : SturmH lam)‖ / t := by
  let R := sturmRealDomainPositiveResolvent lam t hlam ht
  have hR : R (f - g) = R f - R g := R.map_sub f g
  have hsub :
      ((f - g : D lam hlam) : SturmH lam) =
        (f : SturmH lam) - (g : SturmH lam) := rfl
  calc
    ‖(R f : SturmH lam) - (R g : SturmH lam)‖ =
        ‖(R (f - g) : SturmH lam)‖ := by
      rw [hR]
      rfl
    _ ≤ ‖((f - g : D lam hlam) : SturmH lam)‖ / t :=
      sturmRealCorePositiveResolvent_norm_le lam t hlam ht (f - g)
    _ = ‖(f : SturmH lam) - (g : SturmH lam)‖ / t := by rw [hsub]

#print axioms GegenbauerFock.Ultraspherical.sturmRealCorePositiveResolvent_norm_le
#print axioms GegenbauerFock.Ultraspherical.sturmRealCorePositiveResolvent_lipschitz

end GegenbauerFock.Ultraspherical
