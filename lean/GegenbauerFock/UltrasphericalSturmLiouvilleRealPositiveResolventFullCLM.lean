import GegenbauerFock.UltrasphericalSturmLiouvilleRealCoreResolventNorm
import GegenbauerFock.UltrasphericalSturmLiouvilleRealPolynomialDensity
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# V007 — full-Hilbert bounded extension of the polynomial resolvent

The exact positive shifted Sturm inverse on the *actual* real
polynomial-image submodule has the sharp weighted-L² norm bound 1/t.
Therefore it defines a bounded real-linear map from the dense
submodule into the complete weighted Hilbert space. Mathlib's
ContinuousLinearMap.extend then gives a canonical bounded
everywhere-defined real-linear operator on all weighted L².

We prove that this extension agrees EXACTLY with the certified finite
polynomial resolvent on the dense polynomial core.

Showing that this bounded extension is the inverse of
tI - closure(A_0) is a separate closed-graph argument, not
silently assumed by the definition.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev D (lam : ℝ) (hlam : 0 < lam) :=
  sturmRealPolynomialDomain lam hlam

/-- The actual polynomial-core positive Sturm resolvent is a
continuous real-linear map into the ambient weighted L² Hilbert space. -/
noncomputable def sturmRealCorePositiveResolventCLM
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    D lam hlam →L[ℝ] SturmH lam :=
  (((D lam hlam).subtype).comp
    (sturmRealDomainPositiveResolvent lam t hlam ht)).mkContinuous
      t⁻¹ (by
        intro f
        change ‖(sturmRealDomainPositiveResolvent lam t hlam ht f :
            SturmH lam)‖ ≤ t⁻¹ * ‖f‖
        calc
          _ ≤ ‖(f : SturmH lam)‖ / t :=
            sturmRealCorePositiveResolvent_norm_le lam t hlam ht f
          _ = t⁻¹ * ‖f‖ := by
            change ‖(f : SturmH lam)‖ / t =
              t⁻¹ * ‖(f : SturmH lam)‖
            rw [div_eq_mul_inv]
            ring)

@[simp] theorem sturmRealCorePositiveResolventCLM_apply
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : D lam hlam) :
    sturmRealCorePositiveResolventCLM lam t hlam ht f =
      (sturmRealDomainPositiveResolvent lam t hlam ht f :
        SturmH lam) := by
  rfl

/-- Unique continuous real-linear extension of the exact
finite-polynomial inverse of tI-A to the COMPLETE actual weighted
L² space. No self-adjointness is assumed in its construction. -/
noncomputable def sturmRealPositiveResolventFullCLM
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    SturmH lam →L[ℝ] SturmH lam :=
  (sturmRealCorePositiveResolventCLM lam t hlam ht).extend
    (Submodule.subtypeL (D lam hlam))

/-- The full-L² bounded extension evaluates to the EXACT certified
finite polynomial resolvent on every genuine core vector. -/
theorem sturmRealPositiveResolventFullCLM_onCore
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : D lam hlam) :
    sturmRealPositiveResolventFullCLM lam t hlam ht
      (f : SturmH lam) =
        (sturmRealDomainPositiveResolvent lam t hlam ht f :
          SturmH lam) := by
  have hdense :
      Dense (D lam hlam : Set (SturmH lam)) :=
    sturmRealPolynomialDomain_dense_set lam hlam
  unfold sturmRealPositiveResolventFullCLM
  simpa only [sturmRealCorePositiveResolventCLM_apply,
    Submodule.subtypeL_apply] using
    (ContinuousLinearMap.extend_eq
      (sturmRealCorePositiveResolventCLM lam t hlam ht)
      hdense.denseRange_val
      isUniformEmbedding_subtype_val.isUniformInducing f)

#print axioms GegenbauerFock.Ultraspherical.sturmRealCorePositiveResolventCLM_apply
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_onCore

end GegenbauerFock.Ultraspherical
