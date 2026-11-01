import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitCLM
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitProductPrinciple

/-!
# V007 — exact positive-time semigroup law of the genuine heat-limit CLMs

The limit H_s has been constructed pointwise by completeness from the
positive-shift Yosida semigroups, and is a bounded full-L² operator.

Using the kernel-checked exact finite-Yosida law
S_k(s+u) = S_k(s) S_k(u), the product stability lemma passes this
identity to the strong limit and yields H_(s+u)=H_s H_u.

These are semigroup algebraic identities. Strong continuity of H_s
at time zero and equality of its unbounded infinitesimal generator
with the canonical graph closure remain separate tasks.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The genuine full weighted-L² strong heat-limit operator agrees
pointwise with its defining vector limit. -/
theorem sturmRealHeatLimitCLM_apply
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s)
    (f : SturmH lam) :
    sturmRealHeatLimitCLM lam hlam s hs f =
      sturmRealHeatLimitVector lam hlam s hs f := rfl

/-- Time zero of the constructed full-L² semigroup is identity. -/
theorem sturmRealHeatLimitCLM_zero
    (lam : ℝ) (hlam : 0 < lam) :
    sturmRealHeatLimitCLM lam hlam 0 le_rfl =
      (1 : SturmH lam →L[ℝ] SturmH lam) := by
  ext f
  have hlim := sturmRealHeatLimitVector_tendsto
    lam hlam 0 le_rfl f
  have hconst :
      Tendsto
        (fun k : ℕ =>
          sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
            (by positivity : 0 < (k : ℝ) + 1) 0 f)
        atTop (𝓝 f) := by
    have hfun :
        (fun k : ℕ =>
          sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
            (by positivity : 0 < (k : ℝ) + 1) 0 f) =
        (fun _ : ℕ => f) := by
      funext k
      rw [sturmRealYosidaExponential_zero]
      simp
    rw [hfun]
    exact tendsto_const_nhds
  have heq :
      sturmRealHeatLimitVector lam hlam 0 le_rfl f = f :=
    tendsto_nhds_unique hlim hconst
  simpa only [sturmRealHeatLimitCLM_apply, one_apply] using heq

/-- Exact additive positive-time semigroup law for the constructed
actual weighted real L² heat-limit continuous linear operators. -/
theorem sturmRealHeatLimitCLM_add
    (lam : ℝ) (hlam : 0 < lam)
    (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u) :
    sturmRealHeatLimitCLM lam hlam (s + u) (add_nonneg hs hu) =
      sturmRealHeatLimitCLM lam hlam s hs *
        sturmRealHeatLimitCLM lam hlam u hu := by
  ext f
  have huLimit := sturmRealHeatLimitVector_tendsto lam hlam u hu f
  have hsLimit :=
    sturmRealHeatLimitVector_tendsto lam hlam s hs
      (sturmRealHeatLimitVector lam hlam u hu f)
  have hcontract (k : ℕ) :
      ‖sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
          (by positivity : 0 < (k : ℝ) + 1) s‖ ≤ 1 :=
    sturmRealYosidaExponential_opNorm_le_one lam ((k : ℝ) + 1) hlam
      (by positivity : 0 < (k : ℝ) + 1) s hs
  have hprod := strongLimit_product_of_uniform_contraction
    (fun k : ℕ => sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
      (by positivity : 0 < (k : ℝ) + 1) s)
    (fun k : ℕ => sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
      (by positivity : 0 < (k : ℝ) + 1) u)
    hcontract f (sturmRealHeatLimitVector lam hlam u hu f)
    (sturmRealHeatLimitVector lam hlam s hs
      (sturmRealHeatLimitVector lam hlam u hu f))
    huLimit hsLimit
  have hfun :
      (fun k : ℕ =>
        sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
          (by positivity : 0 < (k : ℝ) + 1) (s + u) f) =
      (fun k : ℕ =>
        sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
          (by positivity : 0 < (k : ℝ) + 1) s
          (sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
            (by positivity : 0 < (k : ℝ) + 1) u f)) := by
    funext k
    rw [sturmRealYosidaExponential_add]
    change
      (sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
         (by positivity : 0 < (k : ℝ) + 1) s)
        ((sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
           (by positivity : 0 < (k : ℝ) + 1) u) f) = _
    rfl
  have hprod' :
      Tendsto
        (fun k : ℕ =>
          sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
            (by positivity : 0 < (k : ℝ) + 1) (s + u) f)
        atTop
        (𝓝 (sturmRealHeatLimitVector lam hlam s hs
          (sturmRealHeatLimitVector lam hlam u hu f))) := by
    rw [hfun]
    exact hprod
  have heq :
      sturmRealHeatLimitVector lam hlam (s + u) (add_nonneg hs hu) f =
        sturmRealHeatLimitVector lam hlam s hs
          (sturmRealHeatLimitVector lam hlam u hu f) :=
    tendsto_nhds_unique
      (sturmRealHeatLimitVector_tendsto lam hlam (s + u)
        (add_nonneg hs hu) f) hprod'
  simpa only [sturmRealHeatLimitCLM_apply, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply] using heq

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_apply
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_zero
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_add

end GegenbauerFock.Ultraspherical
