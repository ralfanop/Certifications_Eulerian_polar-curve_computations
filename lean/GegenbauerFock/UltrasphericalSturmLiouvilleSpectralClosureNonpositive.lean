import GegenbauerFock.UltrasphericalSturmLiouvilleSpectralClosureUniqueness
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# V007 — nonpositive closed spectral Sturm realization = polynomial closure

The graph-control hypothesis of SpectralClosureUniqueness is discharged
using only the nonpositive quadratic form of an actual closed extension.
Consequently every closed, nonpositive extension of the genuine real
polynomial Sturm operator is its graph closure, by the already certified
dense range of I - L on polynomials.

The theorem does not claim to have constructed a specific diagonal
eigenbasis representation. That identification remains a separate bridge.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The shifted resolvent graph inequality follows from nonpositive
quadratic form: ‖u‖ ≤ ‖u - Su‖ and ‖Su‖ ≤ 2‖u - Su‖. -/
theorem sturmReal_closed_nonpositive_shift_graph_bound
    (lam : ℝ) (S : SturmH lam →ₗ.[ℝ] SturmH lam)
    (hNonpos : ∀ u : S.domain,
      inner ℝ (S u) (u : SturmH lam) ≤ 0)
    (x y : S.domain) :
    dist (((x : SturmH lam), S x) : SturmH lam × SturmH lam)
         (((y : SturmH lam), S y) : SturmH lam × SturmH lam) ≤
      3 * dist ((x : SturmH lam) - S x)
               ((y : SturmH lam) - S y) := by
  let w : S.domain := x - y
  have hw : (w : SturmH lam) =
      (x : SturmH lam) - (y : SturmH lam) := rfl
  have hSw : S w = S x - S y := S.map_sub x y
  have hneg : inner ℝ (w : SturmH lam) (S w) ≤ 0 := by
    rw [real_inner_comm]
    exact hNonpos w
  have hsq :
      ‖(w : SturmH lam)‖ ^ 2 ≤
        ‖(w : SturmH lam) - S w‖ ^ 2 := by
    have he := norm_sub_sq_real (w : SturmH lam) (S w)
    nlinarith [sq_nonneg (‖S w‖)]
  have hnorm :
      ‖(w : SturmH lam)‖ ≤
        ‖(w : SturmH lam) - S w‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hImg :
      ‖S w‖ ≤ 2 * ‖(w : SturmH lam) - S w‖ := by
    have ht := norm_sub_le (w : SturmH lam)
      ((w : SturmH lam) - S w)
    have hs : (w : SturmH lam) -
        ((w : SturmH lam) - S w) = S w := by abel
    rw [hs] at ht
    linarith
  have hShift :
      ((x : SturmH lam) - S x) -
        ((y : SturmH lam) - S y) =
      (w : SturmH lam) - S w := by
    rw [hw, hSw]
    abel
  have hd1 :
      dist (x : SturmH lam) (y : SturmH lam) ≤
        dist ((x : SturmH lam) - S x)
             ((y : SturmH lam) - S y) := by
    calc
      _ = ‖(w : SturmH lam)‖ := by
        rw [dist_eq_norm, hw]
      _ ≤ ‖(w : SturmH lam) - S w‖ := hnorm
      _ = _ := by rw [dist_eq_norm, hShift]
  have hd2 :
      dist (S x) (S y) ≤
        2 * dist ((x : SturmH lam) - S x)
                 ((y : SturmH lam) - S y) := by
    calc
      _ = ‖S w‖ := by rw [dist_eq_norm, hSw]
      _ ≤ 2 * ‖(w : SturmH lam) - S w‖ := hImg
      _ = _ := by rw [dist_eq_norm, hShift]
  rw [Prod.dist_eq]
  have hd0 : 0 ≤
      dist ((x : SturmH lam) - S x)
           ((y : SturmH lam) - S y) := dist_nonneg
  exact max_le (by linarith) (by linarith)

/-- NONCONDITIONAL on graph-core approximations: only closedness,
extension of the concrete polynomial operator, and spectral
nonpositivity are required. Dense shifted polynomial range is already
proved in V007. Thus equality holds as operators (domains and actions). -/
theorem sturmRealPartialOperator_spectral_eq_closure_of_nonpositive
    (lam : ℝ) (hlam : 0 < lam)
    (S : SturmH lam →ₗ.[ℝ] SturmH lam)
    (hSclosed : S.IsClosed)
    (hExt : sturmRealPartialOperator lam hlam ≤ S)
    (hNonpos : ∀ u : S.domain,
      inner ℝ (S u) (u : SturmH lam) ≤ 0) :
    (sturmRealPartialOperator lam hlam).closure = S :=
  sturmRealPartialOperator_spectral_eq_closure_of_shift_graph_bound
    lam hlam S hSclosed hExt
      (sturmReal_closed_nonpositive_shift_graph_bound lam S hNonpos)

/-- The domain of the closed Sturm operator is precisely the domain
of any closed nonpositive spectral extension. -/
theorem sturmRealPartialOperator_spectral_domain_eq_of_nonpositive
    (lam : ℝ) (hlam : 0 < lam)
    (S : SturmH lam →ₗ.[ℝ] SturmH lam)
    (hSclosed : S.IsClosed)
    (hExt : sturmRealPartialOperator lam hlam ≤ S)
    (hNonpos : ∀ u : S.domain,
      inner ℝ (S u) (u : SturmH lam) ≤ 0) :
    (sturmRealPartialOperator lam hlam).closure.domain = S.domain := by
  exact congrArg LinearPMap.domain
    (sturmRealPartialOperator_spectral_eq_closure_of_nonpositive
      lam hlam S hSclosed hExt hNonpos)

/-- The actual weighted-L² polynomial vectors are a graph core of
EVERY closed nonpositive spectral realization extending the true
polynomial differential operator. This follows from operator equality,
rather than being assumed in the spectral construction. -/
theorem sturmRealPartialOperator_polynomials_spectral_core_of_nonpositive
    (lam : ℝ) (hlam : 0 < lam)
    (S : SturmH lam →ₗ.[ℝ] SturmH lam)
    (hSclosed : S.IsClosed)
    (hExt : sturmRealPartialOperator lam hlam ≤ S)
    (hNonpos : ∀ u : S.domain,
      inner ℝ (S u) (u : SturmH lam) ≤ 0) :
    S.HasCore (sturmRealPartialOperator lam hlam).domain := by
  rw [← sturmRealPartialOperator_spectral_eq_closure_of_nonpositive
    lam hlam S hSclosed hExt hNonpos]
  exact LinearPMap.closureHasCore (sturmRealPartialOperator lam hlam)

#print axioms GegenbauerFock.Ultraspherical.sturmReal_closed_nonpositive_shift_graph_bound
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_spectral_eq_closure_of_nonpositive
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_spectral_domain_eq_of_nonpositive
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_polynomials_spectral_core_of_nonpositive

end GegenbauerFock.Ultraspherical
