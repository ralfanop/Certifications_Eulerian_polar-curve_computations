import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaContraction
import GegenbauerFock.UltrasphericalSturmLiouvilleRealClosedDomainDense

/-!
# V007 — quantitative strong Yosida approximation on ALL real weighted L²

Using genuine density of the canonical Sturm closed domain and the
globally contractive scaled positive resolvent, the domain error estimate
extends to arbitrary L² inputs with an explicit quantitative inequality.

No diagonalization, Gegenbauer orthonormal-basis completeness or
pre-existing strongly continuous semigroup is assumed.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The full-space approximation error is bounded by twice the
distance to any closed-domain vector plus the domain O(1/t) error. -/
theorem sturmRealYosidaContraction_dense_error_bound
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    ‖t • sturmRealPositiveResolventFullCLM lam t hlam ht f - f‖ ≤
      2 * ‖f - (x : SturmH lam)‖ +
        ‖(sturmRealPartialOperator lam hlam).closure x‖ / t := by
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  have hcon :
      ‖t • R f - t • R (x : SturmH lam)‖ ≤
        ‖f - (x : SturmH lam)‖ := by
    simpa only [map_sub, smul_sub] using
      (sturmRealYosidaContraction_norm_le
        lam t hlam ht (f - (x : SturmH lam)))
  have hcore :
      ‖t • R (x : SturmH lam) - (x : SturmH lam)‖ ≤
        ‖(sturmRealPartialOperator lam hlam).closure x‖ / t :=
    sturmRealYosidaContraction_closed_domain_error_le lam t hlam ht x
  have hflip :
      ‖(x : SturmH lam) - f‖ = ‖f - (x : SturmH lam)‖ :=
    norm_sub_rev _ _
  have htri :
      ‖t • R f - f‖ ≤
        ‖t • R f - t • R (x : SturmH lam)‖ +
          ‖t • R (x : SturmH lam) - (x : SturmH lam)‖ +
            ‖(x : SturmH lam) - f‖ := by
    calc
      ‖t • R f - f‖ =
          ‖(t • R f - t • R (x : SturmH lam)) +
            (t • R (x : SturmH lam) - (x : SturmH lam)) +
            ((x : SturmH lam) - f)‖ := by congr 1; abel
      _ ≤ ‖t • R f - t • R (x : SturmH lam)‖ +
          ‖t • R (x : SturmH lam) - (x : SturmH lam)‖ +
          ‖(x : SturmH lam) - f‖ := by
        have h1 := norm_add_le
          (t • R f - t • R (x : SturmH lam))
          (t • R (x : SturmH lam) - (x : SturmH lam))
        have h2 := norm_add_le
          ((t • R f - t • R (x : SturmH lam)) +
            (t • R (x : SturmH lam) - (x : SturmH lam)))
          ((x : SturmH lam) - f)
        linarith
  calc
    ‖t • R f - f‖ ≤
      ‖t • R f - t • R (x : SturmH lam)‖ +
        ‖t • R (x : SturmH lam) - (x : SturmH lam)‖ +
        ‖(x : SturmH lam) - f‖ := htri
    _ ≤ 2 * ‖f - (x : SturmH lam)‖ +
        ‖(sturmRealPartialOperator lam hlam).closure x‖ / t := by
      rw [hflip]
      linarith

/-- Epsilon-uniform-for-large-t form of strong convergence:
for EVERY weighted real L² vector, tR_t f approaches f as t→+∞.
The positive shift parameter and its proof are kept explicit. -/
theorem sturmRealYosidaContraction_strong_approximation
    (lam : ℝ) (hlam : 0 < lam) (f : SturmH lam)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ T : ℝ, 0 < T ∧
      ∀ t : ℝ, T ≤ t → ∀ ht : 0 < t,
        ‖t • sturmRealPositiveResolventFullCLM lam t hlam ht f - f‖ <
          eps := by
  let A := (sturmRealPartialOperator lam hlam).closure
  have hf : f ∈ closure (A.domain : Set (SturmH lam)) := by
    rw [← Submodule.topologicalClosure_coe]
    change f ∈ (sturmRealPartialOperator lam hlam).closure.domain.topologicalClosure
    rw [sturmRealPartialOperator_closure_dense_domain lam hlam]
    trivial
  obtain ⟨g, hg, hdist⟩ :=
    (Metric.mem_closure_iff.mp hf) (eps / 4) (by positivity)
  let x : A.domain := ⟨g, hg⟩
  have hnear : ‖f - (x : SturmH lam)‖ < eps / 4 := by
    simpa only [dist_eq_norm] using hdist
  let T : ℝ := 1 + 4 * ‖A x‖ / eps
  refine ⟨T, by dsimp [T]; positivity, ?_⟩
  intro t htlarge ht
  have hbelow : ‖A x‖ / t ≤ eps / 4 := by
    apply (div_le_iff₀ ht).2
    have haux : 4 * ‖A x‖ / eps ≤ t := by
      dsimp [T] at htlarge
      linarith
    have hmul : 4 * ‖A x‖ ≤ t * eps :=
      (div_le_iff₀ heps).mp haux
    nlinarith
  have hb := sturmRealYosidaContraction_dense_error_bound
    lam t hlam ht f x
  have hAx : A x = (sturmRealPartialOperator lam hlam).closure x := rfl
  rw [← hAx] at hb
  linarith

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaContraction_dense_error_bound
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaContraction_strong_approximation

end GegenbauerFock.Ultraspherical
