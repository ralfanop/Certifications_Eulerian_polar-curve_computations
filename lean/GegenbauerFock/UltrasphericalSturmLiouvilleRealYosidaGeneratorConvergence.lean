import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaGenerator

/-!
# V007 — Yosida bounded generators converge to the genuine closed Sturm action

For every x in the domain of the actual closed unbounded real
ultraspherical Sturm operator A, the bounded Yosida approximation
A_t = t² (tI - A)⁻¹ - t I satisfies

  A_t x = (tR_t) (A x),  ‖A_t x‖ ≤ ‖A x‖,  A_t x → A x.

All statements use the genuine weighted L² realization and the
previously kernel-checked strong convergence of tR_t on the whole
Hilbert space; no spectral diagonalization is needed.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Exact agreement of the bounded Yosida generator with the
scaled resolvent of the actual closed unbounded Sturm action. -/
theorem sturmRealYosidaGenerator_on_closed_domain
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    sturmRealYosidaGenerator lam t hlam ht (x : SturmH lam) =
      t • sturmRealPositiveResolventFullCLM lam t hlam ht
        ((sturmRealPartialOperator lam hlam).closure x) := by
  rw [sturmRealYosidaGenerator_apply,
    sturmRealYosidaContraction_on_closed_domain lam t hlam ht x]

/-- Uniform bound of the Yosida generator on the genuine closed
domain, in terms of the graph-action norm. -/
theorem sturmRealYosidaGenerator_closed_domain_norm_le
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    ‖sturmRealYosidaGenerator lam t hlam ht (x : SturmH lam)‖ ≤
      ‖(sturmRealPartialOperator lam hlam).closure x‖ := by
  rw [sturmRealYosidaGenerator_on_closed_domain lam t hlam ht x]
  exact sturmRealYosidaContraction_norm_le lam t hlam ht
    ((sturmRealPartialOperator lam hlam).closure x)

/-- Strong convergence A_t x → A x in the true real weighted L²
space, for EVERY x in the canonical closed Sturm domain. -/
theorem sturmRealYosidaGenerator_closed_domain_strong_approximation
    (lam : ℝ) (hlam : 0 < lam)
    (x : (sturmRealPartialOperator lam hlam).closure.domain)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ T : ℝ, 0 < T ∧
      ∀ t : ℝ, T ≤ t → ∀ ht : 0 < t,
        ‖sturmRealYosidaGenerator lam t hlam ht (x : SturmH lam) -
            (sturmRealPartialOperator lam hlam).closure x‖ < eps := by
  obtain ⟨T, hT, happrox⟩ :=
    sturmRealYosidaContraction_strong_approximation
      lam hlam ((sturmRealPartialOperator lam hlam).closure x) eps heps
  refine ⟨T, hT, ?_⟩
  intro t hlarge ht
  rw [sturmRealYosidaGenerator_on_closed_domain lam t hlam ht x]
  exact happrox t hlarge ht

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaGenerator_on_closed_domain
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaGenerator_closed_domain_norm_le
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaGenerator_closed_domain_strong_approximation

end GegenbauerFock.Ultraspherical
