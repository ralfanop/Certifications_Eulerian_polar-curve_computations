import Mathlib

/-! M14 §7.4, author TeX SHA256
b0aba7205b0e915ff49512ffd66f4deeaef29d2de766293be58c090820aeca68.
Follow-up to #347: inverse of a bounded injective self-adjoint resolvent
as a genuine densely defined LinearPMap, not only a graph relation.
Cf. Hassi–de Snoo (2024), Theorem 4.1, and
Kaltenbäck–Winkler–Woracek (2006), Theorem 3.5.
The particular magnetic form space, its compact embedding and the
semiclassical trace comparison still require independent proofs. -/
noncomputable section
open scoped InnerProductSpace
namespace Manuscript14.FriedrichsInverse

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

def full (R : H →L[ℂ] H) : H →ₗ.[ℂ] H :=
  R.toLinearMap.toPMap ⊤

def inverseOperator (R : H →L[ℂ] H) : H →ₗ.[ℂ] H :=
  (full R).inverse

theorem full_ker (R : H →L[ℂ] H) (hR : Function.Injective R) :
    (full R).ker = ⊥ := by
  apply LinearPMap.ker_eq_bot.mpr
  intro x y h
  apply Subtype.ext
  exact hR h

theorem inverse_graph_iff (R : H →L[ℂ] H) (hR : Function.Injective R)
    (w f : H) :
    (w,f) ∈ (inverseOperator R).graph ↔ w = R f := by
  rw [inverseOperator, LinearPMap.inverse_graph (full_ker R hR)]
  simp only [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap,
    LinearEquiv.symm_prodComm, LinearEquiv.coe_coe, LinearEquiv.prodComm_apply,
    LinearPMap.mem_graph_iff, Prod.swap]
  constructor
  · rintro ⟨z, hz, hw⟩
    change (z : H) = f at hz
    change R (z : H) = w at hw
    rw [← hz]
    exact hw.symm
  · intro h
    exact ⟨⟨f, Submodule.mem_top⟩, rfl, h.symm⟩

theorem inverse_domain (R : H →L[ℂ] H) (hR : Function.Injective R) :
    ((inverseOperator R).domain : Set H) = Set.range R := by
  ext x
  change x ∈ (inverseOperator R).domain ↔ ∃ f, R f = x
  rw [LinearPMap.mem_domain_iff]
  simp only [inverse_graph_iff R hR]
  exact exists_congr (fun f => eq_comm)

theorem inverse_domain_dense (R : H →L[ℂ] H) (hR : Function.Injective R)
    (hs : IsSelfAdjoint R) : Dense ((inverseOperator R).domain : Set H) := by
  rw [inverse_domain R hR]
  have hk : R.ker = ⊥ := LinearMap.ker_eq_bot.mpr hR
  have ha := ContinuousLinearMap.isSelfAdjoint_iff'.mp hs
  have hc := R.orthogonal_ker
  rw [hk, ha] at hc
  change Dense (R.range : Set H)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  simpa using hc.symm

/-- Equality with the actual unbounded adjoint on the actual graph domain. -/
theorem inverse_selfAdjoint (R : H →L[ℂ] H) (hR : Function.Injective R)
    (hs : IsSelfAdjoint R) :
    (inverseOperator R).adjoint = inverseOperator R := by
  have hd := inverse_domain_dense R hR hs
  have ha := ContinuousLinearMap.isSelfAdjoint_iff'.mp hs
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd]
  ext p
  rcases p with ⟨w,f⟩
  rw [Submodule.mem_adjoint_iff, inverse_graph_iff R hR]
  constructor
  · intro h
    apply ext_inner_left ℂ
    intro b
    have hh := h (R b) b ((inverse_graph_iff R hR _ _).2 rfl)
    change ⟪b,w⟫_ℂ - ⟪R b,f⟫_ℂ = 0 at hh
    rw [← R.adjoint_inner_right, ha] at hh
    exact sub_eq_zero.mp hh
  · intro hw
    intro a b hab
    have hab' := (inverse_graph_iff R hR a b).1 hab
    change ⟪b,w⟫_ℂ - ⟪a,f⟫_ℂ = 0
    rw [hw, hab', ← R.adjoint_inner_right, ha, sub_self]

theorem inverse_closed (R : H →L[ℂ] H) (hR : Function.Injective R)
    (hs : IsSelfAdjoint R) : (inverseOperator R).IsClosed := by
  have hd := inverse_domain_dense R hR hs
  have hc := LinearPMap.adjoint_isClosed hd
  rw [inverse_selfAdjoint R hR hs] at hc
  exact hc

/-- The inverse solves the actual graph equation for every ambient vector. -/
theorem inverse_solves (R : H →L[ℂ] H) (hR : Function.Injective R) (f : H) :
    ∃ w : (inverseOperator R).domain,
      (w : H) = R f ∧ inverseOperator R w = f := by
  have hm := (inverse_graph_iff R hR (R f) f).2 rfl
  exact (LinearPMap.mem_graph_iff (inverseOperator R)).1 hm

/-- For a form resolvent J J*, the inverse has the positive form quadratic
identity on its true domain. Injectivity is the result of #347 for dense J. -/
theorem inverse_form_quadratic (J : V →L[ℂ] H)
    (hi : Function.Injective (J.comp J.adjoint))
    (w : (inverseOperator (J.comp J.adjoint)).domain) :
    ⟪inverseOperator (J.comp J.adjoint) w, (w : H)⟫_ℂ =
      ⟪J.adjoint (inverseOperator (J.comp J.adjoint) w),
        J.adjoint (inverseOperator (J.comp J.adjoint) w)⟫_ℂ := by
  have hw := (inverse_graph_iff (J.comp J.adjoint) hi _ _).1
    ((inverseOperator (J.comp J.adjoint)).mem_graph w)
  rw [hw]
  exact (J.adjoint_inner_left _ _).symm

#print axioms full_ker
#print axioms inverse_graph_iff
#print axioms inverse_domain
#print axioms inverse_domain_dense
#print axioms inverse_selfAdjoint
#print axioms inverse_closed
#print axioms inverse_solves
#print axioms inverse_form_quadratic
end Manuscript14.FriedrichsInverse
