import Mathlib

/-! M14 §7.4 — abstract closed-form resolvent bridge.
The form Hilbert space V and its bounded inclusion J into H are supplied.
This does not construct the magnetic form or prove its compact embedding.
Classical representation by a form-space map; cf. Hassi–de Snoo,
Ann. Funct. Anal. 15 (2024), 78, §2 and (4.1), Theorem 4.1.
The exact form-space inverse construction is also Kaltenbäck–Winkler–Woracek,
Symmetric Relations of Finite Negativity, Operator Theory 162, pp. 191–210,
Theorem 3.5 (p. 195), with S_F = (ιι*)⁻¹ + m I.
-/
noncomputable section
open scoped InnerProductSpace
namespace Manuscript14.FriedrichsForm

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded resolvent of the form energy, represented in H. -/
def formResolvent (J : V →L[ℂ] H) : H →L[ℂ] H := J.comp J.adjoint

/-- Variational solution exists and is unique in the form Hilbert space. -/
theorem variational_unique (J : V →L[ℂ] H) (f : H) :
    ∃! u : V, ∀ v : V, ⟪u, v⟫_ℂ = ⟪f, J v⟫_ℂ := by
  refine ⟨J.adjoint f, ?_, ?_⟩
  · intro v
    exact J.adjoint_inner_left v f
  · intro u hu
    have hh : ⟪u - J.adjoint f, u - J.adjoint f⟫_ℂ = 0 := by
      rw [inner_sub_left, hu, J.adjoint_inner_left, sub_self]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hh)

theorem resolvent_selfAdjoint (J : V →L[ℂ] H) :
    IsSelfAdjoint (formResolvent J) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', formResolvent,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

/-- The resolvent is positive, with its quadratic form given by J*. -/
theorem resolvent_quadratic (J : V →L[ℂ] H) (f : H) :
    ⟪f, formResolvent J f⟫_ℂ = ⟪J.adjoint f, J.adjoint f⟫_ℂ := by
  exact (J.adjoint_inner_left (J.adjoint f) f).symm

/-- An actual compact operator, not just a scalar surrogate. -/
theorem resolvent_compact (J : V →L[ℂ] H) (h : IsCompactOperator J) :
    IsCompactOperator (formResolvent J) := by
  exact h.comp_clm J.adjoint

theorem adjoint_injective_of_dense (J : V →L[ℂ] H) (hJ : DenseRange J) :
    Function.Injective J.adjoint := by
  intro x y h
  have hz : J.adjoint (x-y) = 0 := by rw [map_sub, h, sub_self]
  have hh : ∀ v : V, ⟪x-y, J v⟫_ℂ = 0 := by
    intro v
    rw [← J.adjoint_inner_left, hz, inner_zero_left]
  have hs : ⟪x-y, x-y⟫_ℂ = 0 :=
    hJ.induction_on (p := fun t : H => ⟪x-y, t⟫_ℂ = 0) (x-y)
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const) hh
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hs)

theorem resolvent_injective (J : V →L[ℂ] H) (hJ : DenseRange J) :
    Function.Injective (formResolvent J) := by
  exact (ContinuousLinearMap.self_comp_adjoint_injective_iff J).2
    (adjoint_injective_of_dense J hJ)

/-- In the ambient space, the variational problem identifies exactly the
    graph with reversed coordinates of the bounded resolvent. -/
theorem inverse_graph_iff (J : V →L[ℂ] H) (f w : H) :
    w = formResolvent J f ↔
      ∃ u : V, w = J u ∧ ∀ v : V, ⟪u, v⟫_ℂ = ⟪f, J v⟫_ℂ := by
  constructor
  · intro h
    exact ⟨J.adjoint f, h, fun v => J.adjoint_inner_left v f⟩
  · rintro ⟨u, hw, hu⟩
    obtain ⟨a, ha, huniq⟩ := variational_unique J f
    have he : u = J.adjoint f := (huniq u hu).trans
      (huniq (J.adjoint f) (fun v => J.adjoint_inner_left v f)).symm
    rw [hw, he]
    rfl

#print axioms variational_unique
#print axioms resolvent_selfAdjoint
#print axioms resolvent_quadratic
#print axioms resolvent_compact
#print axioms adjoint_injective_of_dense
#print axioms resolvent_injective
#print axioms inverse_graph_iff
end Manuscript14.FriedrichsForm
