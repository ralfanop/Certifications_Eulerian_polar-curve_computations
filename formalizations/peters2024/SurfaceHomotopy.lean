import Peters2024
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! Relative homotopies for the underlying continuous paths on a simply
connected surface. No identification of simple connectedness with absence
of self-intersections is used. -/
namespace Peters2024

variable {X : Type*} [TopologicalSpace X]

/-- Any two sampled arcs with common endpoints in a simply connected space
have endpoint-preserving homotopic realizations. -/
theorem sampled_arcs_homotopic [SimplyConnectedSpace X] {a b : X}
    (d e : DiscreteArc a b) : d.path.Homotopic e.path :=
  SimplyConnectedSpace.paths_homotopic d.path e.path

/-- A sampled loop on a simply connected surface is contractible relative
to its basepoint. -/
theorem sampled_surface_loop_nullhomotopic [SimplyConnectedSpace X] {a : X}
    (d : DiscreteArc a a) : d.path.Homotopic (Path.refl a) :=
  SimplyConnectedSpace.paths_homotopic d.path (Path.refl a)

/-- The reversal loop in Theorem 3.2 is null-homotopic in any topological
space, even without a simply connectedness assumption. -/
theorem thm_3_2_nullhomotopic {a b : X} (d : DiscreteArc a b) :
    (thm_3_2 d).path.Homotopic (Path.refl a) := by
  change (d.path.trans d.path.symm).Homotopic (Path.refl a)
  exact Path.Homotopic.trans_symm d.path

end Peters2024

#print axioms Peters2024.sampled_arcs_homotopic
#print axioms Peters2024.sampled_surface_loop_nullhomotopic
#print axioms Peters2024.thm_3_2_nullhomotopic
