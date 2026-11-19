import BorsukCore
import HamSandwich.SphereOddDegree.BorsukUlam

/-! The classical dependency of the Filomat article is discharged using the
public HamSandwich proof at revision 76202dbbb6610ffcebbccfbf7a56f833a4c2a376.
The upstream proof is credited, not represented as a new proof of Borsuk–Ulam.
The bridge uses the continuous linear equivalence between Euclidean space
and the finite coordinate product, so the original statement is unchanged. -/

namespace Peters2024
open Set Metric
noncomputable section

/-- Theorem 1.1 in every dimension, including the trivial dimension zero. -/
theorem thm_1_1 (n : ℕ) : BorsukUlam n := by
  exact borsukUlam_of_euclidean (fun _ f => SphereOddDegree.borsuk_ulam f) n

/-- Theorem 1.4: no Borsuk–Ulam hypothesis remains. -/
theorem thm_1_4_closed (n : ℕ) (C : Fin (n+1) → Set (Sphere n))
    (hc : ∀ i, IsClosed (C i)) (cover : ∀ p, ∃ i, p ∈ C i) :
    ∃ i p, p ∈ C i ∧ -p ∈ C i := thm_1_4 n (thm_1_1 n) C hc cover

/-- Theorem 3.5: a sampled antipodal path maps to a loop. -/
theorem thm_3_5_closed (n : ℕ) (hn : 1 ≤ n)
    (f : Sphere n → Coordinates n) (hf : Continuous f) :
    ∃ p : Sphere n, f p = f (-p) ∧
      ∃ d : DiscreteArc p (-p), ∃ k : DiscreteArc (f p) (f p),
        ∀ t : unitInterval, k.path t = f (d.path t) :=
  thm_3_5 n hn (thm_1_1 n) f hf

theorem thm_5_4_closed (α : Sphere 2 → Coordinates 2) (hα : Continuous α) :
    ∃ p, α p = α (-p) := thm_5_4 (thm_1_1 2) α hα

theorem thm_5_5_closed (H : Sphere 2 → Coordinates 2) (hH : Continuous H) :
    ∃ p, H p = H (-p) := thm_5_5 (thm_1_1 2) H hH

/-- Conditional on continuity of the specified kernel, but not on an extra
topological axiom. No claim is made about existence of a physical propagator. -/
theorem thm_5_6_continuous_kernel_closed
    (K : Sphere 2 → Sphere 2 → Coordinates 2) (b : Sphere 2)
    (hK : Continuous (K b)) : ∃ a : Sphere 2,
      K b a = K b (-a) ∧ Nonempty (Path a b) ∧ Nonempty (Path b (-a)) :=
  thm_5_6_continuous_kernel (thm_1_1 2) K b hK

theorem thm_6_2_closed (Φ : Sphere 2 → Coordinates 2) (hΦ : Continuous Φ) :
    ∃ p, Φ p = Φ (-p) := thm_6_2 (thm_1_1 2) Φ hΦ

theorem cor_6_3_closed (Φ : Sphere 2 → Coordinates 2) (hΦ : Continuous Φ) :
    ∃ p : Sphere 2, Φ p = Φ (-p) ∧
      ∃ d : DiscreteArc p (-p), ∃ k : DiscreteArc (Φ p) (Φ p),
        ∀ t : unitInterval, k.path t = Φ (d.path t) :=
  cor_6_3 (thm_1_1 2) Φ hΦ

end
end Peters2024

#print axioms SphereOddDegree.borsuk_ulam
#print axioms Peters2024.thm_1_1
#print axioms Peters2024.thm_1_4_closed
#print axioms Peters2024.thm_3_5_closed
#print axioms Peters2024.thm_5_4_closed
#print axioms Peters2024.thm_5_5_closed
#print axioms Peters2024.thm_5_6_continuous_kernel_closed
#print axioms Peters2024.thm_6_2_closed
#print axioms Peters2024.cor_6_3_closed
