import Peters2024
import Mathlib.Topology.Homotopy.Path

/-! Homotopy-level refinement of the sampled paths in §§3–4. The
straight-line homotopy is relative to both endpoints; it does not assume
that arbitrary paths on a curved surface are homotopic. -/

namespace Peters2024

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Any two paths in a real normed space with equal endpoints admit an
explicit endpoint-preserving linear homotopy. -/
theorem real_normed_paths_homotopic {a b : E} (p q : Path a b) :
    p.Homotopic q := by
  refine ⟨{ toFun := fun x => p x.2 + (x.1 : ℝ) • (q x.2 - p x.2)
            continuous_toFun := ?_
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · exact (p.continuous.comp continuous_snd).add
      (continuous_subtype_val.comp continuous_fst |>.smul
        ((q.continuous.comp continuous_snd).sub (p.continuous.comp continuous_snd)))
  · intro t
    simp
  · intro t
    simp
  · intro s t ht
    rcases ht with ht | ht
    · rw [ht]
      simp
    · rw [Set.mem_singleton_iff] at ht
      rw [ht]
      simp

/-- A closed sampled image path in Euclidean coordinates is genuinely
null-homotopic relative to its basepoint. -/
theorem sampled_image_loop_nullhomotopic {a : E} (d : DiscreteArc a a) :
    d.path.Homotopic (Path.refl a) :=
  real_normed_paths_homotopic d.path (Path.refl a)

end

/-- The non-antipodal result 3.8 gives a loop with a verified relative
homotopy, not merely equality of its sampled endpoints. -/
theorem thm_3_8_nullhomotopic {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (n : ℕ) (f : X → Coordinates n) (hf : Continuous f)
    (a b : X) (he : f a = f b) :
    ∃ d : DiscreteArc a b, ∃ k : DiscreteArc (f a) (f a),
      (∀ t : unitInterval, k.path t = f (d.path t)) ∧
      k.path.Homotopic (Path.refl (f a)) := by
  obtain ⟨d, k, hk⟩ := thm_3_8 f hf a b he
  exact ⟨d, k, hk, sampled_image_loop_nullhomotopic k⟩

/-- The antipodal result 3.5 has the same refinement, retaining the
explicit classical Borsuk–Ulam premise until the upstream build passes. -/
theorem thm_3_5_nullhomotopic (n : ℕ) (hn : 1 ≤ n) (but : BorsukUlam n)
    (f : Sphere n → Coordinates n) (hf : Continuous f) :
    ∃ p : Sphere n, f p = f (-p) ∧
      ∃ d : DiscreteArc p (-p), ∃ k : DiscreteArc (f p) (f p),
      (∀ t : unitInterval, k.path t = f (d.path t)) ∧
      k.path.Homotopic (Path.refl (f p)) := by
  obtain ⟨p, hp, d, k, hk⟩ := thm_3_5 n hn but f hf
  exact ⟨p, hp, d, k, hk, sampled_image_loop_nullhomotopic k⟩

end Peters2024

#print axioms Peters2024.real_normed_paths_homotopic
#print axioms Peters2024.sampled_image_loop_nullhomotopic
#print axioms Peters2024.thm_3_8_nullhomotopic
#print axioms Peters2024.thm_3_5_nullhomotopic
