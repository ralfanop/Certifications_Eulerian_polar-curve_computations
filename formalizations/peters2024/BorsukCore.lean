import Peters2024

/-! The transfer between the article's finite coordinate codomain and Euclidean
space is proved separately so that it can be checked without compiling the
external odd-degree library. Its general topological premise is explicit. -/

namespace Peters2024
open Set Metric
noncomputable section

def EuclideanBorsukUlam : Prop :=
  ∀ (n : ℕ) (f : C(Sphere (n+1), EuclideanSpace ℝ (Fin (n+1)))),
    ∃ p : Sphere (n+1), f p = f (-p)

theorem borsukUlam_zero : BorsukUlam 0 := by
  intro f _hf
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin 1))
    (x := 0) (r := 1)).mpr zero_le_one
  refine ⟨⟨x, hx⟩, ?_⟩
  exact Subsingleton.elim _ _

/-- Independent dimension-one proof via the intermediate value theorem. -/
theorem borsukUlam_one : BorsukUlam 1 := by
  intro f hf
  letI := sphere_pathConnected 1 (by decide)
  let p : Sphere 1 := Classical.choice (PathConnectedSpace.nonempty : Nonempty (Sphere 1))
  let γ := PathConnectedSpace.somePath p (-p)
  let g : ℝ → ℝ := fun t => f (γ.extend t) 0 - f (-γ.extend t) 0
  have hγ : Continuous γ.extend := γ.continuous_extend
  have hcoord : Continuous (fun x : Sphere 1 => f x 0) :=
    (continuous_apply (0 : Fin 1)).comp hf
  have hg : Continuous g := (hcoord.comp hγ).sub (hcoord.comp (hγ.neg))
  have h0 : g 0 = f p 0 - f (-p) 0 := by simp [g, γ]
  have h1 : g 1 = -(f p 0 - f (-p) 0) := by simp [g, γ]
  have hmid : (0 : ℝ) ∈ uIcc (g 0) (g 1) := by
    rw [h0, h1]
    rcases le_total (f p 0 - f (-p) 0) (-(f p 0 - f (-p) 0)) with h | h
    · rw [uIcc_of_le h]
      exact ⟨by linarith, by linarith⟩
    · rw [uIcc_of_ge h]
      exact ⟨by linarith, by linarith⟩
  obtain ⟨t, _, ht⟩ := intermediate_value_uIcc hg.continuousOn hmid
  refine ⟨γ.extend t, ?_⟩
  funext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  exact sub_eq_zero.mp ht

/-- No mathematical assumption is hidden in the codomain identification. -/
theorem borsukUlam_of_euclidean (h : EuclideanBorsukUlam) (n : ℕ) : BorsukUlam n := by
  cases n with
  | zero => exact borsukUlam_zero
  | succ n =>
    intro f hf
    let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ (fun _ : Fin (n+1) => ℝ)
    let g : C(Sphere (n+1), EuclideanSpace ℝ (Fin (n+1))) :=
      ⟨e.symm ∘ f, e.symm.continuous.comp hf⟩
    obtain ⟨p, hp⟩ := h n g
    exact ⟨p, e.symm.injective hp⟩

end
end Peters2024

#print axioms Peters2024.borsukUlam_zero
#print axioms Peters2024.borsukUlam_one
#print axioms Peters2024.borsukUlam_of_euclidean
