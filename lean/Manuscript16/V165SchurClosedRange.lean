import Manuscript16.V165TypedGraphSchur

/-! M16 v16.5 §13, typed closed-range and bijectivity reduction.
Assumes L:D ≃L X as in #366. Complements #374 (kernel). No compact
perturbation/Atkinson/Schatten or det4 criterion asserted. -/
namespace Manuscript16.V165GraphSchur

variable {𝕜 P D X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem mem_block_range_iff (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) (f : P) (g : X) :
    (f,g) ∈ Set.range (block A B C L) ↔
      f - B (L.symm g) ∈ Set.range (schur A B C L) := by
  constructor
  · rintro ⟨⟨p,x⟩,h⟩
    exact ⟨p, ((block_equation_iff A B C L p f x g).mp h).1⟩
  · rintro ⟨p,h⟩
    exact ⟨(p,L.symm (g-C p)),
      (block_equation_iff A B C L p f (L.symm (g-C p)) g).mpr ⟨h,rfl⟩⟩

/-- Actual topological closed-range equivalence for the continuous maps
on P×D and P×X. Does not assume either range is closed. -/
theorem block_range_closed_iff (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) :
    IsClosed (Set.range (block A B C L)) ↔ IsClosed (Set.range (schur A B C L)) := by
  constructor
  · intro hc
    have he : Set.range (schur A B C L) =
        (fun f : P => (f,(0:X))) ⁻¹' Set.range (block A B C L) := by
      ext f
      change f ∈ Set.range (schur A B C L) ↔ (f,(0:X)) ∈ Set.range (block A B C L)
      rw [mem_block_range_iff]
      simp
    rw [he]
    exact hc.preimage (by fun_prop)
  · intro hc
    have he : Set.range (block A B C L) =
        (fun z : P × X => z.1 - B (L.symm z.2)) ⁻¹' Set.range (schur A B C L) := by
      ext z
      rcases z with ⟨f,g⟩
      exact mem_block_range_iff A B C L f g
    rw [he]
    exact hc.preimage (by fun_prop)

theorem block_surjective_iff (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) :
    Function.Surjective (block A B C L) ↔ Function.Surjective (schur A B C L) := by
  constructor
  · intro h f
    obtain ⟨⟨p,x⟩,hp⟩ := h (f,0)
    have hr := ((block_equation_iff A B C L p f x 0).mp hp).1
    exact ⟨p,by simpa using hr⟩
  · rintro h ⟨f,g⟩
    obtain ⟨p,hp⟩ := h (f - B (L.symm g))
    exact ⟨(p,L.symm (g-C p)),
      (block_equation_iff A B C L p f (L.symm (g-C p)) g).mpr ⟨hp,rfl⟩⟩

theorem block_injective_iff (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) :
    Function.Injective (block A B C L) ↔ Function.Injective (schur A B C L) := by
  constructor
  · intro h p q hpq
    have hp : block A B C L (p,L.symm (0-C p)) = (schur A B C L p,0) :=
      (block_equation_iff A B C L p (schur A B C L p) (L.symm (0-C p)) 0).mpr
        ⟨by simp,rfl⟩
    have hq : block A B C L (q,L.symm (0-C q)) = (schur A B C L p,0) :=
      (block_equation_iff A B C L q (schur A B C L p) (L.symm (0-C q)) 0).mpr
        ⟨by simpa using hpq.symm,rfl⟩
    exact congrArg Prod.fst (h (hp.trans hq.symm))
  · rintro h ⟨p,x⟩ ⟨q,y⟩ he
    let f := (block A B C L (q,y)).1
    let g := (block A B C L (q,y)).2
    have hq : block A B C L (q,y) = (f,g) := by rfl
    have hp : block A B C L (p,x) = (f,g) := he.trans hq
    have h1 := (block_equation_iff A B C L p f x g).mp hp
    have h2 := (block_equation_iff A B C L q f y g).mp hq
    have hpq := h (h1.1.trans h2.1.symm)
    subst q
    exact Prod.ext rfl (h1.2.trans h2.2.symm)

theorem block_bijective_iff (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) :
    Function.Bijective (block A B C L) ↔ Function.Bijective (schur A B C L) := by
  exact and_congr (block_injective_iff A B C L) (block_surjective_iff A B C L)

#print axioms Manuscript16.V165GraphSchur.mem_block_range_iff
#print axioms Manuscript16.V165GraphSchur.block_range_closed_iff
#print axioms Manuscript16.V165GraphSchur.block_surjective_iff
#print axioms Manuscript16.V165GraphSchur.block_injective_iff
#print axioms Manuscript16.V165GraphSchur.block_bijective_iff
end Manuscript16.V165GraphSchur
