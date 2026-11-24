import SharedCore.FredholmAtkinson
import Manuscript16.V165TypedGraphSchur

/-!
# M16 §13, `thm:dirac-maxwell-obstruction-164` (i)–(ii): Fredholm property and index

Typed graph-domain setting of `eq:mixed-factor-164` (`Manuscript16.V165GraphSchur`):
`P` is the resonant space, `D` the graph-norm domain, `X` the ambient space, and
`𝒜 = block A B C L : P × D →L P × X` with `A = A_P`, `L : D ≃L X`.

This file proves, with Mathlib's `ContinuousLinearMap.IsFredholm` and
`LinearMap.index` (no ad hoc Fredholm predicate):

* the diagonal operator `diag(F, L) = F.prodMap L` with `L : D ≃L X` is Fredholm iff
  `F` is, with `ker diag(F, L) ≃ ker F` (the second component vanishes) and
  `coker diag(F, L) ≃ coker F` (actual linear equivalences of quotient spaces),
  hence `ind diag(F, L) = ind F`;
* through `V165GraphSchur.typed_factorization`, `𝒜` is Fredholm iff the Schur map
  `F = A_P - B L⁻¹ C` is, and then `ind 𝒜 = ind F`;
* if the Schur correction `K = B L⁻¹ C` is compact and `P` is a complete complex
  inner-product space, `𝒜` is Fredholm iff `A_P` is, and then `ind 𝒜 = ind A_P`
  (`SharedCore.FredholmAtkinson.index_add_compact`, PR #469, reused, not duplicated).

Explicit premises of the final theorem: the continuous linear equivalence
`L : D ≃L X` and the compactness of `B L⁻¹ C`. Their derivation for the concrete
mixed Maxwell–Dirac operators (graph space of `L₀ = W_R ⊕ D₃`, Neumann
construction of `L` from `L₀`, compactness of `L⁻¹` from the Schatten estimate)
is NOT formalized here. No `det₄` statement is made.
-/

noncomputable section

namespace Manuscript16.DiracMaxwellObstructionIndex20261124

open ContinuousLinearMap
open scoped LinearMap.FiniteRangeSetoid

section Diagonal

variable {𝕜 E F D X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

omit [CompleteSpace 𝕜] in
/-- Finite-range equivalence in the first diagonal entry passes to the product map. -/
theorem prodMap_equiv_left {f f' : E →ₗ[𝕜] F} (h : f ≈ f') (g : D →ₗ[𝕜] X) :
    f.prodMap g ≈ f'.prodMap g := by
  rw [LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange] at h ⊢
  have he : f.prodMap g - f'.prodMap g =
      ((LinearMap.inl 𝕜 F X) ∘ₗ (f - f')) ∘ₗ LinearMap.fst 𝕜 E D := by
    apply LinearMap.ext
    rintro ⟨e, d⟩
    simp
  rw [he]
  exact (h.comp_left _).comp_right _

/-- If `F` is Fredholm and `L` is a continuous linear equivalence, then
`diag(F, L) = F.prodMap L` is Fredholm: `G.prodMap L⁻¹` is a quasi-inverse
for any quasi-inverse `G` of `F`. -/
theorem isFredholm_prodMap_of_isFredholm (T : E →L[𝕜] F) (L : D ≃L[𝕜] X)
    (hT : T.IsFredholm) : (T.prodMap (L : D →L[𝕜] X)).IsFredholm := by
  obtain ⟨G, hG⟩ := hT.exists_isQuasiInverse
  refine IsFredholm.of_isQuasiInverse (v := G.prodMap (L.symm : X →L[𝕜] D)) ⟨?_, ?_⟩
  · have hc : ((G.prodMap (L.symm : X →L[𝕜] D) : F × X →ₗ[𝕜] E × D) ∘ₗ
        (T.prodMap (L : D →L[𝕜] X) : E × D →ₗ[𝕜] F × X)) =
        ((G : F →ₗ[𝕜] E) ∘ₗ (T : E →ₗ[𝕜] F)).prodMap (LinearMap.id : D →ₗ[𝕜] D) := by
      apply LinearMap.ext
      rintro ⟨e, d⟩
      simp
    unfold LinearMap.IsLeftQuasiInverse
    rw [hc, ← LinearMap.prodMap_id]
    exact prodMap_equiv_left hG.1 _
  · have hc : ((T.prodMap (L : D →L[𝕜] X) : E × D →ₗ[𝕜] F × X) ∘ₗ
        (G.prodMap (L.symm : X →L[𝕜] D) : F × X →ₗ[𝕜] E × D)) =
        ((T : E →ₗ[𝕜] F) ∘ₗ (G : F →ₗ[𝕜] E)).prodMap (LinearMap.id : X →ₗ[𝕜] X) := by
      apply LinearMap.ext
      rintro ⟨f, x⟩
      simp
    unfold LinearMap.IsRightQuasiInverse
    rw [hc, ← LinearMap.prodMap_id]
    exact prodMap_equiv_left hG.2 _

/-- Conversely, if `F.prodMap L` is Fredholm (for any bounded `L`), then `F` is
Fredholm: `fst ∘ H ∘ inl` is a quasi-inverse of `F` for any quasi-inverse `H`. -/
theorem isFredholm_of_isFredholm_prodMap (T : E →L[𝕜] F) (L : D →L[𝕜] X)
    (h : (T.prodMap L).IsFredholm) : T.IsFredholm := by
  obtain ⟨H, hH⟩ := h.exists_isQuasiInverse
  let G : F →L[𝕜] E :=
    (ContinuousLinearMap.fst 𝕜 E D).comp (H.comp (ContinuousLinearMap.inl 𝕜 F X))
  refine IsFredholm.of_isQuasiInverse (v := G) ⟨?_, ?_⟩
  · have h1 : (G : F →ₗ[𝕜] E) ∘ₗ (T : E →ₗ[𝕜] F) =
        LinearMap.fst 𝕜 E D ∘ₗ (((H : F × X →ₗ[𝕜] E × D) ∘ₗ
          (T.prodMap L : E × D →ₗ[𝕜] F × X)) ∘ₗ LinearMap.inl 𝕜 E D) := by
      apply LinearMap.ext
      intro e
      simp [G]
    have h2 : LinearMap.fst 𝕜 E D ∘ₗ ((LinearMap.id : E × D →ₗ[𝕜] E × D) ∘ₗ
        LinearMap.inl 𝕜 E D) = LinearMap.id := by
      apply LinearMap.ext
      intro e
      simp
    have key := LinearMap.FiniteRangeSetoid.equiv_comp_left (u' := LinearMap.fst 𝕜 E D)
      (LinearMap.FiniteRangeSetoid.equiv_comp_right (u := LinearMap.inl 𝕜 E D) hH.1)
    rw [h2] at key
    unfold LinearMap.IsLeftQuasiInverse
    rw [h1]
    exact key
  · have h1 : (T : E →ₗ[𝕜] F) ∘ₗ (G : F →ₗ[𝕜] E) =
        LinearMap.fst 𝕜 F X ∘ₗ (((T.prodMap L : E × D →ₗ[𝕜] F × X) ∘ₗ
          (H : F × X →ₗ[𝕜] E × D)) ∘ₗ LinearMap.inl 𝕜 F X) := by
      apply LinearMap.ext
      intro f
      simp [G]
    have h2 : LinearMap.fst 𝕜 F X ∘ₗ ((LinearMap.id : F × X →ₗ[𝕜] F × X) ∘ₗ
        LinearMap.inl 𝕜 F X) = LinearMap.id := by
      apply LinearMap.ext
      intro f
      simp
    have key := LinearMap.FiniteRangeSetoid.equiv_comp_left (u' := LinearMap.fst 𝕜 F X)
      (LinearMap.FiniteRangeSetoid.equiv_comp_right (u := LinearMap.inl 𝕜 F X) hH.2)
    rw [h2] at key
    unfold LinearMap.IsRightQuasiInverse
    rw [h1]
    exact key

/-- Fredholm property of the diagonal operator `diag(F, L)`, both directions. -/
theorem isFredholm_prodMap_iff (T : E →L[𝕜] F) (L : D ≃L[𝕜] X) :
    (T.prodMap (L : D →L[𝕜] X)).IsFredholm ↔ T.IsFredholm :=
  ⟨isFredholm_of_isFredholm_prodMap T _, isFredholm_prodMap_of_isFredholm T L⟩

/-- `ker diag(F, L) = ker F × 0`, as an actual linear equivalence with `ker F`. -/
def kerProdMapEquiv (T : E →L[𝕜] F) (L : D ≃L[𝕜] X) :
    LinearMap.ker (T.prodMap (L : D →L[𝕜] X) : E × D →ₗ[𝕜] F × X) ≃ₗ[𝕜]
      LinearMap.ker (T : E →ₗ[𝕜] F) where
  toFun z := ⟨z.1.1, by
    have h := z.2
    rw [LinearMap.mem_ker] at h ⊢
    exact congrArg Prod.fst h⟩
  invFun e := ⟨(e.1, 0), by
    have h := e.2
    rw [LinearMap.mem_ker] at h ⊢
    simp [h]⟩
  left_inv z := by
    have h := z.2
    rw [LinearMap.mem_ker] at h
    have h2 : L z.1.2 = 0 := congrArg Prod.snd h
    have h3 : z.1.2 = 0 := by simpa using h2
    apply Subtype.ext
    exact Prod.ext rfl h3.symm
  right_inv e := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Projection of the codomain `F × X` onto the cokernel of `F`. -/
def cokerProj (T : E →L[𝕜] F) : (F × X) →ₗ[𝕜] F ⧸ LinearMap.range (T : E →ₗ[𝕜] F) :=
  (LinearMap.range (T : E →ₗ[𝕜] F)).mkQ ∘ₗ LinearMap.fst 𝕜 F X

omit [CompleteSpace 𝕜] in
theorem cokerProj_surjective (T : E →L[𝕜] F) :
    Function.Surjective (cokerProj (X := X) T) := by
  intro q
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ q
  exact ⟨(f, 0), rfl⟩

omit [CompleteSpace 𝕜] in
/-- `range diag(F, L) = range F × X`, i.e. the kernel of `cokerProj`. -/
theorem ker_cokerProj (T : E →L[𝕜] F) (L : D ≃L[𝕜] X) :
    LinearMap.ker (cokerProj (X := X) T) =
      LinearMap.range (T.prodMap (L : D →L[𝕜] X) : E × D →ₗ[𝕜] F × X) := by
  ext ⟨f, x⟩
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  change (LinearMap.range (T : E →ₗ[𝕜] F)).mkQ f = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨(e, L.symm x), ?_⟩
    simpa using he
  · rintro ⟨⟨e, d⟩, h⟩
    exact ⟨e, congrArg Prod.fst h⟩

/-- `coker diag(F, L) ≅ coker F`, as an actual linear equivalence of quotients. -/
def cokerProdMapEquiv (T : E →L[𝕜] F) (L : D ≃L[𝕜] X) :
    ((F × X) ⧸ LinearMap.range (T.prodMap (L : D →L[𝕜] X) : E × D →ₗ[𝕜] F × X)) ≃ₗ[𝕜]
      (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) :=
  (Submodule.quotEquivOfEq _ _ (ker_cokerProj T L).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (cokerProj_surjective T))

omit [CompleteSpace 𝕜] in
/-- `ind diag(F, L) = ind F` for every bounded `F` and `L : D ≃L X`. -/
theorem index_prodMap (T : E →L[𝕜] F) (L : D ≃L[𝕜] X) :
    (T.prodMap (L : D →L[𝕜] X)).index = T.index := by
  rw [LinearMap.index_eq_finrank_sub, LinearMap.index_eq_finrank_sub,
    (kerProdMapEquiv T L).finrank_eq, (cokerProdMapEquiv T L).finrank_eq]

omit [CompleteSpace 𝕜] in
/-- A continuous linear equivalence has index zero. -/
theorem index_equiv (e : E ≃L[𝕜] F) : (e : E →L[𝕜] F).index = 0 :=
  LinearMap.index_of_bijective e.bijective

end Diagonal

section Block

open Manuscript16.V165GraphSchur

variable {P D X : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

omit [CompleteSpace P] in
/-- The diagonal factor of `eq:mixed-factor-164` is `F.prodMap L`. -/
theorem diagonal_eq_prodMap (T : P →L[ℂ] P) (L : D ≃L[ℂ] X) :
    diagonal T L = T.prodMap (L : D →L[ℂ] X) := by
  apply ContinuousLinearMap.ext
  rintro ⟨p, x⟩
  rfl

/-- The Schur correction `K = B L⁻¹ C : P →L P`. -/
def schurCorrection (B : D →L[ℂ] P) (C : P →L[ℂ] X) (L : D ≃L[ℂ] X) : P →L[ℂ] P :=
  B.comp (L.symm.toContinuousLinearMap.comp C)

omit [CompleteSpace P] in
theorem schur_eq_sub (A : P →L[ℂ] P) (B : D →L[ℂ] P) (C : P →L[ℂ] X) (L : D ≃L[ℂ] X) :
    schur A B C L = A - schurCorrection B C L :=
  rfl

omit [CompleteSpace P] in
/-- `𝒜` is Fredholm iff the Schur map `F = A_P - B L⁻¹ C` is Fredholm. -/
theorem block_isFredholm_iff_schur (A : P →L[ℂ] P) (B : D →L[ℂ] P)
    (C : P →L[ℂ] X) (L : D ≃L[ℂ] X) :
    (block A B C L).IsFredholm ↔ (schur A B C L).IsFredholm := by
  rw [← typed_factorization A B C L]
  rw [isFredholm_equiv_comp, isFredholm_comp_equiv, diagonal_eq_prodMap]
  exact isFredholm_prodMap_iff _ L

omit [CompleteSpace P] in
/-- `ind 𝒜 = ind F` whenever the Schur map `F` is Fredholm. -/
theorem block_index_eq_schur (A : P →L[ℂ] P) (B : D →L[ℂ] P)
    (C : P →L[ℂ] X) (L : D ≃L[ℂ] X) (hF : (schur A B C L).IsFredholm) :
    (block A B C L).index = (schur A B C L).index := by
  have hD : (diagonal (schur A B C L) L).IsFredholm := by
    rw [diagonal_eq_prodMap]
    exact isFredholm_prodMap_of_isFredholm _ L hF
  have hR := (rightShear (L.symm.toContinuousLinearMap.comp C)).isFredholm
  have hLft := (leftShear (B.comp L.symm.toContinuousLinearMap)).isFredholm
  rw [← typed_factorization A B C L, IsFredholm.index_comp hLft (hD.comp hR),
    IsFredholm.index_comp hD hR, index_equiv, index_equiv, diagonal_eq_prodMap,
    index_prodMap]
  simp

/-- `thm:dirac-maxwell-obstruction-164` (i)–(ii), typed abstract form: if the Schur
correction `B L⁻¹ C` is compact, then `𝒜` is Fredholm iff `A_P` is Fredholm, and in
that case `ind 𝒜 = ind A_P`. -/
theorem block_isFredholm_iff_and_index_eq (A : P →L[ℂ] P) (B : D →L[ℂ] P)
    (C : P →L[ℂ] X) (L : D ≃L[ℂ] X)
    (hK : IsCompactOperator (schurCorrection B C L)) :
    ((block A B C L).IsFredholm ↔ A.IsFredholm) ∧
      (A.IsFredholm → (block A B C L).index = A.index) := by
  have hiff : (schur A B C L).IsFredholm ↔ A.IsFredholm := by
    rw [schur_eq_sub, sub_eq_add_neg]
    exact SharedCore.FredholmAtkinson.isFredholm_add_compact_iff A
      (-schurCorrection B C L) hK.neg
  refine ⟨(block_isFredholm_iff_schur A B C L).trans hiff, fun hA => ?_⟩
  rw [block_index_eq_schur A B C L (hiff.mpr hA), schur_eq_sub, sub_eq_add_neg]
  exact SharedCore.FredholmAtkinson.index_add_compact A _ hA hK.neg

end Block

end Manuscript16.DiracMaxwellObstructionIndex20261124

#print axioms Manuscript16.DiracMaxwellObstructionIndex20261124.prodMap_equiv_left
#print axioms Manuscript16.DiracMaxwellObstructionIndex20261124.isFredholm_prodMap_of_isFredholm
#print axioms Manuscript16.DiracMaxwellObstructionIndex20261124.isFredholm_of_isFredholm_prodMap
#print axioms Manuscript16.DiracMaxwellObstructionIndex20261124.isFredholm_prodMap_iff
#print axioms Manuscript16.DiracMaxwellObstructionIndex20261124.kerProdMapEquiv
#print axioms Manuscript16.DiracMaxwellObstructionIndex20261124.cokerProj_surjective
#print axioms Manuscript16.DiracMaxwellObstructionIndex20261124.ker_cokerProj
#print axioms Manuscript16.DiracMaxwellObstructionIndex20261124.cokerProdMapEquiv
#print axioms Manuscript16.DiracMaxwellObstructionIndex20261124.index_prodMap
#print axioms Manuscript16.DiracMaxwellObstructionIndex20261124.index_equiv
#print axioms Manuscript16.DiracMaxwellObstructionIndex20261124.diagonal_eq_prodMap
#print axioms Manuscript16.DiracMaxwellObstructionIndex20261124.schur_eq_sub
#print axioms Manuscript16.DiracMaxwellObstructionIndex20261124.block_isFredholm_iff_schur
#print axioms Manuscript16.DiracMaxwellObstructionIndex20261124.block_index_eq_schur
#print axioms Manuscript16.DiracMaxwellObstructionIndex20261124.block_isFredholm_iff_and_index_eq
