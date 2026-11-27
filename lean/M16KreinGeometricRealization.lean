import M16KreinSpectralGraphClosure

noncomputable section
open scoped BigOperators
open M16KreinDomains M16KreinGraphGap M16KreinSpectralGraphClosure
open Manuscript16.V166L2SpectralInverse
open Manuscript16.DiracMaxwellCoefficientModel20261124

namespace M16KreinGeometricRealization

/-! Geometric input is a complete orthonormal family of smooth eigenvectors
of a closed symmetric differential realization. The following constructs
the Hilbert basis and derives the resolvent, rather than assuming the
coefficient graph or its resolvent. -/

theorem basis_from_complete_eigenfamily {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (v : ι → E) (hv : Orthonormal ℂ v)
    (hd : ⊤ ≤ (Submodule.span ℂ (Set.range v)).topologicalClosure) :
    ∃ b : HilbertBasis ι ℂ E, ∀ j, b j = v j := by
  refine ⟨HilbertBasis.mk hv hd, ?_⟩
  intro j
  rw [HilbertBasis.coe_mk]

theorem eigenfamily_zero_resolvent {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (v : ι → E) (hv : Orthonormal ℂ v)
    (hd : ⊤ ≤ (Submodule.span ℂ (Set.range v)).topologicalClosure)
    (lam : ι → ℝ) (G : Submodule ℂ (E × E))
    (hcl : IsClosed (G : Set (E × E)))
    (heig : ∀ j, (v j,(lam j : ℂ) • v j) ∈ G)
    (hs : ∀ p q : E × E, p ∈ G → q ∈ G →
      inner ℂ p.1 q.2 = inner ℂ p.2 q.1)
    (g : ℝ) (hg : 0 < g) (hl : ∀ j, g ≤ |lam j|) :
    ∃ R : E →L[ℂ] E, GraphResolvent (G : Set (E × E)) 0 R ∧
      ‖R‖ ≤ 1/g := by
  obtain ⟨b,hb⟩ := basis_from_complete_eigenfamily v hv hd
  have he : ∀ j, (b j,(lam j : ℂ) • b j) ∈ G := by
    intro j
    rw [hb j]
    exact heig j
  obtain ⟨R,hR,hn⟩ := reference_zero_graph lam g hg hl
  let R' : E →L[ℂ] E :=
    b.repr.symm.toLinearIsometry.toContinuousLinearMap.comp
      (R.comp b.repr.toLinearIsometry.toContinuousLinearMap)
  refine ⟨R', ?_, ?_⟩
  · intro x f
    simp only [zero_smul,add_zero,SetLike.mem_coe]
    have h := hR (b.repr x) (b.repr f)
    simp only [zero_smul,add_zero] at h
    have heq : (x,f) ∈ G ↔ (b.repr x,b.repr f) ∈
        ((multOp (fun j => (lam j : ℂ))).graph : Set (L2 ι × L2 ι)) := by
      rw [closed_symmetric_eigenbasis_graph b lam G hcl he hs x f,
        SetLike.mem_coe,mem_graph_multOp_iff]
    rw [heq,h]
    change b.repr x = R (b.repr f) ↔ x = b.repr.symm (R (b.repr f))
    constructor
    · intro hx
      rw [← hx,b.repr.symm_apply_apply]
    · intro hx
      rw [hx,b.repr.apply_symm_apply]
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    change ‖b.repr.symm (R (b.repr x))‖ ≤ (1/g)*‖x‖
    rw [b.repr.symm.norm_map]
    calc
      _ ≤ ‖R‖*‖b.repr x‖ := R.le_opNorm _
      _ ≤ _ := by
        rw [b.repr.norm_map]
        exact mul_le_mul_of_nonneg_right hn (norm_nonneg _)

-- Both perturbed diagonal resolvents and the block inverse are obtained
-- on the original graph spaces; no coefficient-space inverse is assumed.
theorem eigenfamily_block_disk {ι κ E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Nontrivial F]
    (v : ι → E) (w : κ → F)
    (hv : Orthonormal ℂ v) (hw : Orthonormal ℂ w)
    (hdv : ⊤ ≤ (Submodule.span ℂ (Set.range v)).topologicalClosure)
    (hdw : ⊤ ≤ (Submodule.span ℂ (Set.range w)).topologicalClosure)
    (la : ι → ℝ) (ld : κ → ℝ)
    (GA : Submodule ℂ (E × E)) (GD : Submodule ℂ (F × F))
    (hA : IsClosed (GA : Set (E × E))) (hD : IsClosed (GD : Set (F × F)))
    (heA : ∀ j, (v j,(la j : ℂ) • v j) ∈ GA)
    (heD : ∀ j, (w j,(ld j : ℂ) • w j) ∈ GD)
    (hsA : ∀ p q : E × E, p ∈ GA → q ∈ GA →
      inner ℂ p.1 q.2 = inner ℂ p.2 q.1)
    (hsD : ∀ p q : F × F, p ∈ GD → q ∈ GD →
      inner ℂ p.1 q.2 = inner ℂ p.2 q.1)
    (hla : ∀ j, 4 ≤ |la j|) (hld : ∀ j, (3:ℝ)/2 ≤ |ld j|)
    (VA : E →L[ℂ] E) (VD : F →L[ℂ] F)
    (X : F →L[ℂ] E) (Y : E →L[ℂ] F)
    (hX : ‖X‖ ≤ 2*‖Y‖) (z : ℂ)
    (hz : ‖z‖ < M16Krein.gapRadius (4-‖VA‖) (3/2-‖VD‖) ‖Y‖) :
    ∃ R : E × F →L[ℂ] E × F,
      GraphResolvent
        (perturb (diagonalGraph (perturb (GA : Set _) VA) (perturb (GD : Set _) VD))
          (fun u : E × F => (X u.2,Y u.1))) z R := by
  obtain ⟨RA,hRA,hnA⟩ := eigenfamily_zero_resolvent v hv hdv la GA hA heA hsA 4
    (by norm_num) hla
  obtain ⟨RD,hRD,hnD⟩ := eigenfamily_zero_resolvent w hw hdw ld GD hD heD hsD
    (3/2) (by norm_num) hld
  have ha := lt_of_lt_of_le hz (M16Krein.gap_radius_le_a (4-‖VA‖) (3/2-‖VD‖) ‖Y‖)
  have hd := lt_of_lt_of_le hz (M16Krein.gap_radius_le_d (4-‖VA‖) (3/2-‖VD‖) ‖Y‖)
  obtain ⟨ra,hra,hna⟩ := perturbed_diagonal_resolvent (GA : Set _) RA VA z 4
    (by norm_num) hnA (by linarith) hRA
  obtain ⟨rd,hrd,hnd⟩ := perturbed_diagonal_resolvent (GD : Set _) RD VD z (3/2)
    (by norm_num) hnD (by linarith) hRD
  exact disk_graph_resolvent _ _ z ra rd X Y (4-‖VA‖) (3/2-‖VD‖)
    hz hna hnd hX hra hrd

-- Real/imaginary component graph of a possibly unbounded operator.
def pairGraph {E : Type*} (G : Set (E × E)) :
    Set ((E × E) × (E × E)) :=
  {q | (q.1.1,q.2.1) ∈ G ∧ (q.1.2,q.2.2) ∈ G}

theorem pairGraph_closed {E : Type*} [TopologicalSpace E]
    (G : Set (E × E)) (hG : IsClosed G) : IsClosed (pairGraph G) := by
  change IsClosed
    ((fun q : (E × E) × (E × E) => (q.1.1,q.2.1)) ⁻¹' G ∩
     (fun q : (E × E) × (E × E) => (q.1.2,q.2.2)) ⁻¹' G)
  exact (hG.preimage (continuous_fst.fst.prodMk continuous_snd.fst)).inter
    (hG.preimage (continuous_fst.snd.prodMk continuous_snd.snd))

theorem pairGraph_domain {E : Type*} (G : Set (E × E)) :
    domain (pairGraph G) = {x : E × E | x.1 ∈ domain G ∧ x.2 ∈ domain G} := by
  ext x
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨⟨y.1,hy.1⟩,⟨y.2,hy.2⟩⟩
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    exact ⟨(a,b),ha,hb⟩

theorem pairGraph_adjoint {E : Type*} [Zero E]
    (G : Set (E × E)) (p : E → E → ℝ)
    (h0 : (0,0) ∈ G) (hp : ∀ x, p 0 x = 0) :
    adjGraph (complexPair p) (pairGraph G) = pairGraph (adjGraph p G) := by
  ext q
  constructor
  · intro h
    change (∀ x y : E × E, (x.1,y.1) ∈ G ∧ (x.2,y.2) ∈ G →
      complexPair p y q.1 = complexPair p x q.2) at h
    change (∀ x y, (x,y) ∈ G → p y q.1.1 = p x q.2.1) ∧
      (∀ x y, (x,y) ∈ G → p y q.1.2 = p x q.2.2)
    constructor
    · intro x y hxy
      have hh := congrArg Complex.re (h (x,0) (y,0) ⟨hxy,h0⟩)
      simpa [complexPair,hp] using hh
    · intro x y hxy
      have hh := congrArg Complex.im (h (x,0) (y,0) ⟨hxy,h0⟩)
      simpa [complexPair,hp] using hh
  · intro h
    change (∀ x y, (x,y) ∈ G → p y q.1.1 = p x q.2.1) ∧
      (∀ x y, (x,y) ∈ G → p y q.1.2 = p x q.2.2) at h
    intro x y hxy
    change (x.1,y.1) ∈ G ∧ (x.2,y.2) ∈ G at hxy
    simp only [complexPair,h.1 _ _ hxy.1,h.1 _ _ hxy.2,
      h.2 _ _ hxy.1,h.2 _ _ hxy.2]

theorem pairGraph_selfAdjoint {E : Type*} [Zero E]
    (G : Set (E × E)) (p : E → E → ℝ)
    (h0 : (0,0) ∈ G) (hp : ∀ x, p 0 x = 0)
    (hsa : adjGraph p G = G) :
    adjGraph (complexPair p) (pairGraph G) = pairGraph G := by
  rw [pairGraph_adjoint G p h0 hp,hsa]

-- Invariance of the finite eigenspace evaluation sum under an orthogonal
-- basis change (real Hodge eigenforms). Apply coordinatewise in a fibre.
theorem orthogonal_sum_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι → ι → ℝ) (v : ι → ℝ)
    (hU : ∀ j k, ∑ i, U i j * U i k = if j = k then 1 else 0) :
    (∑ i, (∑ j, U i j * v j)^2) = ∑ j, (v j)^2 := by
  calc
    _ = ∑ i, ∑ j, ∑ k, (U i j * U i k)*(v j*v k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_two,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ j, ∑ k, (∑ i, U i j * U i k)*(v j*v k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [hU,pow_two]

theorem fibre_evaluation_invariant {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (U : ι → ι → ℝ) (v : ι → κ → ℝ)
    (hU : ∀ j k, ∑ i, U i j * U i k = if j = k then 1 else 0) :
    (∑ a : κ, ∑ i : ι, (∑ j, U i j * v j a)^2) =
      ∑ a : κ, ∑ j : ι, (v j a)^2 := by
  apply Finset.sum_congr rfl
  intro a ha
  exact orthogonal_sum_sq U (fun j => v j a) hU

-- Transitivity and orthogonal action on a finite eigenspace imply the
-- diagonal evaluation density is independent of the point.
theorem eigenspace_diagonal_constant {Ω ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (v : Ω → ι → κ → ℝ)
    (h : ∀ x y, ∃ U : ι → ι → ℝ,
      (∀ j k, ∑ i, U i j * U i k = if j = k then 1 else 0) ∧
      (∀ i a, v y i a = ∑ j, U i j * v x j a)) :
    ∀ x y, (∑ a : κ, ∑ j : ι, (v y j a)^2) =
      ∑ a : κ, ∑ j : ι, (v x j a)^2 := by
  intro x y
  obtain ⟨U,hU,hv⟩ := h x y
  simp_rw [hv]
  exact fibre_evaluation_invariant U (v x) hU

theorem pairGraph_singleValued {E : Type*} (G : Set (E × E))
    (hG : ∀ x y z, (x,y) ∈ G → (x,z) ∈ G → y = z) :
    ∀ x y z : E × E, (x,y) ∈ pairGraph G → (x,z) ∈ pairGraph G → y = z := by
  intro x y z hy hz
  exact Prod.ext (hG _ _ _ hy.1 hz.1) (hG _ _ _ hy.2 hz.2)

#print axioms eigenspace_diagonal_constant
#print axioms pairGraph_singleValued
#print axioms basis_from_complete_eigenfamily
#print axioms eigenfamily_zero_resolvent
#print axioms eigenfamily_block_disk
#print axioms pairGraph_closed
#print axioms pairGraph_domain
#print axioms pairGraph_adjoint
#print axioms pairGraph_selfAdjoint
#print axioms orthogonal_sum_sq
#print axioms fibre_evaluation_invariant
end M16KreinGeometricRealization
