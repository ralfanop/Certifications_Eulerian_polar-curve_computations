import M16KreinGraphGap

noncomputable section
open scoped BigOperators
open Filter Topology
open Manuscript16.V166L2SpectralInverse
open Manuscript16.DiracMaxwellCoefficientModel20261124
open M16KreinDomains

namespace M16KreinSpectralGraphClosure

/-! The geometric eigenbasis and symmetry/closedness are input hypotheses,
not an assumed diagonal graph identification. The reverse implication is
proved by finite spectral truncation and closedness. -/

theorem closed_symmetric_eigenbasis_graph
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (b : HilbertBasis ι ℂ E) (lam : ι → ℝ)
    (G : Submodule ℂ (E × E)) (hclosed : IsClosed (G : Set (E × E)))
    (heig : ∀ j, (b j, (lam j : ℂ) • b j) ∈ G)
    (hsymm : ∀ p q : E × E, p ∈ G → q ∈ G →
      inner ℂ p.1 q.2 = inner ℂ p.2 q.1)
    (x y : E) :
    (x,y) ∈ G ↔ ∀ j, b.repr y j = (lam j : ℂ) * b.repr x j := by
  constructor
  · intro hxy j
    rw [b.repr_apply_apply, b.repr_apply_apply]
    have h := hsymm (b j, (lam j : ℂ) • b j) (x,y) (heig j) hxy
    change inner ℂ (b j) y = inner ℂ ((lam j : ℂ) • b j) x at h
    simpa [inner_smul_left] using h
  · intro hxy
    classical
    have ht : ∀ s : Finset ι,
        ((∑ j ∈ s, b.repr x j • b j),
         (∑ j ∈ s, b.repr y j • b j)) ∈ G := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using G.zero_mem
      | @insert j s hj ih =>
        simp only [Finset.sum_insert hj]
        have h := G.smul_mem (b.repr x j) (heig j)
        change (b.repr x j • b j,
          b.repr x j • ((lam j : ℂ) • b j)) ∈ G at h
        rw [smul_smul, mul_comm (b.repr x j), ← hxy j] at h
        exact G.add_mem h ih
    have hx := b.hasSum_repr x
    have hy := b.hasSum_repr y
    change Tendsto (fun s : Finset ι => ∑ j ∈ s, b.repr x j • b j)
      atTop (𝓝 x) at hx
    change Tendsto (fun s : Finset ι => ∑ j ∈ s, b.repr y j • b j)
      atTop (𝓝 y) at hy
    exact hclosed.mem_of_tendsto (hx.prodMk_nhds hy) (Filter.Eventually.of_forall ht)

theorem closed_symmetric_graph_transport
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (b : HilbertBasis ι ℂ E) (lam : ι → ℝ)
    (G : Submodule ℂ (E × E)) (hclosed : IsClosed (G : Set (E × E)))
    (heig : ∀ j, (b j, (lam j : ℂ) • b j) ∈ G)
    (hsymm : ∀ p q : E × E, p ∈ G → q ∈ G →
      inner ℂ p.1 q.2 = inner ℂ p.2 q.1) :
    transport b.repr.toEquiv (G : Set (E × E)) =
      ((multOp (fun j => (lam j : ℂ))).graph : Set (L2 ι × L2 ι)) := by
  apply M16KreinGraphGap.eigenbasis_graph_transport
  exact closed_symmetric_eigenbasis_graph b lam G hclosed heig hsymm

#print axioms closed_symmetric_eigenbasis_graph
#print axioms closed_symmetric_graph_transport
end M16KreinSpectralGraphClosure
